/*
 * libevent issue #232: SSL bufferevent write-readiness loss
 *
 * Bug: after partial SSL_write, the SSL bufferevent loses track of
 * write-readiness notifications from the underlying socket.  The socket
 * becomes writable but the bufferevent is never informed, so remaining
 * data sits unsent forever.
 *
 * Affected: release-2.1.5-beta (before PR #190)
 * Fixed:    merged via PR #190 (before 2.1.6)
 */

#include <event2/event.h>
#include <event2/bufferevent.h>
#include <event2/bufferevent_ssl.h>
#include <event2/buffer.h>
#include <event2/listener.h>

#include <openssl/ssl.h>
#include <openssl/err.h>
#include <openssl/x509.h>
#include <openssl/evp.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <sys/socket.h>
#include <netinet/in.h>

#define DATA_SIZE (10 * 1024 * 1024)

struct ctx {
  struct event_base *base;
  SSL_CTX *server_ssl_ctx;
  size_t bytes_received;
  struct timeval start;
  const char *cert_path;
  const char *key_path;
};

/* ── server callbacks ───────────────────────────────────────── */

static void
server_read_cb(struct bufferevent *bev, void *arg)
{
  struct ctx *c = (struct ctx *)arg;
  struct evbuffer *in = bufferevent_get_input(bev);
  size_t n = evbuffer_get_length(in);
  evbuffer_drain(in, n);
  c->bytes_received += n;

  if (c->bytes_received >= DATA_SIZE) {
    struct timeval now;
    gettimeofday(&now, NULL);
    long ms = (now.tv_sec - c->start.tv_sec) * 1000 +
              (now.tv_usec - c->start.tv_usec) / 1000;
    printf("{\"test\":\"issue_232\",\"outcome\":\"PASS\",\"elapsed_ms\":%ld}\n", ms);
    event_base_loopbreak(c->base);
  }
}

static void
server_event_cb(struct bufferevent *bev, short what, void *arg)
{
  (void)arg;
  if (what & (BEV_EVENT_ERROR | BEV_EVENT_EOF)) {
    unsigned long err;
    while ((err = bufferevent_get_openssl_error(bev)))
      fprintf(stderr, "SSL error: %s\n", ERR_error_string(err, NULL));
    bufferevent_free(bev);
  }
}

static void
accept_cb(struct evconnlistener *listener, evutil_socket_t fd,
          struct sockaddr *addr, int socklen, void *arg)
{
  (void)listener; (void)addr; (void)socklen;
  struct ctx *c = (struct ctx *)arg;

  SSL *ssl = SSL_new(c->server_ssl_ctx);
  struct bufferevent *bev = bufferevent_openssl_socket_new(
      c->base, fd, ssl, BUFFEREVENT_SSL_ACCEPTING,
      BEV_OPT_CLOSE_ON_FREE);

  bufferevent_setcb(bev, server_read_cb, NULL, server_event_cb, c);
  bufferevent_enable(bev, EV_READ);
}

/* ── client callback ────────────────────────────────────────── */

static void
client_event_cb(struct bufferevent *bev, short what, void *arg)
{
  (void)arg;
  if (what & BEV_EVENT_CONNECTED) {
    char *data = malloc(DATA_SIZE);
    if (!data) { perror("malloc"); return; }
    memset(data, 'A', DATA_SIZE);
    bufferevent_write(bev, data, DATA_SIZE);
    free(data);
  } else if (what & (BEV_EVENT_ERROR | BEV_EVENT_EOF)) {
    unsigned long err;
    while ((err = bufferevent_get_openssl_error(bev)))
      fprintf(stderr, "Client SSL error: %s\n", ERR_error_string(err, NULL));
    bufferevent_free(bev);
  }
}

/* ── SSL setup ──────────────────────────────────────────────── */

static SSL_CTX *
make_server_ctx(const char *cert, const char *key)
{
#if OPENSSL_VERSION_NUMBER >= 0x10100000L
  SSL_CTX *ctx = SSL_CTX_new(TLS_server_method());
#else
  SSL_CTX *ctx = SSL_CTX_new(SSLv23_server_method());
#endif
  if (!ctx) return NULL;
  if (SSL_CTX_use_certificate_file(ctx, cert, SSL_FILETYPE_PEM) != 1) {
    SSL_CTX_free(ctx); return NULL;
  }
  if (SSL_CTX_use_PrivateKey_file(ctx, key, SSL_FILETYPE_PEM) != 1) {
    SSL_CTX_free(ctx); return NULL;
  }
  return ctx;
}

static SSL_CTX *
make_client_ctx(void)
{
#if OPENSSL_VERSION_NUMBER >= 0x10100000L
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
#else
  SSL_CTX *ctx = SSL_CTX_new(SSLv23_client_method());
#endif
  if (!ctx) return NULL;
  SSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, NULL);
  return ctx;
}

/* ── main ───────────────────────────────────────────────────── */

int main(int argc, char **argv)
{
  const char *cert_path = "test.crt";
  const char *key_path  = "test.key";

  if (argc >= 3) {
    cert_path = argv[1];
    key_path  = argv[2];
  }

#if OPENSSL_VERSION_NUMBER < 0x10100000L
  SSL_library_init();
  SSL_load_error_strings();
#endif

  SSL_CTX *server_ctx = make_server_ctx(cert_path, key_path);
  SSL_CTX *client_ctx = make_client_ctx();
  if (!server_ctx || !client_ctx) {
    fprintf(stderr, "SSL context creation failed\n");
    printf("{\"test\":\"issue_232\",\"outcome\":\"ERROR\",\"elapsed_ms\":0}\n");
    return 1;
  }

  struct event_base *base = event_base_new();
  struct ctx c = {
    .base = base,
    .server_ssl_ctx = server_ctx,
    .bytes_received = 0,
    .cert_path = cert_path,
    .key_path = key_path
  };
  gettimeofday(&c.start, NULL);

  /* server listener */
  struct sockaddr_in sin;
  memset(&sin, 0, sizeof(sin));
  sin.sin_family = AF_INET;
  sin.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  sin.sin_port = 0;

  struct evconnlistener *listener = evconnlistener_new_bind(
      base, accept_cb, &c,
      LEV_OPT_CLOSE_ON_FREE | LEV_OPT_REUSEABLE, -1,
      (struct sockaddr *)&sin, sizeof(sin));
  if (!listener) {
    fprintf(stderr, "listener failed\n");
    printf("{\"test\":\"issue_232\",\"outcome\":\"ERROR\",\"elapsed_ms\":0}\n");
    return 1;
  }

  evutil_socket_t lfd = evconnlistener_get_fd(listener);
  ev_socklen_t sinlen = sizeof(sin);
  getsockname(lfd, (struct sockaddr *)&sin, &sinlen);
  int port = ntohs(sin.sin_port);

  /* client */
  SSL *client_ssl = SSL_new(client_ctx);
  struct bufferevent *client_bev = bufferevent_openssl_socket_new(
      base, -1, client_ssl, BUFFEREVENT_SSL_CONNECTING,
      BEV_OPT_CLOSE_ON_FREE);
  bufferevent_setcb(client_bev, NULL, NULL, client_event_cb, &c);
  bufferevent_enable(client_bev, EV_READ | EV_WRITE);

  struct sockaddr_in dst;
  memset(&dst, 0, sizeof(dst));
  dst.sin_family = AF_INET;
  dst.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  dst.sin_port = htons(port);
  bufferevent_socket_connect(client_bev,
      (struct sockaddr *)&dst, sizeof(dst));

  event_base_dispatch(base);

  evconnlistener_free(listener);
  SSL_CTX_free(server_ctx);
  SSL_CTX_free(client_ctx);
  event_base_free(base);
  return 0;
}
