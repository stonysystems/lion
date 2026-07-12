/*
 * libevent issue #237: bufferevent filter hang
 *
 * Bug: evhttp_set_bevcb returns a bufferevent filter, but be_filter_ctrl
 * omits the fd event setup that be_socket_ctrl performs.  Without fd events
 * registered in epoll, the server never reads the HTTP request.
 *
 * Affected: release-2.1.5-beta
 * Fixed:    master (before 2.1.6)
 */

#include <event2/event.h>
#include <event2/http.h>
#include <event2/bufferevent.h>
#include <event2/buffer.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <netinet/in.h>

static struct timeval g_start;

static enum bufferevent_filter_result
passthrough(struct evbuffer *src, struct evbuffer *dst,
            ev_ssize_t limit, enum bufferevent_flush_mode mode, void *ctx)
{
  (void)limit; (void)mode; (void)ctx;
  evbuffer_remove_buffer(src, dst, evbuffer_get_length(src));
  return BEV_OK;
}

static struct bufferevent *
filter_bevcb(struct event_base *base, void *arg)
{
  (void)arg;
  struct bufferevent *bev =
      bufferevent_socket_new(base, -1, BEV_OPT_CLOSE_ON_FREE);
  struct bufferevent *filter = bufferevent_filter_new(
      bev, passthrough, passthrough, BEV_OPT_CLOSE_ON_FREE, NULL, NULL);
  return filter;
}

static void
request_done(struct evhttp_request *req, void *arg)
{
  struct event_base *base = (struct event_base *)arg;
  struct timeval now;
  gettimeofday(&now, NULL);
  long ms = (now.tv_sec - g_start.tv_sec) * 1000 +
            (now.tv_usec - g_start.tv_usec) / 1000;

  if (req && evhttp_request_get_response_code(req) == 200) {
    printf("{\"test\":\"issue_237\",\"outcome\":\"PASS\",\"elapsed_ms\":%ld}\n", ms);
  } else {
    printf("{\"test\":\"issue_237\",\"outcome\":\"ERROR\",\"elapsed_ms\":%ld}\n", ms);
  }
  event_base_loopbreak(base);
}

static void
generic_handler(struct evhttp_request *req, void *arg)
{
  (void)arg;
  struct evbuffer *buf = evbuffer_new();
  evbuffer_add_printf(buf, "OK");
  evhttp_send_reply(req, 200, "OK", buf);
  evbuffer_free(buf);
}

int main(void)
{
  gettimeofday(&g_start, NULL);

  struct event_base *base = event_base_new();
  struct evhttp *http = evhttp_new(base);

  evhttp_set_bevcb(http, filter_bevcb, NULL);
  evhttp_set_gencb(http, generic_handler, NULL);

  struct evhttp_bound_socket *bound =
      evhttp_bind_socket_with_handle(http, "127.0.0.1", 0);
  if (!bound) {
    fprintf(stderr, "bind failed\n");
    return 1;
  }

  evutil_socket_t fd = evhttp_bound_socket_get_fd(bound);
  struct sockaddr_in sin;
  ev_socklen_t sinlen = sizeof(sin);
  getsockname(fd, (struct sockaddr *)&sin, &sinlen);
  int port = ntohs(sin.sin_port);

  struct evhttp_connection *conn =
      evhttp_connection_base_new(base, NULL, "127.0.0.1", port);
  struct evhttp_request *req = evhttp_request_new(request_done, base);
  evhttp_make_request(conn, req, EVHTTP_REQ_GET, "/test");

  event_base_dispatch(base);

  evhttp_connection_free(conn);
  evhttp_free(http);
  event_base_free(base);
  return 0;
}
