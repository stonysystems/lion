/*
 * Combined libuv stress workload
 *
 * Ports the same test design as the Rust (Tokio/Lion) correctness-stress
 * "combined" run: one event loop concurrently driving the same core-subsystem
 * workloads under a heartbeat, with a timeout = hang oracle. The execution model
 * differs (libuv event loop + callbacks vs Rust async/await), so the code is
 * necessarily different while the test goals and structure are the same. This
 * corresponds to the Rust single-threaded (current-thread) configuration.
 *
 * W1: Timer Cancel Storm   — Timer Ops. A long timer and a short timer; the short
 *     fires first and cancels the long (Rust: the requests workload's timeout-
 *     guarded op). 500 timer pairs × 100 iterations = 50,000 register/cancel ops
 *
 * W2: Callback Chain Storm  — Task Lifecycle + Cooperative Scheduling. Nested
 *     callback chains that re-fire (Rust: fan-out + cooperative compute).
 *     100 parents × 10 children, each child re-fires once
 *
 * W3: TCP Echo Waves        — Network I/O (Rust: the echo workload).
 *     Server + 20 sequential client connections with data exchange
 *
 * W4: Handle Lifecycle      — libuv's own bug-triggering subsystem: close →
 *     bind/listen, exercising issue 3503 (missing UV_HANDLE_CLOSING check).
 *
 * W5: Heartbeat Monitor     — Heartbeat, the liveness canary (as in Rust).
 *     30 ticks × 100ms periodic timer
 *
 * Expected results:
 *   v1.43.0: HANG — W4 triggers issue 3503 (bind/listen on closing handle)
 *   v1.44.2: PASS — all workloads complete
  *
 * DISCLOSURE: W4 (and, for libevent, W3's filter layer) is the library's own
 * documented bug-trigger subsystem embedded in the mix; a combined HANG on a
 * bug-carrying version is attributable to it (see summary.md), not to the
 * neutral W1/W2/W5 mix.
 */

#include <uv.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>

/* ── app-wide completion tracking ─────────────────────────── */

struct app {
  uv_loop_t *loop;
  int remaining;
  struct timeval t0;
};

static void app_done(struct app *a)
{
  a->remaining--;
  if (a->remaining <= 0) {
    struct timeval now;
    gettimeofday(&now, NULL);
    long ms = (now.tv_sec - a->t0.tv_sec) * 1000 +
              (now.tv_usec - a->t0.tv_usec) / 1000;
    printf("{\"test\":\"combined\",\"outcome\":\"PASS\",\"elapsed_ms\":%ld}\n", ms);
    uv_stop(a->loop);
  }
}

static void free_handle(uv_handle_t *h) { free(h); }

/* ── W1: Timer Cancel Storm ──────────────────────────────── */

#define W1_PAIRS  500
#define W1_ITERS  100

struct w1_pair {
  struct app *a;
  uv_timer_t long_t;
  uv_timer_t short_t;
  int remaining;
};

static int w1_active;
static void w1_noop(uv_handle_t *h) { (void)h; }
static void w1_long_cb(uv_timer_t *h) { (void)h; }

static void w1_short_cb(uv_timer_t *handle)
{
  struct w1_pair *p = handle->data;
  uv_timer_stop(&p->long_t);
  p->remaining--;
  if (p->remaining > 0) {
    uv_timer_start(&p->long_t, w1_long_cb, 10000, 0);
    uv_timer_start(&p->short_t, w1_short_cb, 1, 0);
  } else {
    uv_close((uv_handle_t *)&p->long_t, w1_noop);
    uv_close((uv_handle_t *)&p->short_t, w1_noop);
    w1_active--;
    if (w1_active == 0)
      app_done(p->a);
  }
}

static void w1_setup(struct app *a)
{
  w1_active = W1_PAIRS;
  for (int i = 0; i < W1_PAIRS; i++) {
    struct w1_pair *p = calloc(1, sizeof(*p));
    p->a = a;
    p->remaining = W1_ITERS;
    uv_timer_init(a->loop, &p->long_t);
    uv_timer_init(a->loop, &p->short_t);
    p->long_t.data = p;
    p->short_t.data = p;
    uv_timer_start(&p->long_t, w1_long_cb, 10000, 0);
    uv_timer_start(&p->short_t, w1_short_cb, 1, 0);
  }
}

/* ── W2: Callback Chain Storm ────────────────────────────── */

#define W2_PARENTS   100
#define W2_CHILDREN  10

struct w2_child {
  uv_timer_t timer;
  int yields;
  int *parent_counter;
  struct app *a;
};

static int w2_parents_remaining;

static void w2_child_close(uv_handle_t *h) { free(h->data); }

static void w2_child_cb(uv_timer_t *handle)
{
  struct w2_child *c = handle->data;
  c->yields--;
  if (c->yields > 0) {
    uv_timer_start(handle, w2_child_cb, 0, 0);
  } else {
    (*c->parent_counter)--;
    if (*c->parent_counter == 0) {
      free(c->parent_counter);
      w2_parents_remaining--;
      if (w2_parents_remaining == 0)
        app_done(c->a);
    }
    uv_close((uv_handle_t *)handle, w2_child_close);
  }
}

static void w2_parent_close(uv_handle_t *h) { free(h->data); }

static void w2_parent_cb(uv_timer_t *handle)
{
  struct w2_parent { struct app *a; } *p = handle->data;
  int *counter = malloc(sizeof(int));
  *counter = W2_CHILDREN;
  for (int i = 0; i < W2_CHILDREN; i++) {
    struct w2_child *c = calloc(1, sizeof(*c));
    c->a = p->a;
    c->yields = 2;
    c->parent_counter = counter;
    uv_timer_init(p->a->loop, &c->timer);
    c->timer.data = c;
    uv_timer_start(&c->timer, w2_child_cb, 0, 0);
  }
  uv_close((uv_handle_t *)handle, w2_parent_close);
}

struct w2_parent_ctx { struct app *a; };

static void w2_setup(struct app *a)
{
  w2_parents_remaining = W2_PARENTS;
  for (int i = 0; i < W2_PARENTS; i++) {
    struct w2_parent_ctx *p = calloc(1, sizeof(*p));
    p->a = a;
    uv_timer_t *t = calloc(1, sizeof(*t));
    uv_timer_init(a->loop, t);
    t->data = p;
    uv_timer_start(t, w2_parent_cb, 0, 0);
  }
}

/* ── W3: TCP Echo Waves ──────────────────────────────────── */

#define W3_ROUNDS  20

struct w3_state {
  struct app *a;
  uv_tcp_t server;
  int port;
  int remaining;
};

static char w3_slab[256];
static void w3_alloc(uv_handle_t *h, size_t s, uv_buf_t *b) {
  (void)h; (void)s;
  b->base = w3_slab;
  b->len = sizeof(w3_slab);
}
static void w3_noop(uv_handle_t *h) { (void)h; }

struct w3_server_conn {
  uv_tcp_t handle;
  uv_write_t wreq;
  uv_buf_t buf;
};

struct w3_client {
  uv_tcp_t handle;
  uv_connect_t creq;
  uv_write_t wreq;
  uv_buf_t buf;
  struct w3_state *w;
};

static void w3_start_round(struct w3_state *w);

static void w3_client_read(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf)
{
  (void)buf;
  struct w3_client *cl = stream->data;
  if (nread > 0) {
    uv_read_stop(stream);
    uv_close((uv_handle_t *)stream, free_handle);
    cl->w->remaining--;
    if (cl->w->remaining > 0)
      w3_start_round(cl->w);
    else {
      uv_close((uv_handle_t *)&cl->w->server, w3_noop);
      app_done(cl->w->a);
    }
  } else if (nread < 0) {
    uv_close((uv_handle_t *)stream, free_handle);
  }
}

static void w3_server_read(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf)
{
  struct w3_server_conn *sc = stream->data;
  if (nread > 0) {
    uv_read_stop(stream);
    sc->buf = uv_buf_init(buf->base, nread);
    uv_write(&sc->wreq, stream, &sc->buf, 1, NULL);
    uv_close((uv_handle_t *)stream, free_handle);
  } else if (nread < 0) {
    uv_close((uv_handle_t *)stream, free_handle);
  }
}

static void w3_on_connect(uv_connect_t *req, int status)
{
  struct w3_client *cl = req->data;
  if (status < 0) return;
  cl->buf = uv_buf_init("PING", 4);
  uv_write(&cl->wreq, (uv_stream_t *)&cl->handle, &cl->buf, 1, NULL);
  uv_read_start((uv_stream_t *)&cl->handle, w3_alloc, w3_client_read);
}

static void w3_on_connection(uv_stream_t *server, int status)
{
  if (status < 0) return;
  struct w3_state *w = server->data;
  struct w3_server_conn *sc = calloc(1, sizeof(*sc));
  uv_tcp_init(w->a->loop, &sc->handle);
  sc->handle.data = sc;
  uv_accept(server, (uv_stream_t *)&sc->handle);
  uv_read_start((uv_stream_t *)&sc->handle, w3_alloc, w3_server_read);
}

static void w3_start_round(struct w3_state *w)
{
  struct w3_client *cl = calloc(1, sizeof(*cl));
  cl->w = w;
  uv_tcp_init(w->a->loop, &cl->handle);
  cl->handle.data = cl;
  cl->creq.data = cl;
  struct sockaddr_in addr;
  uv_ip4_addr("127.0.0.1", w->port, &addr);
  uv_tcp_connect(&cl->creq, &cl->handle, (const struct sockaddr *)&addr, w3_on_connect);
}

static struct w3_state w3_st;

static void w3_setup(struct app *a)
{
  w3_st.a = a;
  w3_st.remaining = W3_ROUNDS;
  uv_tcp_init(a->loop, &w3_st.server);
  w3_st.server.data = &w3_st;
  struct sockaddr_in addr;
  uv_ip4_addr("127.0.0.1", 0, &addr);
  uv_tcp_bind(&w3_st.server, (const struct sockaddr *)&addr, 0);
  uv_listen((uv_stream_t *)&w3_st.server, 128, w3_on_connection);
  struct sockaddr_in bound;
  int namelen = sizeof(bound);
  uv_tcp_getsockname(&w3_st.server, (struct sockaddr *)&bound, &namelen);
  w3_st.port = ntohs(bound.sin_port);
  w3_start_round(&w3_st);
}

/* ── W4: Handle Lifecycle (triggers 3503) ────────────────── */

#define W4_ROUNDS  10

struct w4_state {
  struct app *a;
  int remaining;
};

static void w4_on_conn(uv_stream_t *s, int st) { (void)s; (void)st; }

static void w4_do_round(struct w4_state *w);

static void w4_next(uv_timer_t *handle)
{
  struct w4_state *w = handle->data;
  uv_close((uv_handle_t *)handle, free_handle);
  w->remaining--;
  if (w->remaining > 0)
    w4_do_round(w);
  else
    app_done(w->a);
}

static void w4_do_round(struct w4_state *w)
{
  uv_tcp_t *tcp = calloc(1, sizeof(*tcp));
  uv_tcp_init(w->a->loop, tcp);
  uv_close((uv_handle_t *)tcp, free_handle);

  struct sockaddr_in addr;
  uv_ip4_addr("127.0.0.1", 0, &addr);
  int r = uv_tcp_bind(tcp, (const struct sockaddr *)&addr, 0);
  if (r == 0)
    r = uv_listen((uv_stream_t *)tcp, 5, w4_on_conn);

  if (r != 0) {
    /* Fixed version: correctly rejected → schedule next round */
    uv_timer_t *t = calloc(1, sizeof(*t));
    uv_timer_init(w->a->loop, t);
    t->data = w;
    uv_timer_start(t, w4_next, 0, 0);
  }
  /* Buggy version: bind/listen succeeded on closing handle.
   * Event loop is now inconsistent → will hang or crash.
   * Do not call app_done; let timeout detect the failure. */
}

static struct w4_state w4_st;

static void w4_setup(struct app *a)
{
  w4_st.a = a;
  w4_st.remaining = W4_ROUNDS;
  w4_do_round(&w4_st);
}

/* ── W5: Heartbeat Monitor ───────────────────────────────── */

#define W5_TICKS  30

struct w5_state {
  struct app *a;
  uv_timer_t timer;
  int remaining;
};

static void w5_tick(uv_timer_t *handle)
{
  struct w5_state *w = handle->data;
  w->remaining--;
  if (w->remaining <= 0) {
    uv_timer_stop(handle);
    uv_close((uv_handle_t *)handle, w3_noop);
    app_done(w->a);
  }
}

static struct w5_state w5_st;

static void w5_setup(struct app *a)
{
  w5_st.a = a;
  w5_st.remaining = W5_TICKS;
  uv_timer_init(a->loop, &w5_st.timer);
  w5_st.timer.data = &w5_st;
  uv_timer_start(&w5_st.timer, w5_tick, 100, 100);
}

/* ── main ─────────────────────────────────────────────────── */

int main(void)
{
  uv_loop_t *loop = uv_default_loop();
  struct app a = { .loop = loop, .remaining = 5 };
  gettimeofday(&a.t0, NULL);

  w1_setup(&a);
  w2_setup(&a);
  w3_setup(&a);
  w4_setup(&a);
  w5_setup(&a);

  uv_run(loop, UV_RUN_DEFAULT);

  uv_loop_close(loop);
  return 0;
}
