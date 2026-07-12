/*
 * Combined libevent stress workload
 *
 * Ports the same test design as the Rust (Tokio/Lion) correctness-stress
 * "combined" run: one event loop concurrently driving the same core-subsystem
 * workloads under a heartbeat, with a timeout = hang oracle. The execution model
 * differs (libevent event loop + callbacks vs Rust async/await), so the code is
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
 * W3: HTTP Filter Echo      — Network I/O (Rust: the echo workload). An evhttp
 *     server with a passthrough bufferevent filter, 20 client requests.
 *     Also exercises issue 237 (be_filter_ctrl missing fd event setup).
 *
 * W4: Connection Lifecycle  — libevent's own bug-triggering subsystem: close
 *     detection via EV_CLOSED (socketpair → register → remote close → detect),
 *     exercising issue 984 (phantom EV_ET swallows the close notification).
 *
 * W5: Heartbeat Monitor     — Heartbeat, the liveness canary (as in Rust).
 *     30 ticks × 100ms periodic timer
 *
 * Expected results:
 *   2.1.5-beta:    HANG — W3 stalls (issue 237)
 *   2.1.11-stable: HANG — W4 stalls (issue 984)
 *   2.1.12-stable: PASS — all workloads complete
  *
 * DISCLOSURE: W4 (and, for libevent, W3's filter layer) is the library's own
 * documented bug-trigger subsystem embedded in the mix; a combined HANG on a
 * bug-carrying version is attributable to it (see summary.md), not to the
 * neutral W1/W2/W5 mix.
 */

#include <event2/event.h>
#include <event2/http.h>
#include <event2/bufferevent.h>
#include <event2/buffer.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <netinet/in.h>

/* ── app-wide completion tracking ─────────────────────────── */

struct app {
  struct event_base *base;
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
    event_base_loopbreak(a->base);
  }
}

/* ── W1: Timer Cancel Storm ───────────────────────────────
 *
 * Analog of Tokio:
 *   tokio::select! {
 *       _ = tokio::time::sleep(Duration::from_secs(10)) => unreachable!(),
 *       _ = tokio::time::sleep(Duration::from_millis(1)) => {}
 *   }
 *
 * libevent equivalent: register two timers; when the 1ms timer fires,
 * cancel the 10s timer with evtimer_del().
 */

#define W1_PAIRS  500
#define W1_ITERS  100

struct w1_pair {
  struct app *a;
  struct event *ev_long;
  struct event *ev_short;
  int remaining;
};

static int w1_active;

static void w1_long_cb(evutil_socket_t fd, short what, void *arg)
{
  (void)fd; (void)what; (void)arg;
  /* should never fire — short timer cancels it */
}

static void w1_short_cb(evutil_socket_t fd, short what, void *arg)
{
  (void)fd; (void)what;
  struct w1_pair *p = arg;

  evtimer_del(p->ev_long);           /* cancel the 10s timer */
  p->remaining--;

  if (p->remaining > 0) {
    struct timeval tv_long  = {10, 0};
    struct timeval tv_short = {0, 1000};  /* 1ms */
    evtimer_add(p->ev_long,  &tv_long);
    evtimer_add(p->ev_short, &tv_short);
  } else {
    event_free(p->ev_long);
    event_free(p->ev_short);
    w1_active--;
    if (w1_active == 0)
      app_done(p->a);
    free(p);
  }
}

static void w1_setup(struct app *a)
{
  w1_active = W1_PAIRS;
  for (int i = 0; i < W1_PAIRS; i++) {
    struct w1_pair *p = calloc(1, sizeof(*p));
    p->a = a;
    p->remaining = W1_ITERS;
    p->ev_long  = evtimer_new(a->base, w1_long_cb,  p);
    p->ev_short = evtimer_new(a->base, w1_short_cb, p);
    struct timeval tv_long  = {10, 0};
    struct timeval tv_short = {0, 1000};
    evtimer_add(p->ev_long,  &tv_long);
    evtimer_add(p->ev_short, &tv_short);
  }
}

/* ── W2: Callback Chain Storm ─────────────────────────────
 *
 * Analog of Tokio:
 *   for _ in 0..100 {                       // 100 parents
 *       tokio::spawn(async {
 *           for _ in 0..10 {                // 10 children each
 *               tokio::spawn(async {
 *                   tokio::task::yield_now().await;   // yield once
 *               });
 *           }
 *       });
 *   }
 *
 * libevent equivalent: 100 parent 0-delay timers; each parent callback
 * registers 10 child 0-delay timers; each child re-fires once (yield),
 * then completes.
 */

#define W2_PARENTS   100
#define W2_CHILDREN  10

struct w2_child {
  struct event *ev;
  int yields;           /* fires remaining (1 = yield once, then done) */
  int *parent_counter;  /* parent's children_remaining */
  int *global_counter;  /* parents_remaining */
  struct app *a;
};

static int w2_parents_remaining;

static void w2_child_cb(evutil_socket_t fd, short what, void *arg)
{
  (void)fd; (void)what;
  struct w2_child *c = arg;
  c->yields--;
  if (c->yields > 0) {
    /* yield: re-register with 0-delay */
    struct timeval tv = {0, 0};
    evtimer_add(c->ev, &tv);
  } else {
    /* child done */
    event_free(c->ev);
    (*c->parent_counter)--;
    if (*c->parent_counter == 0) {
      /* all children of this parent done */
      free(c->parent_counter);
      w2_parents_remaining--;
      if (w2_parents_remaining == 0)
        app_done(c->a);
    }
    free(c);
  }
}

struct w2_parent {
  struct event *ev;
  struct app *a;
};

static void w2_parent_cb(evutil_socket_t fd, short what, void *arg)
{
  (void)fd; (void)what;
  struct w2_parent *p = arg;
  event_free(p->ev);

  int *counter = malloc(sizeof(int));
  *counter = W2_CHILDREN;

  for (int i = 0; i < W2_CHILDREN; i++) {
    struct w2_child *c = calloc(1, sizeof(*c));
    c->a = p->a;
    c->yields = 2;          /* fire once (spawn), re-fire once (yield) */
    c->parent_counter = counter;
    c->ev = evtimer_new(p->a->base, w2_child_cb, c);
    struct timeval tv = {0, 0};
    evtimer_add(c->ev, &tv);
  }
  free(p);
}

static void w2_setup(struct app *a)
{
  w2_parents_remaining = W2_PARENTS;
  for (int i = 0; i < W2_PARENTS; i++) {
    struct w2_parent *p = calloc(1, sizeof(*p));
    p->a = a;
    p->ev = evtimer_new(a->base, w2_parent_cb, p);
    struct timeval tv = {0, 0};
    evtimer_add(p->ev, &tv);
  }
}

/* ── W3: HTTP Filter Echo ─────────────────────────────────
 *
 * Analog of Lion W6 (TCP echo waves), adapted for libevent's
 * HTTP + bufferevent architecture.
 *
 * Server uses evhttp_set_bevcb to return a passthrough bufferevent
 * filter — the standard pattern for adding a protocol layer
 * (compression, rate-limiting, etc.).
 *
 * On 2.1.5-beta, be_filter_ctrl omits fd event registration,
 * so the server never reads the request and the client hangs.
 */

#define W3_REQUESTS  20

struct w3_state {
  struct app *a;
  struct evhttp *http;
  int port;
  int remaining;
};

static enum bufferevent_filter_result
w3_passthrough(struct evbuffer *src, struct evbuffer *dst,
               ev_ssize_t limit, enum bufferevent_flush_mode mode, void *ctx)
{
  (void)limit; (void)mode; (void)ctx;
  evbuffer_remove_buffer(src, dst, evbuffer_get_length(src));
  return BEV_OK;
}

static struct bufferevent *
w3_bevcb(struct event_base *base, void *arg)
{
  (void)arg;
  struct bufferevent *bev =
      bufferevent_socket_new(base, -1, BEV_OPT_CLOSE_ON_FREE);
  return bufferevent_filter_new(bev, w3_passthrough, w3_passthrough,
                                BEV_OPT_CLOSE_ON_FREE, NULL, NULL);
}

static void w3_send_next(struct w3_state *w);

struct w3_req_ctx {
  struct w3_state *w;
  struct evhttp_connection *conn;
};

static void
w3_response(struct evhttp_request *req, void *arg)
{
  (void)req;
  struct w3_req_ctx *rc = arg;
  struct w3_state *w = rc->w;
  evhttp_connection_free(rc->conn);
  free(rc);
  w->remaining--;
  if (w->remaining > 0)
    w3_send_next(w);
  else
    app_done(w->a);
}

static void
w3_send_next(struct w3_state *w)
{
  /* new connection per request — matches Lion's wave-of-connections pattern */
  struct w3_req_ctx *rc = malloc(sizeof(*rc));
  rc->w = w;
  rc->conn = evhttp_connection_base_new(w->a->base, NULL, "127.0.0.1", w->port);
  struct evhttp_request *req = evhttp_request_new(w3_response, rc);
  evhttp_make_request(rc->conn, req, EVHTTP_REQ_GET, "/echo");
}

static void
w3_handler(struct evhttp_request *req, void *arg)
{
  (void)arg;
  struct evbuffer *buf = evbuffer_new();
  evbuffer_add_printf(buf, "OK");
  evhttp_send_reply(req, 200, "OK", buf);
  evbuffer_free(buf);
}

static struct w3_state w3_st;

static void w3_setup(struct app *a)
{
  w3_st.a = a;
  w3_st.remaining = W3_REQUESTS;
  w3_st.http = evhttp_new(a->base);
  evhttp_set_bevcb(w3_st.http, w3_bevcb, NULL);
  evhttp_set_gencb(w3_st.http, w3_handler, NULL);

  struct evhttp_bound_socket *bound =
      evhttp_bind_socket_with_handle(w3_st.http, "127.0.0.1", 0);
  evutil_socket_t fd = evhttp_bound_socket_get_fd(bound);
  struct sockaddr_in sin;
  ev_socklen_t len = sizeof(sin);
  getsockname(fd, (struct sockaddr *)&sin, &len);
  w3_st.port = ntohs(sin.sin_port);

  w3_send_next(&w3_st);
}

/* ── W4: Connection Lifecycle (EV_CLOSED) ─────────────────
 *
 * Simulates server-side connection lifecycle monitoring:
 * after finishing I/O, monitor a socket for remote close using
 * EV_CLOSED — the pattern used by Envoy and other libevent-based
 * servers.
 *
 * On pre-2.1.12, close() → EPOLLHUP → the event masking logic
 * preserves EV_ET but strips the real events, so the callback
 * fires with phantom EV_ET and EV_CLOSED is never delivered.
 */

#define W4_ROUNDS  10

struct w4_state {
  struct app *a;
  int remaining;
  int local_fd;
  int remote_fd;
  struct event *close_ev;
  struct event *trigger;
};

static void w4_start_round(struct w4_state *w);

static void
w4_close_detected(evutil_socket_t fd, short what, void *arg)
{
  (void)fd;
  struct w4_state *w = arg;
  if (what & EV_CLOSED) {
    event_free(w->close_ev);
    close(w->local_fd);
    w->remaining--;
    if (w->remaining > 0)
      w4_start_round(w);
    else
      app_done(w->a);
  }
  /* phantom EV_ET without EV_CLOSED: ignored → hang */
}

static void
w4_trigger_close(evutil_socket_t fd, short what, void *arg)
{
  (void)fd; (void)what;
  struct w4_state *w = arg;
  event_free(w->trigger);
  close(w->remote_fd);
  w->remote_fd = -1;
}

static void
w4_start_round(struct w4_state *w)
{
  int sv[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) < 0)
    return;
  w->local_fd  = sv[0];
  w->remote_fd = sv[1];

#ifdef EV_CLOSED
  w->close_ev = event_new(w->a->base, sv[0],
      EV_CLOSED | EV_ET | EV_PERSIST,
      w4_close_detected, w);
  event_add(w->close_ev, NULL);

  w->trigger = evtimer_new(w->a->base, w4_trigger_close, w);
  struct timeval tv = {0, 50000};  /* 50ms */
  evtimer_add(w->trigger, &tv);
#else
  close(sv[0]);
  close(sv[1]);
  w->remaining--;
  if (w->remaining <= 0)
    app_done(w->a);
  else
    w4_start_round(w);
#endif
}

static struct w4_state w4_st;

static void w4_setup(struct app *a)
{
  w4_st.a = a;
  w4_st.remaining = W4_ROUNDS;
  w4_start_round(&w4_st);
}

/* ── W5: Heartbeat Monitor ────────────────────────────────
 *
 * Analog of Tokio/Lion heartbeat:
 *   for _ in 0..30 {
 *       tokio::time::sleep(Duration::from_millis(100)).await;
 *   }
 */

#define W5_TICKS  30

struct w5_state {
  struct app *a;
  struct event *ev;
  int remaining;
};

static void
w5_tick(evutil_socket_t fd, short what, void *arg)
{
  (void)fd; (void)what;
  struct w5_state *w = arg;
  w->remaining--;
  if (w->remaining > 0) {
    struct timeval tv = {0, 100000};  /* 100ms */
    evtimer_add(w->ev, &tv);
  } else {
    event_free(w->ev);
    app_done(w->a);
  }
}

static struct w5_state w5_st;

static void w5_setup(struct app *a)
{
  w5_st.a = a;
  w5_st.remaining = W5_TICKS;
  w5_st.ev = evtimer_new(a->base, w5_tick, &w5_st);
  struct timeval tv = {0, 100000};
  evtimer_add(w5_st.ev, &tv);
}

/* ── main ─────────────────────────────────────────────────── */

int main(void)
{
  struct app a;
  a.base = event_base_new();
  a.remaining = 5;   /* W1–W5 */
  gettimeofday(&a.t0, NULL);

  w1_setup(&a);      /* timer cancel storm   */
  w2_setup(&a);      /* callback chain storm */
  w3_setup(&a);      /* HTTP filter echo     */
  w4_setup(&a);      /* connection lifecycle */
  w5_setup(&a);      /* heartbeat monitor   */

  event_base_dispatch(a.base);

  event_base_free(a.base);
  return 0;
}
