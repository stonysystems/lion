/*
 * libevent issue #984: phantom EV_ET event dispatch
 *
 * Bug: evmap_io_active_ preserves the internal EV_ET flag during event
 * masking.  When a fd registered only for EV_CLOSED receives EPOLLHUP
 * (mapped to EV_READ|EV_WRITE), the mask reduces to just EV_ET — which
 * still passes the filter, causing a phantom callback.  The real
 * EV_CLOSED is never delivered, so the application hangs.
 *
 * Affected: all versions before commit c10cde4c (May 2020)
 * Fixed:    release-2.1.12-stable
 */

#include <event2/event.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/time.h>

struct ctx {
  struct event_base *base;
  int remote_fd;
  struct timeval start;
};

static void
close_detected(evutil_socket_t fd, short what, void *arg)
{
  (void)fd;
  struct ctx *c = (struct ctx *)arg;

  if (what & EV_CLOSED) {
    struct timeval now;
    gettimeofday(&now, NULL);
    long ms = (now.tv_sec - c->start.tv_sec) * 1000 +
              (now.tv_usec - c->start.tv_usec) / 1000;
    printf("{\"test\":\"issue_984\",\"outcome\":\"PASS\",\"elapsed_ms\":%ld}\n", ms);
    event_base_loopbreak(c->base);
    return;
  }
  /*
   * Phantom EV_ET without EV_CLOSED: ignore.
   * Edge-triggered means this fd won't fire again → hang.
   */
}

static void
trigger_close(evutil_socket_t fd, short what, void *arg)
{
  (void)fd; (void)what;
  struct ctx *c = (struct ctx *)arg;
  close(c->remote_fd);
  c->remote_fd = -1;
}

int main(void)
{
  int sv[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) < 0) {
    perror("socketpair");
    return 1;
  }

  struct event_base *base = event_base_new();
  struct ctx c = { .base = base, .remote_fd = sv[1] };
  gettimeofday(&c.start, NULL);

#ifdef EV_CLOSED
  struct event *ev = event_new(base, sv[0],
      EV_CLOSED | EV_ET | EV_PERSIST,
      close_detected, &c);
  event_add(ev, NULL);

  struct event *timer = evtimer_new(base, trigger_close, &c);
  struct timeval tv = { 0, 200000 };
  evtimer_add(timer, &tv);

  event_base_dispatch(base);

  event_free(ev);
  event_free(timer);
#else
  printf("{\"test\":\"issue_984\",\"outcome\":\"N/A\",\"elapsed_ms\":0}\n");
#endif

  if (c.remote_fd >= 0) close(c.remote_fd);
  close(sv[0]);
  event_base_free(base);
  return 0;
}
