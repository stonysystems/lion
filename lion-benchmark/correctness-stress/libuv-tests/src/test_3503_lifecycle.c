/*
 * libuv issue #3503: bind/listen on a closing handle
 *
 * Bug: uv_tcp_bind() and uv_listen() do not check UV_HANDLE_CLOSING.
 * Operations proceed on a half-torn-down handle, leaving the event loop
 * in an inconsistent state (hang or crash).
 *
 * Affected: v1.43.0 (and all versions before v1.44.2)
 * Fixed:    v1.44.2 (commit 8bcd689c04)
 */

#include <uv.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>

static void on_connect(uv_stream_t *server, int status) {
  (void)server; (void)status;
}

int main(void)
{
  struct timeval t0;
  gettimeofday(&t0, NULL);

  uv_loop_t loop;
  uv_tcp_t tcp;
  struct sockaddr_in addr;

  uv_ip4_addr("127.0.0.1", 0, &addr);
  uv_loop_init(&loop);
  uv_tcp_init(&loop, &tcp);

  uv_close((uv_handle_t *)&tcp, NULL);

  int r1 = uv_tcp_bind(&tcp, (const struct sockaddr *)&addr, 0);
  int r2 = 0;
  if (r1 == 0)
    r2 = uv_listen((uv_stream_t *)&tcp, 5, on_connect);

  if (r1 != 0 || r2 != 0) {
    /* Fixed version: bind/listen correctly rejected on closing handle */
    struct timeval now;
    gettimeofday(&now, NULL);
    long ms = (now.tv_sec - t0.tv_sec) * 1000 +
              (now.tv_usec - t0.tv_usec) / 1000;
    printf("{\"test\":\"issue_3503\",\"outcome\":\"PASS\",\"elapsed_ms\":%ld}\n", ms);
    uv_run(&loop, UV_RUN_DEFAULT);
    uv_loop_close(&loop);
    return 0;
  }

  /* Buggy version: bind/listen succeeded on closing handle.
   * uv_run() will crash (assertion in uv__stream_destroy) or hang. */
  uv_run(&loop, UV_RUN_DEFAULT);

  return 0;
}
