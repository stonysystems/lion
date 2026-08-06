// Falsification probe for the timer-fire mutants (M01–M04): one uncancelled
// sleep, duration argv[1] in ms (≥256 ms lands in an upper wheel level and
// must survive a cascade), placement argv[2]:
//   "root"  — the sleep IS the block_on future (re-polled every tick, so it
//             also exercises the executor's root-poll redundancy);
//   "spawn" — the sleep runs inside a spawned task (waker-driven only).
// Usage: apply a mutant patch, `cargo build --release`, run with `timeout`.
// Key result (see ../results/matrix.md): under M02 "spawn 500" hangs while
// "root 500" completes one park-cap (~100 ms) late.
fn main() {
  let ms: u64 = std::env::args().nth(1).unwrap_or_else(|| "500".into()).parse().unwrap();
  let mode = std::env::args().nth(2).unwrap_or_else(|| "root".into());
  let runtime = rt::runtime::Builder::new_current_thread()
    .enable_all()
    .build()
    .unwrap();
  let t0 = std::time::Instant::now();
  match mode.as_str() {
    "spawn" => match runtime {
      rt::runtime::RuntimeInstance::Single(r) => r.block_on(async move {
        rt::spawn(async move {
          rt::time::sleep(std::time::Duration::from_millis(ms)).await;
        }).await.unwrap();
      }),
      _ => unreachable!(),
    },
    _ => match runtime {
      rt::runtime::RuntimeInstance::Single(r) => r.block_on(async move {
        rt::time::sleep(std::time::Duration::from_millis(ms)).await;
      }),
      _ => unreachable!(),
    },
  }
  println!("mode={} slept {} ms, wall {} ms", mode, ms, t0.elapsed().as_millis());
}
