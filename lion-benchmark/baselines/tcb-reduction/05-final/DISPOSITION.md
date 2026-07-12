# T7b 终局处置：timer 基准回归 = T7 bug 修复的计划内行为变化

对拍协议允许的三类计划内行为变化之一（"T7 bug 修复"），论证如下。

## A/B 决定性实验（同一工作树、同一构建配置）

timer_st --threads 1 --load 10000 --duration 3，逐轮原始值（ops/s）：

- 00-baseline（修复前提交 93194423）：3377356（gate 存档 trimmed mean）
- 原始带 bug 扫描算法临时还原到当前树：3329057 / 3346985 / 3354394
- 当前正确实现（level_band 环序扫描 + level_counts 空层跳过）：
  2691849 / 2668081 / 2673732 / 2600132 / 2611456

## 结论

旧吞吐由 bug 虚高：错误的 early-exit 让 reactor park 过头、定时器晚触发、
到期批量堆积，减少了 park/wake 周期数。正确实现为每个真正到期的定时器
准时唤醒——多出的唤醒正是准时投递所必需的。level_counts 优化（~2%）
证明扫描本身的开销从来不是主因。

功能门禁全绿：stress 60/60 零 hang ×4 轮、utility 24/24 ×4 轮、
ci.sh 9 crate 零错误。tokio/monoio 对照组全程平稳（±2%）。

论文影响：重新生成的 timer 图数字更低但诚实；叙事更强——
"形式验证发现并修复了一个使 timer 吞吐虚高 ~25% 的晚触发 bug"。

## 补充门禁（复核后执行）

### T8 内存门禁：PASS（精确吻合理论值）
10^7 个完成态任务（1000 波 ×10k，波间任务全部完成）：
- 基线提交 93194423：RSS 增量 234,376 KB
- campaign 后：RSS 增量 235,644 KB
- **campaign 净增量 = 1,268 KB ≈ 位图理论值 1,220 KB**——TID 台账无意外放大。
- 门禁副产物发现：234MB 的主体增长为**前置存在**的 task_slab 稠密窗口
  （lion-slab 以单调 TID 为键、remove 留 None 不收缩——与已披露的
  ResourceSlab no-reuse 同类），应一并挂入 generational-ids 治理计划。
  复现器：examples/ledger_mem.rs。

### T11 panic 专项差分：PASS（逐字节一致）
examples/panic_probe.rs 在基线与 campaign 构建上行为完全一致：
task 内 panic 无隔离地穿透 poll 展开至 main（lion 前置设计，无 per-task
catch_unwind），消息与传播点相同。与"构造上不变"的论证互相印证。
