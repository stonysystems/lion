# ironfleet reference dataset #2 (clean-clone validation run)

Second reference batch, collected on the paper topology (replicas
on zoo-002 EPYC 7702P, client on zoo-004) by `../../collect_paper_data.sh`
(STAGES=ironfleet) from the **fresh GitHub clone** validation run — including
a from-scratch scons/dotnet build of the C# app (the batch that exposed and
now verifies the MSBuild-`OUTDIR` fix, commit `d9c23bb6`).

Same layout as `../ref-result` (raw `.reqlog`/`.cpulog` per cell×rep,
`PROVENANCE.txt`, exported `table.{md,tex}`). Cell-by-cell agreement with
batch #1: throughput 3244/1985/1638/326 vs 3275/1970/1661/342 req/s,
Lion/C# = 1.98× unpinned / 6.09× single-core (batch #1: 1.97× / 5.76×).

Note on the CPU column: `ps -o %cpu` is a lifetime average, and the .NET
startup burst inflates the first seconds (this batch's raw `csharp_1core`
r1/r3 logs open at ~166% before decaying to the true 100% steady state, with
throughput unaffected). The exported peak therefore skips the first 5 samples;
raw logs keep everything.
