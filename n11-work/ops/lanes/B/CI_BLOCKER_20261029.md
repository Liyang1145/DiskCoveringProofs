# Lane B CI blocker — 2026-10-29

## Observation

Workflow `n11-lean-build`, run `40802064355` (head `2f5a2d11`), was inspected
through the live job log `123215323857`.  Both lane-B aggregate targets exited
nonzero for the same non-mathematical reason: required frozen dependencies were
killed by the workflow's 900 MB memory guard.

```
03:17:59Z OOM-GUARD killing lean (avail=892MB)
03:18:00Z error: Lean exited with code 137
03:18:00Z ✖ [8966/9298] Building N11Formalization.Ladder49_jt_kkt_z (911s)
03:18:00Z Some required targets logged failures:
03:18:00Z - N11Formalization.DBMSourceTreeData
03:18:00Z - N11Formalization.Ladder49_jt_kkt_z
03:18:00Z === EXIT N11Formalization.Paid16GeneralNext1182 1
03:18:00Z === BUILD N11Formalization.EnergyTerminalBatchB13
...
03:31:42Z MEM 03:31:42 avail=832MB top: 8294664 .../lean .../N11Formalizatio
03:31:42Z OOM-GUARD killing lean (avail=830MB)
03:31:44Z error: Lean exited with code 137
03:31:44Z ✖ [8948/9299] Building N11Formalization.Ladder49_jt_kkt_z (813s)
03:31:46Z Some required targets logged failures:
03:31:46Z - N11Formalization.DBMSourceTreeData
03:31:46Z - N11Formalization.Ladder49_jt_kkt_z
03:31:46Z === EXIT N11Formalization.EnergyTerminalBatchB13 1
```

There is no lane-B `error:` line and no `Sorry`/axiom report in this region.
This run therefore does **not** say either B theorem is false or ill-typed.  It
also does not validate the current split proof in `Paid16GeneralNext1182.lean`,
because that file changed by 112 lines after head `2f5a2d11`.

## Consequence

The repeated first failure is in the shared frozen dependency closure, not in
the lane-B aggregation code.  The newest workflow run `40803687450` (head
`7f7157f4`) was still queued with zero jobs at 03:57Z.  Local `.lake/build` has
no oleans for `DBMSourceTreeData`, `Ladder49_jt_kkt_z`, or `EnergyTerminalBatchB12`.

## Recommended next action for the workflow owner

Obtain one cached, successful build of `DBMSourceTreeData` and
`Ladder49_jt_kkt_z` on a runner with a lower or no artificial OOM threshold, then
restore that cache for the serial lane build.  Alternatively, run those two
dependencies in a dedicated unguarded (or higher-memory) job before lane B.
Simply moving lane B earlier cannot fix this: every B target imports the same
closure.  Only after those dependencies replay should the next lane-B verdict be
read from the first `=== EXIT` line for `EnergyTerminalResidualCensus` and
`EnergyTerminalBatchB13Main`.

