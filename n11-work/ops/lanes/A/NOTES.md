# Lane A notes

CURRENT (session 168): the q0 first-owner repairs are **drafted / source
preflight PASS / CI pending**.  The latest completed lane-A log was from run
`41378003343` (job `125062414500`, HEAD `016484e6`); it confirms the old
failures, not the repaired files.  Run `41380560959` at `a29e4ee1` was still in
progress and its log was not yet downloadable.  No kernel credit is claimed.

## Ledger

- CI-green paid Lane A targets: `C450ChainCompletionMain`,
  `C450ChainCompletionAudit`, `Cos`, `Mono`, `Bins`, `EndpointChecks`, and
  `UpperTables`.
- Repair only the first owning error; dependency-red descendants are not
  diagnostics.  A green q0 chain would prove `q0_degree3 : Q0RunExclusion 1`
  (1/7).
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions
  or raised heartbeats.
- `SectorValid`, strict `totalUpper < piLo`, `Q0Degree3AreaInput`, all seven
  exclusions, and the arbitrary-centre theorem remain unpaid.

ROOT-IMPORT REQUEST: import the CI-green `C450ChainCompletion` and
`C450ChainCompletionMain` in the stage-1 root (supervisor-only edit).

## Condensed history

- Sessions 115--153 exactly audited 21 edge peaks, 21 discrete peaks, 18,441
  sector points, 72/72 bins, 18,369 within-bin steps, 63/63 jumps, and bin-3
  (256 nodes / 32,640 pairs).  Global sector unimodality was refuted; the valid
  route is bin-wise.  These are source/arithmetic checks, not kernel credit.
- Sessions 142--153 split 21 edge and 9 sector peaks and repaired the bin-3
  half bound.  All split/calculus/bin/table modules remain CI pending.
- C450/Main/Audit, `Cos`, `Mono`, `Bins`, `EndpointChecks`, and `UpperTables`
  are CI-green.  Root still carries both HARK markers.
- Sessions 158--162 found and repaired earlier base errors, then identified CI
  lane routing as the reachability blocker.  Session 159 introduced
  `SevenClassQ0Deg3Repaired.lean`, a generated copy of frozen SHA
  `48d41f5d3a71c41adc3ff0af26f86740b2f4ed82383a037d182aac0f16075b61`
  adding only the missing census import and ear-count open.
- Sessions 165--166 made the strict-total division bounds goal-shaped with
  `div_le_div_of_nonneg_right`; exact ledger checks passed, but no Lean verdict
  was obtained.
- Session 167 read the live log of run `41378003343`.  First owners were the
  repaired-copy import placement, nine sector peak rational comparisons, and
  the 21 edge coefficient equalities.  The log's peak goal reduces to a huge
  fraction-to-fraction inequality; the edge goal reduces to a literal rational
  versus a two-term `Finset.sum`.  Fixes: move provenance below imports and add
  terminal `decide +kernel` to those bounded closed rational goals.  No frozen
  module, arithmetic table, or theorem statement changed.

## 2026-11-02 (session 168) -- old log confirmed; repaired tree audited

Re-downloaded run `41378003343` and inspected the exact goals: sector peak 01
reduces to an exact fraction inequality, while the edge `hcoeff` case «1»
reduces to `643066…1523 / 200…0000 = ∑ x ∈ {1,2}, …`.  This confirms that the
declared terminal kernel suffix targets the actual residual shapes rather than
an unrelated simplification step.  Regenerated all repaired modules
deterministically and reran the sector split-preservation checker.  Added
`audit_q0_degree3_kernel_repairs.py`, which checks import placement, both kernel
suffixes, banned tokens in all 11 repaired modules, and `TARGETS.txt`
registration.

The exact-rational emitter independently recomputed all nine sector maxima and
they equal `SevenClassQ0Deg3UpperTables.sectorMax`.  The older
`q0-degree3-piecewise-8.json` metadata is stale at sector rows 0--8 and witness
rows 1/8; the emitter already binds to recomputed exact values and prints the
drift, so this is not substituted by a cached maximum.

**Files / SHA256.**
`SevenClassQ0Deg3Repaired.lean` `37317833f1bc1d1066edc0f3cb866069657d27f39826bf4f6c93bd014517d3d3`;
`SevenClassQ0Deg3UpperReductionUnimodalBase.lean`
`3e38d206b45fe1bb6bf7c2f020d862ea37294862085b93cf71849e5c5585519b`;
`emit_q0_degree3_repaired.py`
`94674838008d6d3a1a0d65dc48b5614a444e815565e9f8694b0bd54211c2233f`;
`emit_q0_degree3_sector_peak.py`
`84ae09862ea1001a9cdc1216a1d1bfb2ac9abc4d43705ab07fd2110922bc6736`;
`split_q0_degree3_edge_peak.py`
`4cc9cb0bf28ef780df2e125269667b40d0de3d3afa05522bd47810278e9b6765`;
`audit_q0_degree3_kernel_repairs.py`
`10b7ff7f3e03d708295098f91619efa26d99981cb0366bb2bdaf447d2cf5ca45`.
Sector rows 00--08 SHA256:
`0762019a6f0b612e0ecf67f1c27f1e210a2bd352153ea759ef5e9fa5102a5755`,
`e4445823acf3dfcb0f79098c6c70356e021d715b9d3181f08b3399f541562f23`,
`a8bad4c1df79ba728a0bc6203dac3334d3db9082e8871aed41b78f8ade5dcc51`,
`880dff4aff0e88fa27950028456eb042900a12fb19440c6f78ba5d9a1b2f0af3`,
`42a849e914cec8c0c5eefdb2487fbc7530256ba55f0a95c6e895187e4ef202b3`,
`4214989487644b4d491cfa4a898ceac785dd64c8ba225e01932edd9f6fd18d9d`,
`c4d5a4ac6a91e311d52b559947dd51482d64cc849e0fcf825f03cbce7a33742e`,
`228cf7cf4cc1a59c1fb7d812c8eb9b6c786046ed1426fb08f7fb8d148b91752a`,
`1a57e4243c23f7b4ebee11dfd406200ab9a3c1f12ce82df581bf42c1b32eff13`.

**Checks (scope).** Deterministic emitter reruns PASS; sector split preservation
9/9 PASS; new source preflight PASS; `py_compile`, targeted banned-token scan,
and `git diff --check` PASS.  Exact Python recomputation matches all nine table
maxima.  A tiny local Lean probe (`Rat` inequality plus reflexivity) timed out
at 30 s, so there is **no local kernel verdict**; `decide +kernel` syntax and
elaboration remain CI-pending.

**Still unproved / unpaid.** `StrictTotal`, `Q0Exclusion`, all peak/shape/bin
assemblers, `Q0Degree3AreaInput`, the other six exclusions, and the
arbitrary-centre theorem remain CI pending/unpaid.  The in-progress run is not
evidence for this repaired worktree.

**Next concrete step.** Supervisor commits this worktree, then CI must reach
lane A and build `SevenClassQ0Deg3Repaired`, the nine `SectorPeak` rows, and
`UpperReductionUnimodalBase`.  Inspect the first owning error after
`SevenClassQ0Deg3Repaired`; if a kernel suffix fails, replace only that closed
goal with an explicitly rewritten rational comparison.

## 2026-11-02 (session 169) -- live CI boundary rechecked

Run `41380560959` remains **in_progress** at `a29e4ee1`; its single `build`
job `125106045871` started `2026-11-02T05:08:31Z` and has no conclusion.  This
commit does not contain the current uncommitted q0 repairs, so it cannot provide
a verdict on them.  No kernel credit is claimed.

Re-ran `audit_q0_degree3_kernel_repairs.py` (PASS: repaired-module import
placement, both terminal kernel suffixes, banned-token scan, TARGETS
registration; no kernel verdict) and
`check_q0_degree3_sector_peak_split.py` (PASS 9/9: split proof bodies preserved
up to the declared suffix).  `git diff --check` PASS.  A cached-Mathlib probe of
the giant exact `Rat` reflexivity equality was started, but it had not produced
a verdict when this session ended; it is not evidence.

**Next concrete step.** Supervisor must commit this worktree (including
`audit_q0_degree3_kernel_repairs.py`).  Then inspect the first lane-A target
result in CI.  If `SevenClassQ0Deg3Repaired` passes, inspect
`SevenClassQ0Deg3SectorPeak00`; on a red `decide +kernel`, replace only that
closed rational goal with an explicit rewritten comparison.  Do not treat the
currently in-progress `a29e4ee1` run as testing these files.

## 2026-11-02 (session 170) -- repair preflight repeated; local Lean unavailable

Re-ran `audit_q0_degree3_kernel_repairs.py`: PASS for import placement, both
terminal suffix shapes, banned-token scan, and all 11 repaired modules being
present in `TARGETS.txt`.  Re-ran
`check_q0_degree3_sector_peak_split.py`: PASS 9/9 split-body preservation.
`git diff --check` PASS.  The q0 repairs remain **drafted / source-preflight
PASS / CI pending**; no kernel credit is claimed.

Two bounded local syntax probes were attempted: a Mathlib `Rat`/reflexivity probe
under `mathlib-probe` timed out at 90 s, and a core-only `Nat` reflexivity probe
using `decide +kernel` timed out at 20 s while loading the toolchain.  Neither is
a verdict, so `decide +kernel` syntax/elaboration remains CI-pending.  No source
was changed on the basis of an inconclusive probe.

**Next concrete step.** After the supervisor commits this worktree, inspect CI's
first lane-A failure.  If `SevenClassQ0Deg3Repaired` and
`SevenClassQ0Deg3SectorPeak00` are green, proceed to peak rows 01--08 and then
`UpperReductionUnimodalBase`; if a suffix is red, replace only the owning closed
rational goal with an explicit normalized comparison.

## 2026-11-02 (session 171) -- live CI boundary isolated; no new verdict

Checked GitHub Actions directly rather than relying on the stale `LATEST.md`.
The q0 repair commit `00ac8c14` produced two non-Lean runs:
`41395436373` (delivery bytes, red only because `cover11/README.md` size does
not match its manifest) and `41395436408` (fresh n=12 arithmetic, green).
Neither ran Lean.  The Lean workflow run for `68d172d9` is `41394181326` and
is still `pending` with no job, so it has not tested lane A.

The newest downloadable Lean job is still `125062414500`, run `41378003343`
(HEAD `016484e6`, before the q0 repairs).  Its Actions log is capped at
281,186,304 bytes and ends during a `Patch120DomainPacket` warning before lane
A starts; therefore it cannot provide a lane-A verdict.  In that log, the
edge/sector q0 failure text is visible only in the pre-cap section already
recorded in session 168.

**Checks (scope).** Reran `audit_q0_degree3_kernel_repairs.py`: PASS (source
preflight only).  Reran `check_q0_degree3_sector_peak_split.py`: PASS 9/9.
Reran `check_q0_degree3_edge_peak_split.py`: PASS 21/21 byte-preserved edge
proofs and one declared terminal suffix.  A bounded `lake env lean --version`
probe in `/workspace/tools/mathlib-probe` timed out at 100 s, so no new local
Lean result.  `python tools/project_status.py --check` PASSed its handoff-index
scope.  No files in the frozen tree changed this session.

**Still unproved / unpaid.**  `decide +kernel` elaboration and all q0
peak/edge/assembler modules remain CI pending.  `StrictTotal`, `Q0Exclusion`,
`Q0Degree3AreaInput`, the other six exclusions, and the arbitrary-centre
theorem remain unpaid.

**Next concrete step.** The supervisor must make a Lean-path push (or rerun
`41394181326`) so CI emits a new job after the cached energy targets.  Inspect
the first lane-A `=== EXIT`/`error:` for `SevenClassQ0Deg3Repaired`; do not use
the delivery or n=12 success as Lean evidence.

## 2026-11-02 (session 172) -- repaired HEAD has no Lean run; probe inconclusive

Queried the public GitHub Actions API directly for `Liyang1145/DiskCoveringProofs`.
For repaired HEAD `00ac8c14`, only runs `41395436373` (delivery, failure) and
`41395436408` (fresh n=12 arithmetic, success) exist.  The newest Lean run is
still `41394181350` at `68d172d9`; it contains only a successful `math` job and
no n=11 Lean job.  Therefore there is still **no CI verdict** on any q0 repair.

Re-ran the three source preflights: `audit_q0_degree3_kernel_repairs.py` PASS
(no kernel verdict), sector peak split PASS 9/9, edge peak split PASS 21/21.
`python tools/project_status.py --check` PASS (handoff-index scope only).
A bounded core/Mathlib probe of peak row 0 reduced to a missing cached olean
`Mathlib/Data/Rat/Defs.olean`, not a Lean error in the proof; it is no evidence.
The prior whole-`Mathlib` giant-Rat probe timed out at 120 s and is also no
evidence.

**Files / hashes.** No Lean or generated table changed this session.  Existing
repaired-module SHA256 values remain as recorded in session 168.  This entry
changes only `n11-work/ops/lanes/A/NOTES.md`.

**Still unproved / unpaid.** `decide +kernel` elaboration and every repaired q0
peak/edge/assembler module remain CI pending.  `StrictTotal`, `Q0Exclusion`,
`Q0Degree3AreaInput`, six other exclusions, and the arbitrary-centre theorem
remain unpaid.

**Next concrete step.** Supervisor must push a path that launches the n=11 Lean
workflow on `00ac8c14` (or rerun the workflow with that SHA).  Inspect the first
lane-A `error:` after `SevenClassQ0Deg3Repaired`; do not use the n=12 or
delivery runs as Lean evidence.
