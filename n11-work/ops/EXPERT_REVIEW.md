# EXPERT REVIEW - n=11 Lean lanes

**Date:** 2026-10-30 (UTC)
**Scope:** `n11/work` at `22719e0d`; required state check, lane records, CI
artifacts, `git log --stat -8`, and current lane Lean/audit bytes. Run
`41035092539` is in progress at this head. Completed run `41027178023` on
`34b14918` is the newest full exit summary used below. No local project build,
Lean edit, or toolchain/lakefile change was made.

## Overall

- **C450 is closed, not open work.** `C450ChainCompletionMain` is CI-green and
  transitively imported by the current root through `EnergyTerminalBatchB12Main`.
  The 36-segment telescope, including the vacuous source-36 tail, is assembled.
- **B13 is now real count progress.** At `34b14918`, `DescentBounds`, `B13`, and
  `Paid16GeneralNext1182` exit 0. `B13.paid_count = 1997` is a kernel theorem.
  `B13Main` was red only because it imported the red optional census; current
  `521ca436...` removes that dependency, but its matching run is still pending.
- **C produced the first green residual payment theorem.** At `34b14918`,
  `Paid16MatrixCellCertificate` and `EnergyRefineN2341` both exit 0. The latter
  proves the strict radius inequality for source node 2341. It is not wired into
  a paid set, so the residual count has **not** moved yet.
- **A remains 0/7 classes.** The narrow-cosine argument is genuine mathematics,
  but the current suffix module is red through the `Bins` dependency and supplies
  no `EdgeDecFrom` theorem yet. At most edges 9/10 are near credit, i.e. 2/42
  edge-shape facts, not a metric-class exclusion.
- **Counts to carry forward:** formal B13 payment 1997/2386; documented residual
  389, whose cardinal equality is not yet a green kernel theorem; C's node 2341
  is a green one-ID refinement awaiting integration; class exclusions 0/7; C450
  36/36. The arbitrary-center full-disk theorem remains conditional.
- Checks run here: `project_status.py --check` (manifest/index only), the A/B/C
  static/exact audits, and artifact inspection. These are diagnostics, not Lean
  proof credit. No `sorry`, new axiom, float LP, or manifest count was accepted.

## Lane A

- The mathematical correction on 2026-10-30 was necessary and sound:
  for negative coefficient `b`, `cosHiReal x <= 0` does not imply
  `A*cosHiReal x - b < 0`; the threshold `cosHiReal x <= b/A` is the right
  sufficient condition. The file now uses that condition.
- The narrow-arc proof is plausible and internally coherent. `sinT 14` is shown
  nonnegative on `[2,3*pi/4]` from `sin x >= 2/3` and the degree-29 remainder
  `3^29/29! <= 1/100`; the exact node-1490 value is then below `-131/200`.
  The `-2/3` upper tail is retained only above `3*pi/4`.
- **Critical wiring gap:** `edgeWitness 9 = edgeWitness 10 = 1489`, while the new
  antitone interval begins at 1490. `edgeDecFrom_of_antitoneOn_from` requires the
  antitone interval to begin at the witness, so it cannot instantiate the new
  theorem. This is not a proof failure, but it means the suffix work has not yet
  produced a single `EdgeDecFrom` fact.
- `Bins` is still red on the completed run. The current worktree changes
  `Nat.mod_lt k.val (n := 256)` to `(y := 256)`, which matches Lean's binder name;
  only a matching exit 0 can settle it. `EndpointChecks` and both suffix modules
  remain transitive red until then.
- **Highest leverage:** first get `Bins` green without changing mathematics. Then
  add a next-node wrapper, e.g.
  `edgeDecFrom_of_antitoneOn_from_next (i w) (hw : edgeWitness i = w)
   (hstep : edgeUpper ... (w+1) <= edgeUpper ... w)
   (hanti : AntitoneOn (edgeHiReal (edgeCoeff i)) (Icc (nodeQ ... (w+1)) piHi)) :
   EdgeDecFrom i`.
  Split `k = w` from `w < k`; for edges 9/10 use `w=1489`, one exact 1489
  comparison, then the new narrow `-131/200` bound from 1490 and the `-2/3` tail.
  Prove the two ratio comparisons by exact `norm_num`.
- Do not launch a 42-leaf `fin_cases`/`norm_num` module. Put edges 9/10 in
  `SevenClassQ0Deg3EdgeShape.lean`, then add sectors in a separate file. Even a
  green `EdgeValid` is only one field of `Degree3AreaCertificate`; `SectorValid`,
  the strict total, and `Q0Degree3AreaInput` remain open, so no 1/7 class credit
  is available yet.

## Lane B

- The architecture is sound: `B13.paidIDs = B12.paidIDs ∪ Next1182.newIDs`,
  disjointness is proved by the split `b09HighIDs`/part-local `high_not_next`
  strategy, and `paid_count = 1997` follows by `card_union_of_disjoint`.
- `B13.remaining_of_b13` correctly transfers the remaining-radius premise back to
  B12. Current `B13Main` composes that transfer through
  `remaining_of_b12` into `C450ChainCompletionMain`; its statement is the useful
  conditional full-disk theorem with the smaller premise.
- The previous `B13Main` red was not a B13 mathematics failure: CI attributes it
  to the optional `EnergyTerminalResidualCensus` import (C02/C03 free-variable
  errors). Removing that import was the correct isolation. The literal-census
  module remains red and must stay outside the main chain.
- **Highest leverage:** wait for `41035092539`; require
  `EnergyTerminalBatchB13Main` exit 0 on `521ca436...` and an allowed axiom
  report. Then the supervisor should replace the root import
  `EnergyTerminalBatchB12Main` with `EnergyTerminalBatchB13Main` at
  `n11-work/lean/N11Formalization.lean:1961`. That is the actual 1997-credit
  switch; another proof module before the root import adds no mathematical value.
- Do not describe 389 residual IDs as kernel-proven yet. `B13` exposes
  `residualIDs` and proves its equivalence to `RemainingTerminalRadius`, but the
  389-cardinality theorem is in the red `EnergyTerminalResidualCensus`. The
  1997 payment is formal; the 389/2386 denominator still needs its census repair.
- The split high-exclusion proof is preferable to restoring a monolithic
  `decide +kernel`; preserve the 216 `Fin.ext_iff; omega` leaves and do not raise
  heartbeats. If the pending run is red, diagnose only `B13Main` first.

## Lane C

- The restored matrix framework is a sound generic consumer: it ties a scaled DBM
  refinement's terminal packets to the source node's strict radius inequality.
  `EnergyRefineN2341` supplies exact tree validity, root scaling, packet validity,
  and `new_radius` for node 2341. CI exit 0 at `34b14918` makes this genuine Lean
  evidence, including six kernel decisions.
- It still pays **zero** residual IDs because it defines a private `newIDs` and no
  B13 consumer imports it. This is green theorem inventory, not a moved count.
- **Highest leverage:** create one incremental consumer module, not another
  archive batch. Start `EnergyTerminalBatchB13Refine2341.lean` with
  `paidIDs := B13.paidIDs ∪ EnergyRefineN2341.newIDs`, prove the singleton
  disjointness (equivalently `2341 ∉ B13.paidIDs`), then
  `paid_count : paidIDs.card = 1998`, dispatch `paid_radius` to B13 or
  `EnergyRefineN2341.new_radius`, and prove a `remaining_of` transfer to
  `B13.RemainingTerminalRadius`. Only a CI-green consumer can reduce the open set.
- Use a bounded residual-membership proof for `2341`. Do not reintroduce
  `EnergyTerminalResidualCensus` into `B13Main`, and do not treat the red
  `FrozenCapResidualMembership` import as available until its census closure is
  repaired.
- After 2341 is consumed, restore one admissible archive candidate per module;
  next is 3040. Keep one payload and only its own bounded kernel sites per CI
  target. The 57 archive drafts as audited total 724 kernel decisions (the other
  56 consequently hold 718) and include 15 `maxHeartbeats 0` files: aggregate
  restoration is an OOM/correctness hazard, not progress.
- The seven public frozen-cap exclusions are negative conditional facts and do
  not discharge `RemainingTerminalRadius`; the existing row-cap and
  `FrozenCapPublicExcludedTree` work is still conditional/often red. Do not revive
  the 700-leaf row-cap family without a positive consumer.

## Risks

- **Count conflation:** 1997 paid, 389 residual, and 0/7 classes are different
  ledgers. B13's payment does not prove the residual census, and C's green node
  2341 does not pay it until integrated.
- **Pending-byte verdicts:** `41035092539` is in progress. `B13Main` and A's
  current suffix bytes have no completed matching verdict.
- **Dependency red mistaken for own proof failure:** A's suffix and
  `EndpointChecks` are red through `Bins`; read the first target-specific error.
- **False suffix credit:** witness 1489 versus interval start 1490 must be handled
  explicitly; reusing the existing wrapper would silently omit the peak node.
- **Resource blowups:** A's rational peak checks, C's giant packet literals and
  `decide +kernel` terms, and the red row-cap leaves are all OOM/timeout prone.
  Split leaves and preserve per-target limits; never raise heartbeats or admit
  `maxHeartbeats 0`.
- **Audit substitution:** exact Fraction/float-search/tree/hash reports and static
  closure audits are not kernel proofs. CI exit 0 plus the allowed axiom set is
  the only payment gate.
- **Root still conditional:** even after B13Main and the root import, the
  arbitrary-center full-disk theorem still depends on `SevenClassExclusions` and
  the remaining energy premise.
