EXPERT (2026-10-30):
- CI now reaches `EndpointChecks`; it is the sole real blocker, while all later lane-A exits are dependency-only.
- Split it now: `EndpointChecksTaylor` (generic Taylor/monotonicity), `EndpointChecksBins` (eight scalar bin lemmas), then assembly.
- First theorem: `sinT4_eq_quartic (a : ℝ) : sinT 4 a = a - a^3/6 + a^5/120 - a^7/5040`; use `simp [sinT, Finset.sum_range_succ]` then `ring_nf`.
- Replace repeated `![...] j` lookups with scalar `endpointU0..7 : ℚ`; close rational branches by `simp only [endpointUj, sinPoly4]; norm_num`.
- For `hj.val < 5` false branches use `norm_num at hj` before `omega`; do not leave bare `omega` after `fin_cases`.
- Build in order: EndpointChecks -> UpperReductionUnimodal -> both suffix modules -> EdgeShape; then prove `SectorValid` and instantiate `Q0Degree3AreaInput`.
- `edgeValid` or 42 drafted facts alone are not a class exclusion; `SevenClassExclusions` remains 0/7.

# Lane A notes

## Ledger

- C450 is closed at `495c970c`, CI-green, and transitively imported through
  `EnergyTerminalBatchB12Main`; stale `HARK-MISSING` comments are not a gap.
- Cos and Mono were CI-green at `e5875cf8`.
- Bins source repair is **drafted, CI pending**:
  `n11-work/lean/N11Formalization/SevenClassQ0Deg3Bins.lean`
  SHA256 `a3d8f972205f52d664ecb69073704de6d34bf1a5e15816d9a8ffc8f9f2e25326`.
  It replaces the line-95 `Nat.mod_lt` call with the pinned-API form
  `Nat.mod_lt k.val (by norm_num : 0 < 256)` plus `omega`, matching existing
  uses in `SourceLoop.lean`.
- EndpointChecks restricts lower Taylor premises to bins 0--4 and handles bins
  5--7 separately. Exact endpoint audit passed 8/8; minimum slack was
  `6.6940497252e-7` (bin 7).
- UpperReductionUnimodal has 21 exact peak checks and the single-peak
  factorization. Shape facts remain explicit and are not all paid.
- Seven-class exclusions: 0/7 paid. No kernel-green all-node degree-three
  certificate exists.

## 2026-10-30 (sessions 24--35, condensed)

Cos/Mono were CI-green at `e5875cf8`. Bins was repaired first to use
`Nat.mod_lt ... (y := 256)`, then the line-95 type mismatch above. Exact
edge-9/10 tails were developed with the correct threshold
`cosHiReal <= edgeCoeff/(19/50)^2`; a global `cosHiReal <= 0` shortcut was
rejected. The narrow tail uses `-131/200` at node 1490, then `-2/3` above
`3*pi/4`. Edge 11 uses node 1118, `-103/720`, and the same `-2/3` tail.
Edge 14's positive prefix uses `cosT14_antitoneOn`, an exact node-486 Taylor
check, and a real-to-grid monotonicity wrapper. The old audit script
`audit_q0_degree3_narrow_cos.py` and its JSON report remain exact-rational
arithmetic evidence, not Lean evidence.

## 2026-10-30 (sessions 36--39, condensed)

EdgeShape acquired zero-witness prefixes, generic cosine-threshold/derivative
wrappers, prior-node/one-step prefix closures, and cosine antitonicity through
`3π/4`. Exact `Fraction` audits selected all prior nodes and rejected peak-node
reuse at edges 2--7 and 16--18 by small negative margins. Entering session 41:
21/42 shape facts drafted, `EdgeDecFrom {9,10,11}`, and
`EdgeIncTo {0,...,8,12,...,20}`. No local Lean verdict; all CI pending.
## 2026-10-30 (session 40) -- Bins API repair

Replaced the line-95 `Nat.mod_lt` application with
`Nat.mod_lt k.val (by norm_num : 0 < 256)`, matching `SourceLoop.lean`.
Bins later kernel-passed in run `41050329106`; no earlier local Lean verdict
was available.

## 2026-10-30 (session 41, condensed)

Session 41 proved cosine antitonicity through `3π/4`, closed the 16 decreasing
EdgeShape suffixes `edgeDecFrom_{0,...,8,14,...,20}`, and drafted 37/42 shape
facts. Exact `Fraction` node selection passed; smallest crossing margin was
`-0.0008342` (edge 0, node 544). Only `EdgeIncTo {9,10,11}` remained, but all
results were **drafted, CI pending**; the probe timeout was not a Lean verdict.
EdgeShape hash then: `12869a2a...6ea`.

## 2026-10-30 (sessions 42--47, condensed)

- Drafted all 42 EdgeShape facts and `edgeValid`; assembled EndpointChecks,
  endpoint Taylor bounds, 21 UpperReduction peak checks, and both suffix modules.
- Repair chain for stale CI reds: Bins API `Nat.mod_lt`; EndpointChecks
  `div_le_div_iff`, sine-remainder sign, explicit power derivative, finite-branch
  tactic selection, literal endpoint-table reduction, and cast/ring plumbing.
- Session 47 read run `41065332260`: `ring` did not unfold `sinT 4`; `hmain`
  retained opaque `↑(sinPoly4 a)`; `convert ... <;> ring` stalled; `norm_num`
  committed before `omega`; and vector indices such as `![...] 5` survived.
  Repairs were `norm_num [sinT, Finset.sum_range_succ]`, `unfold sinPoly4`,
  a named derivative equality, `omega`-first branches, and eight literal
  `[simp]` table facts. EndpointChecks hash became `ff880fc9...aa65dc`.
- Exact endpoint audits passed independently; no declaration was kernel-paid.

## 2026-10-30 (session 48) -- current-run diagnostics mapped; draft unchanged

**Files / SHA256.** EndpointChecks remains
`ff880fc9f255a06305ff0980686d9d1e3f3c21c68adcbddb6a7ad45a00aa65dc`;
`TARGETS.txt` remains
`0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.
No new source edit: the public artifact for completed run `41065332260` tested
the pre-repair `ede0d1c8` file, not this hash.

**Progress.** Downloaded the public run artifact and full Actions log through
the GitHub API. Extracted all 18 EndpointChecks diagnostics (lines 76, 105,
128, 222, 234, 255, 257, 260, 271, 273, 276, 300, 305, 310, 317, 327, 341).
They reduce to five clusters: sine `sinT 4` normalization; casted `sinPoly4`
in `hmain`; derivative `ring_nf`; `False` branches for `j = 5..7`; and
vector-indexed endpoint values. The session-47 draft addresses every cluster.
The artifact is evidence for the repair mapping, not a verdict on current bytes.

**Checks (scope).** `verify_q0_degree3_endpoint_polynomial.py`: PASS 8/8,
minimum slack `1813339696040923404218003961318003972770323 /
52701008282540452209375000000000000000000000000`.
`audit_endpoint_low_denom.py`: PASS 8/8, bin-7 slack `6.6940497252e-7`.
`git diff --check` and the forbidden-token scan passed. A bounded local
Mathlib probe timed out without a verdict. No local project build was run.

**Still unproved.** Kernel acceptance of EndpointChecks with hash `ff880fc9`;
then UpperReductionUnimodal, suffixes, EdgeShape/`edgeValid`, nine sectors,
strict total, `Q0Degree3AreaInput`, seven exclusions, and the
arbitrary-centre full-disk theorem.

**Next concrete step.** After supervisor commit/push, read the first completed
run at or after current HEAD. Quote its first EndpointChecks diagnostic; fix
only that site before advancing in `TARGETS.txt`.

## 2026-10-30 (session 49) -- C450 endpoint non-vacuity audit

**Did.** Re-audited the green C450 telescope against the handoff warning that an
empty `drop 36` base must not be mistaken for payment of segment 36.  Confirmed
`C450Source36Segment.source35_remaining_of_remaining` explicitly inserts
`source36_paid`; the empty base is therefore the correct endpoint.  Added
`C450ChainCompletionAudit.lean`, which proves that `source36` is a member of
`C450Source11Segment.remainingSegs`, recovers
`SegmentNormalized source36` directly from `h450`, and proves the consumed tail
is nonempty.  Added the module to `TARGETS.txt`.

**Files / SHA256.** `C450ChainCompletionAudit.lean`
`e6306c1f22d5879a03cb8cea70582d88330a3102edd1251c89ce79761238b488`;
`TARGETS.txt` `39d32d75080cbd329a3068f8d3b3beaa40f899c3f1c7665b6a71fb2e8d27cc03`.
The pre-existing `C450ChainCompletionMain.lean` is unchanged at
`3f6088615e0a88e2a8927562c947c0c685e3e57bb15376ca3467fc7f6a33539c`.

**Checks (scope).** `git diff --check` passed and the forbidden-token scan of
the new module found none.  A Mathlib-only probe of the `change`/kernel/empty-list
tactic pattern timed out without a verdict.  The audit is **CI-pending**: no
local project build ran.
`EnergyTerminalBatchB12Main` already imports `C450ChainCompletionMain`, so the
stale root comments at lines 1952--1953 are not evidence of a missing consumer.
The audit module itself is not requested for root import.

**Still unproved / unpaid.** Kernel acceptance of the new audit; separately,
the red `EndpointChecks` chain and all seven-class obligations remain unpaid.
C450's mathematical chain is already CI-green only through its previously
checked hashes; this session's audit confirms the final-segment plumbing.

**Next concrete step.** Read CI for `C450ChainCompletionAudit` after supervisor
push.  If green, record C450 as fully audited; if red, quote and repair only its
first diagnostic without touching the new Fen/`h450` chain.

## 2026-10-30 (session 50) -- audit hardening + CI state

**Did.** `ops/ci/LATEST.md` has newest completed run `41059074494` (success
at `96ed4912`); `41065332260` is still in progress.  `C450ChainCompletionAudit`
is still untracked in this worktree, so no CI run has tested it.  Static review
confirmed `C450Source11Segment.remainingSegs` is `def ... := c450Segs.drop 11`
(line 367), so the audit's `change` is definitionally valid.  Replaced the
uncertain `exact List.not_mem_nil hmem` with the robust `cases hmem`.

**Files / SHA256.** `C450ChainCompletionAudit.lean` now
`ea77c2ee45437f4885b0d8061a7c7794fc439d5a87f7d3ce2e505d94fe1a015e`
(was `e6306c1f...`).  `TARGETS.txt` unchanged at `39d32d75...cc03`;
`EndpointChecks` unchanged at `ff880fc9...aa65dc`; `NOTES.md`/`TARGETS.txt` are modified
locally, not committed.

**Checks (scope).** Forbidden-token scan of the patched audit: clean.
Mathlib probes of `norm_num [sinT, Finset.sum_range_succ]` timed out at 150 s
(full import) and 100 s (narrow import); a bare `#check` probe gave no output.
These are sandbox timeouts, **not** Lean verdicts.  Manual sign audit of
`sinPoly4_le_sinTQ14`: after unfolding, the difference is
`(a^9/9! - a^11/11!) + ... + (a^25/25! - a^27/27!)`, each pair nonnegative by
`sinTaylorPair_le` with `n = 9,13,17,21,25`, so the post-`norm_num`
`linarith` is mathematically the right closing step.

**Still unproved.** No kernel verdict on the audit or on the repaired
EndpointChecks; UpperReductionUnimodal, both suffix modules, EdgeShape/
`edgeValid`, seven sectors, strict total, `Q0Degree3AreaInput`, and the seven
exclusions all remain unpaid at this hash.

**Next concrete step.** Read the first CI run at or after the supervisor commit
containing `ea77c2ee` and `ff880fc9`; quote the first diagnostic of
`C450ChainCompletionAudit` or `EndpointChecks` and repair only that site.

## 2026-10-30 (session 51) -- completed-run provenance checked

**Did.** Queried the GitHub Actions API directly because `ops/ci/LATEST.md` was
stale. Run `41065332260` completed `success` at 14:15:52Z on `ede0d1c8`, but
that artifact predates the repaired EndpointChecks bytes. Its EndpointChecks
entry is therefore stale evidence, not a verdict on `ff880fc9`.

Supervisor commit `79e52a68` touched only `ops/PROGRESS.md` and
`ops/ci/LATEST.md`. Its two runs are `41072186791` (workflow "Scoped
mathematical replay", success) and `41072186884` (workflow "Delivery bytes, not
mathematical proof", failure). Neither is a lane-A Lean build verdict. The
supervisor's `n11-lean-build` for the current lane-A bytes has not run because
the audit is untracked and the two repaired files are uncommitted.

**Files / SHA256.** No source edit this session. EndpointChecks remains
`ff880fc9f255a06305ff0980686d9d1e3f3c21c68adcbddb6a7ad45a00aa65dc`;
audit remains `ea77c2ee45437f4885b0d8061a7c7794fc439d5a87f7d3ce2e505d94fe1a015e`;
TARGETS remains `39d32d75080cbd329a3068f8d3b3beaa40f899c3f1c7665b6a71fb2e8d27cc03`.

**Checks (scope).** Confirmed HEAD and remote branch at `79e52a68`; confirmed the
new commit contains no lane-A Lean changes. `git diff --check` and the
forbidden-token scan over the audit and EndpointChecks pass. Current Git status
shows the two modified lane-A files and untracked audit. No local project or full
Lean build was run.

**Still unproved.** Kernel acceptance of the audit and repaired EndpointChecks;
then UpperReductionUnimodal, suffix modules, EdgeShape/`edgeValid`, seven
sectors, strict total, `Q0Degree3AreaInput`, seven exclusions, and the
arbitrary-centre full-disk theorem.

**Next concrete step.** After the supervisor commits this worktree, find the
new `n11-lean-build` run at or after that commit, quote its first diagnostic for
`C450ChainCompletionAudit` (TARGETS order), and repair only that line.
