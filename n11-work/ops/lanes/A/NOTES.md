EXPERT (2026-10-30):
- Do not add suffix theory until Bins exits 0; current red is dependency-level,
  not a verdict on the repaired source.
- If Bins is red, fix only its first diagnostic; then build EndpointChecks,
  UpperReductionUnimodal, both suffix modules, and EdgeShape in order.
- The useful continuous-prefix bridge is an exact cosine lower bound at the
  witness node followed by antitone `cosT 14` on the prefix.
- Edges 15/19 (node 389) and 20 (node 486) pass that bridge exactly; edges
  16/17/18 do not, so do not repeat the same pattern for them.
- SevenClassExclusions remains 0/7 until sectors, strict total, and
  `Q0Degree3AreaInput`.

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

## 2026-10-30 (session 42) -- all 42 shape facts and endpoint assembled

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeShape.lean`
  `fb48cf172b955c46aab2a969f2f29ee670da4456ff73f17620512da5a99260de`.
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3Bins.lean` unchanged,
  `a3d8f972205f52d664ecb69073704de6d34bf1a5e15816d9a8ffc8f9f2e25326`.
- `TARGETS.txt` unchanged,
  `0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.

**Progress.** Closed the final increasing prefixes with the existing
prefix-plus-one-grid-step wrapper: edges 9/10 use predecessor 1488 and edge 11
uses predecessor 1117. Added `edgeIncTo_{nine,ten,eleven}`, then assembled
`edgeMonotone : EdgeMonotone`, `edgeUnimodal : EdgeUnimodal`, and
`edgeValid : EdgeValid`; edges 12/13 use the existing qualified decreasing
facts from `SevenClassQ0Deg3EdgeSuffixHigh`. All 42 individual shape facts are
now drafted.

**Checks (scope).** Exact `Fraction` arithmetic emulating `cosTQ` verified
`cosTQ 14 (nodeQ ... prev) > edgeCoeff i / (19/50)^2` at (9,1488), (10,1488),
and (11,1117); the corresponding one-step `edgeUpper` inequalities are encoded
as separate `norm_num` goals. `git diff --check` and the forbidden-token scan
passed. `python3 tools/project_status.py --check` previously passed (index /
manifest consistency only). No local Lean/project build was run. The refreshed
public `ci/LATEST.md` still reports stale run `41037794295`; newer CI runs are
pending, so every new statement is **drafted, CI pending**, not paid.

**Still unproved.** Kernel acceptance of Bins, all downstream targets, the 42
shape facts, and `edgeValid`; nine sectors; strict total;
`Q0Degree3AreaInput`; seven exclusions; and the arbitrary-centre full-disk
theorem.

**Next concrete step.** Read the first refreshed CI diagnostic in target order.
If Bins or EdgeShape is red, fix only that first error; if both are green,
begin the nine-sector assembly feeding `SevenClassExclusions`.

## 2026-10-30 (session 43, continuation) -- CI refresh and Bins API audit

**Files / SHA256.** No source change beyond session 42:
`SevenClassQ0Deg3Bins.lean`
`a3d8f972205f52d664ecb69073704de6d34bf1a5e15816d9a8ffc8f9f2e25326`;
`SevenClassQ0Deg3EdgeShape.lean`
`fb48cf172b955c46aab2a969f2f29ee670da4456ff73f17620512da5a99260de`;
`TARGETS.txt`
`0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.

**Progress.** Re-read guidance, lane assignment, CI snapshot, and prior notes.
The public `ci/LATEST.md` is stale: its newest rows are run `41050329106`
(pending, `d70898ab`) and `41050208198` (in progress, `18c6e03b`), while its
detailed report remains run `41037794295`. The only quoted lane-A red in that
old report is `SevenClassQ0Deg3Bins.lean:95:23`; the local repaired line is the
known project pattern `Nat.mod_lt k.val (by norm_num : 0 < 256)`, as used by
`SourceLoop.lean`. No conclusion is drawn for the pending runs.

**Checks (scope).** `git log` confirms current HEAD `e2d2cab4` includes the
supervisor merge cycle; source hashes above were recomputed. A Mathlib-family
probe for the `mod_lt` goal and a bare pinned-Lean `#check` both hit bounded
timeouts before producing output, so neither is a Lean verdict. No project
build was run.

**Still unproved.** Kernel acceptance of Bins, EndpointChecks,
UpperReductionUnimodal, both suffix modules, EdgeShape and `edgeValid`; all
nine sectors; strict total; `Q0Degree3AreaInput`; seven exclusions; and the
arbitrary-centre full-disk theorem. Everything new remains **drafted, CI
pending**.

**Next concrete step.** Consume the completed result of run `41050329106` (or
the first newer completed `n11/work` run). Quote its first lane-A diagnostic
in target order; if Bins is green, proceed to EndpointChecks, otherwise fix
only that first error before touching downstream modules.

## 2026-10-30 (session 44) -- CI consumed; first EndpointChecks red repaired

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EndpointChecks.lean`
  `a52b222ca8bc12167943db42c4784ca478c23147bf89c25221d64867e35154e7`.
- Bins unchanged and now CI-green:
  `a3d8f972205f52d664ecb69073704de6d34bf1a5e15816d9a8ffc8f9f2e25326`.
- EdgeShape unchanged, CI-red:
  `fb48cf172b955c46aab2a969f2f29ee670da4456ff73f17620512da5a99260de`.

**Progress.** GitHub Actions run `41050329106` completed **success** at
`d70898ab`, updated 2026-10-30T12:42:05Z. Its job log shows exit 0 for
`C450ChainCompletionMain`, `Cos`, `Mono`, `Bins`; Bins is therefore CI-green.
The first new lane-A red is `EndpointChecks` exit 1. Its first diagnostic was
`SevenClassQ0Deg3EndpointChecks.lean:32:10: Unknown identifier div_le_div_iff`.
Replaced that obsolete rewrite and its multiplication proof with
`div_le_div_of_nonneg_left` and the cast factorial comparison. The module still
has later independent diagnostics at lines 78, 101, 107, 123, 130--131,
189, 215--216, 231--232, 248, 260, 292, 297, 302, 309, 319, 333; these are
drafted source fixes pending, not paid. `UpperReductionUnimodal`,
`EdgeSuffixNonpos`, `EdgeSuffixHigh`, and `EdgeShape` also exited 1, but those
were dependency failures of red EndpointChecks and are not independent verdicts.

**Checks (scope).** Queried the public Actions API and parsed the complete job
log (not inferred from stale `ci/LATEST.md`). `git diff --check` passed for the
edited EndpointChecks file; forbidden-token scan found none. No local Lean or
project build was run, so the new rewrite is **CI pending** and not a Lean
verdict. The CI success of `C450ChainCompletionMain` and `Bins` is kernel scope.

**Still unproved.** Kernel acceptance of the EndpointChecks repair and all later
targets; the downstream draft declarations in EndpointChecks/UpperReduction/
EdgeShape; nine sectors; strict total; `Q0Degree3AreaInput`; seven exclusions;
and the arbitrary-centre full-disk theorem. No mathematical payment is claimed.

**Next concrete step.** Rerun lane-A CI in target order. If line 32 is green,
quote the first remaining EndpointChecks diagnostic at line 78 and fix only that
goal before touching later lines.

## 2026-10-30 (session 45) -- EndpointChecks proof-plumbing repair

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EndpointChecks.lean`
  `53daf90db8328eeca312bb6d084d66dbb44d818eb68bd13a13e55ccce06c53fa`
  (**drafted, CI pending**).
- Bins `a3d8f972...e25326` is CI-green; EdgeShape `fb48cf17...260de` and
  `TARGETS.txt` `0e01498...ac1f2` are unchanged.

**Progress.** Retrieved and parsed the full run-`41050329106` job log. Beyond
the already repaired `div_le_div_iff`, fixed the line-67 sine-remainder sign
(`.2` to `.1`), replaced the unsupported `fun_prop` derivative proof by
explicit `hasDerivAt_pow`, removed obsolete explicit exponents from
`pow_le_one₀`, normalized addition order before `max_le_max_left`, moved the
`nodeQ`/endpoint helper facts before their uses, and strengthened the finite
rational `norm_num` closers. The later identical diagnostics in that log are
from the pre-repair source.

**Checks (scope).** Exact `Fraction` re-audit
`verify_q0_degree3_endpoint_polynomial.py` passed 8/8; minimum slack is
`1813339696040923404218003961318003972770323 / 52701008282540452209375000000000000000000000000`
(about `3.44e-5` in decimal, display only). `git diff --check` and the
forbidden-token scan passed. A bounded Mathlib probe timed out without output;
no local Lean/project build verdict. Latest lane-A CI run `41059074494` is
still in progress, so none of these repairs is paid.

**Still unproved.** Kernel acceptance of EndpointChecks and every downstream
target; all 42 EdgeShape facts and `edgeValid`; nine sectors; strict total;
`Q0Degree3AreaInput`; seven exclusions; arbitrary-centre full-disk theorem.

**Next concrete step.** When run `41059074494` completes, quote its first
EndpointChecks diagnostic; if EndpointChecks is green, advance to
UpperReductionUnimodal in target order.

## 2026-10-30 (session 46) -- Taylor API/finite-branch repairs

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EndpointChecks.lean`
  `5b033ddf218f267fda0f17f2b9cc7bcdef7eb3a87d560ad8909d03c3de15cf77`
  (**drafted, CI pending**).
- New bounded probe `n11-work/ops/lanes/A/probe_endpoint_taylor_api.lean`
  `9e0be8e902bdcc50066fad7b2e70318b5f8cf0f9a34fc573984493bcfca0fc37`.
  `TARGETS.txt` unchanged.

**Progress.** Run `41059074494` is still in progress at head `96ed4912`, which
predates the lane-A edits; its EndpointChecks diagnostics therefore do not test
this source. Fixed `sinTaylorPair_le` to supply the positive denominator before
`factorial_le` to `div_le_div_of_nonneg_left`. Replaced both
`... at hj ⊢` finite proofs (`endpointUBin_le_one_of_lt5`,
`nodeQ_binHi_le_two_of_lt5`) with `first | norm_num ... | omega`, avoiding the
recorded "No goals to be solved" failures when `hj` is contradictory.

**Checks (scope).** Exact `Fraction` audits passed: endpoint polynomial 8/8
(minimum slack `1813339696040923404218003961318003972770323 /
52701008282540452209375000000000000000000000000`), and low-denominator caps
8/8 with bin-7 slack `6.6940497252e-7`. `git diff --check`, the forbidden-token
scan, and `project_status.py --check` passed. A Mathlib probe was stopped after
120 s with no output; it is **not** a Lean verdict. No project build was run.

**Still unproved.** All new EndpointChecks declarations are kernel-unpaid; then
UpperReductionUnimodal, suffixes, EdgeShape/`edgeValid`, nine sectors, strict
total, `Q0Degree3AreaInput`, seven exclusions, and the arbitrary-centre theorem.

**Next concrete step.** Consume the first completed run containing this file.
Quote its first EndpointChecks diagnostic; fix only that site before advancing.
