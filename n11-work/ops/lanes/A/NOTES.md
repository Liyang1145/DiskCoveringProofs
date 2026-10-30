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
  SHA256 `d4cdee60b4133182ca0c4ccca631c94241675be4faaac24f72b7862fbd5dac91`.
  It replaces the line-95 `Nat.mod_lt`/`Nat.le_of_lt` mismatch by explicit
  `Nat.mod_lt` plus `omega`.
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

## 2026-10-30 (session 36) -- zero-witness and positive prefixes

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeShape.lean`
  `99070a805d9067dd1b8e8ba43139f82897a2f43a9057bb04286c45992865c2f9`.
- `n11-work/ops/lanes/A/TARGETS.txt` unchanged,
  `0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.
- No frozen module, C450 module, root file, lakefile, or toolchain was edited.

**Progress.** Added `edgeIncTo_of_witness_zero`, proving that a zero witness
has a one-point increasing prefix, and instantiated it for edges 12 and 13.
Added the generic exact-threshold wrapper
`edge_ratio_le_cosHiReal_of_prefix` and the generic derivative wrapper
`edgeHiReal_monotoneOn_of_ratio_le`. Instantiated the wrappers for edges 15
and 19 at node 389 and edge 20 at node 486, yielding
`edgeIncTo_fifteen`, `edgeIncTo_nineteen`, and `edgeIncTo_twenty`.

Together with the existing prefix at edge 14 and decreasing suffixes at edges
9/10/11, EdgeShape now drafts nine of the 42 shape facts:
`EdgeDecFrom {9,10,11}`; `EdgeIncTo {12,13,14,15,19,20}`.

**Checks (scope).** `python tools/project_status.py --check` passed before the
edit (index/manifest consistency only). `git diff --check` and the
forbidden-token scan over EdgeShape passed. A `Fraction` audit recomputed each
new witness margin `cosTQ(14,nodeQ) - edgeCoeff/(19/50)^2` from the checked-in
mu/edge table: edge 15 `+3.865203484613561e-4`, edge 19
`+3.864510963837937e-4`, edge 20 `+4.192797580133260e-4`. It also confirmed
the continuous cosine bridge fails at edges 16/17/18, with margins
`-3.356169768567508e-4`, `-4.252444397268349e-4`, and
`-3.372097746406843e-4`. This is exact rational table arithmetic, not Lean.

A tiny core Lean probe exited by timeout after 30 s and a Mathlib probe after
120 s, both without a Lean verdict. No project build was run locally. The
checked-in CI snapshot (`41027178023`) predates these changes and still shows
Bins/EndpointChecks/UpperReductionUnimodal/suffix targets red transitively;
EdgeShape has **no CI verdict**. All new facts are **drafted, CI pending**.

**Still unproved.** Kernel acceptance of Bins, downstream modules, and all new
EdgeShape declarations; 33 of 42 shape facts; the 21 peak checks are only
source-drafted pending kernel acceptance; nine sectors; strict total;
`Q0Degree3AreaInput`; seven exclusions; and the arbitrary-centre full-disk
theorem. No mathematical payment is claimed.

**Next concrete step.** Read the refreshed CI result in target order. If Bins
is red, fix only its first diagnostic. If Bins and EdgeShape are green, treat
edge 16 first with a discrete-cell argument: locate the unique cell where the
continuous edge bracket changes sign inside `[nodeQ 410, nodeQ 411]`, prove the
cell endpoint values ordered by exact rational arithmetic, and keep the other
40 cells under the monotone derivative bound. Do not reuse the continuous
cosine bridge for edges 16--18: its required witness-node inequality is false.

## 2026-10-30 (session 37) -- discrete peak steps for edges 16--18

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeShape.lean`
  `633c80a756a04e88826268f60aa53fb22dbf643830839d5a4947199fcb556a14`.
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3Bins.lean` unchanged from
  session 36, `d4cdee60b4133182ca0c4ccca631c94241675be4faaac24f72b7862fbd5dac91`.
- `TARGETS.txt` unchanged, `0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.

**Progress.** Added `edgeIncTo_of_monotoneOn_to_prev_and_step`: monotonicity
on `[0, node (w-1)]` plus one exact comparison `edgeUpper (w-1) <= edgeUpper w`
closes `EdgeIncTo i`. The cosine threshold bridge succeeds at the preceding
nodes 410, 405, 410 for edges 16, 17, 18 (although it fails at their peak
witnesses), so all three increasing-prefix obligations are now drafted.
EdgeShape stands at 12/42 shape facts: `EdgeDecFrom {9,10,11}` and
`EdgeIncTo {12,...,20}`.

**Checks (scope).** Exact `Fraction` arithmetic from the checked-in mu/edge
table gives preceding-node derivative margins `+8.198262e-5`, `+6.766350e-5`,
`+8.175262e-5`; it gives one-step peak increments `+2.574426e-8`,
`+4.835285e-9`, `+2.539145e-8`. `python3 tools/project_status.py --check`
passed (index/manifest consistency only). `git diff --check` and the
forbidden-token scan over EdgeShape passed. No local project build was run;
CI snapshot `41027178023` predates these bytes. All new declarations are
**drafted, CI pending**.

**Still unproved.** Kernel acceptance of all repaired/downstream modules and
the 12 drafted shape facts; 30 of 42 shape facts; nine sectors; strict total;
`Q0Degree3AreaInput`; seven exclusions; and the arbitrary-centre full-disk
theorem. No mathematical payment is claimed.

**Next concrete step.** Read refreshed CI in target order. If EdgeShape is
green, apply the same `prev + exact step` pattern with the appropriate local
monotonicity or derivative bound to edges 0--8's increasing prefixes and
their decreasing suffixes. If it is red, fix only the first reported
EdgeShape diagnostic before adding facts.

## 2026-10-30 (session 38) -- early increasing prefixes

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeShape.lean`
  `514e76a30ccdd0649c8877b2fb049a979ab5c735ab0a2caa71a45ba433912600`.
- `n11-work/ops/lanes/A/TARGETS.txt` unchanged,
  `0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.

**Progress.** Generalized `edge_ratio_le_cosHiReal_of_prefix` from a
`π/4` node bound to `π/2`, matching the actual domain of
`cosT14_antitoneOn`. Added exact threshold checks and monotone-prefix
closures for edges 0 (node 543), 1 (878), and 8 (878), giving
`edgeIncTo_zero`, `edgeIncTo_one`, and `edgeIncTo_eight`. EdgeShape now
drafts 15/42 shape facts: `EdgeDecFrom {9,10,11}` and
`EdgeIncTo {0,1,8,12,...,20}`.

**Checks (scope).** `python3 tools/project_status.py --check` passed
(index/manifest consistency only). `git diff --check` and the forbidden-token
scan passed. CI snapshot `41027178023` predates these bytes; CI
`41037794295` is pending. No local project build was run. All new declarations
are **drafted, CI pending**; the three exact ratio inequalities have not yet
received a kernel verdict.

**Still unproved.** The CI acceptance of the drafted shape facts and Bins;
27 of 42 shape facts; nine sectors; strict total; `Q0Degree3AreaInput`;
seven exclusions; and the arbitrary-centre full-disk theorem.

**Next concrete step.** On refresh, fix the first EdgeShape diagnostic if
CI is red. If green, handle edges 2--7: their peak nodes lie above `π/2`, so
prove a separate cosine-prefix bound there (or use discrete-cell/derivative
intervals) instead of reusing `cosT14_antitoneOn`; then attack decreasing
suffixes 0--8.

## 2026-10-30 (session 39) -- extended-domain prefixes 2--7

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeShape.lean`
  `e740b22c7a640b88b35c00efe2597f0f3d900d3f5e0a5c4d948f19a2d0eb4d79`.
- `TARGETS.txt` unchanged,
  `0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.

**Progress.** Proved the degree-28 Taylor cosine polynomial antitone on
`[0, 3π/4]` by the three already-established branches for nonnegative
`sinT 14`, and added the matching cosine-threshold/cosine-bridge wrappers.
Closed increasing prefixes for edges 2--7, at prior nodes 1111, 1063, 1072,
1072, 1063, 1111 and peaks 1112, 1064, 1073, 1073, 1064, 1112. The first
attempt used the peak nodes and the exact audit correctly rejected it: the
cosine thresholds are short by `5.57e-6` (edge 2), `5.18e-4` (edge 3),
`1.70e-4` (edge 4), `1.71e-4` (edge 5), `5.20e-4` (edge 6), and
`9.10e-6` (edge 7). The committed pattern is the prior-node/one-step form.
EdgeShape now drafts 21/42 shape facts: `EdgeDecFrom {9,10,11}` and
`EdgeIncTo {0,...,8,12,...,20}`.

**Checks (scope).** Exact `Fraction` arithmetic from the checked-in mu/edge
table gives prior-node cosine margins `1.514613e-3`, `1.013269e-3`,
`1.359952e-3`, `1.358359e-3`, `1.011607e-3`, `1.511081e-3` and exact
grid-step increments `1.671259e-7`, `5.486147e-8`, `1.318117e-7`,
`1.314589e-7`, `5.449331e-8`, `1.663436e-7` for edges 2--7. This is table
arithmetic, not Lean. `python3 tools/project_status.py --check` passed
(index/manifest consistency only); `git diff --check` and the forbidden-token
scan passed. A bounded `lake env lean` attempt terminated before elaboration
because the local Lake package checkout reported untracked Mathlib files; this
is **not** a Lean verdict. No project build was run. CI snapshot `41027178023`
predates these bytes. All new declarations are **drafted, CI pending**.

**Still unproved.** Kernel acceptance of Bins/downstream modules and the
drafted EdgeShape facts; 21 of 42 shape facts; 21 peak checks pending kernel
acceptance; nine sectors; strict total; `Q0Degree3AreaInput`; seven
exclusions; and the arbitrary-centre full-disk theorem.

**Next concrete step.** Read refreshed CI in target order and fix only the
first EdgeShape diagnostic if red. If green, add `cosHiReal` antitone on
`[0,3π/4]`, then close decreasing suffixes 0/1 from their next nodes
(544/879) with one exact step; close suffixes 2--7 from their witness nodes
using the negative coefficient threshold and the already-proved posterior
cosine tail.
