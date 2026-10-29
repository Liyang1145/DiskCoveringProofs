# Lane A notes

SUPERVISOR (2026-10-29 01:05 CST): STOP hardening `verify_chain_completion.py`.
C450 completion modules are frozen pending CI. Do not edit them unless CI
LATEST.md reports a Lean error there; then patch from the first error line.
Continue SevenClassExclusions, starting with q0 degree three (`Q0RunExclusion 1`).

## 2026-10-28 (part 4) — q0 degree-three grid-node feasibility probe

**Did.** Added `probe_q0_degree3_nodes.py`, an exact-rational probe of two
simplified node families for `Degree3AreaCertificate` using the source q0
multiplier midpoints, `U = piHi`, `N = 2048`, and the source `piLo`.
- Constant node `a = 2/5` is `NodeValid` at every grid node but its exact
  `totalUpper` is above `piLo`; therefore it cannot instantiate the strict field.
- Affine node `a = 192/1000 + q/16` gives an exact total below `piLo`, but fails
  `NodeValid` (the cheap upper `capQ q <= (19/50)*sinHiNLag(q/2)` exceeds
  `sinLoNLag a`, especially near `q = pi`).
This rules out these shortcuts and shows a piecewise/adaptive rational node
family is needed (or a genuine per-node arcsin enclosure).

**Checks (scope).** `timeout 120s python3 probe_q0_degree3_nodes.py`: PASS,
exact `Fraction` arithmetic on source multipliers/grid only; JSON regenerated.
`python3 -m py_compile`: exit 0. No Lean build or kernel check was run.

Hashes:
- `probe_q0_degree3_nodes.py`: `f4a63dfd8fe7ad408a7dfd2b879a5435886b2053293213f82a2ead440f2a4d7a`
- `q0-degree3-node-probe.json`: `9a7ca6dd3fbd89a9b9eb73ef95d2aa5b31ee24a9cde7e1f66f6009d4c9722ac5`

**Still unproved.** q0 degree three is unconditional only from the explicitly
uninhabited `Q0Degree3AreaInput`. No concrete `Degree3AreaCertificate` has been
kernel checked; no edge/sector maxima table module exists.

**Next concrete step.** Emit a piecewise-constant node family with four bins
(e.g. `[0,1/2]`, `[1/2,1]`, `[1,3/2]`, `[3/2,U]`) and rational values chosen
so `sinLoNLag a >= max capQ` on each bin; recompute exact edge/sector maxima and
the final total. If strict, emit the Lean table with bin-membership proofs, then
add its target for CI. Avoid `native_decide` and huge kernel `decide`s.

## 2026-10-28 — q0 degree-three reduction (drafted, CI pending)

**Did.** Added `SevenClassQ0Deg3.lean`: exact `Degree3AreaCertificate`, proof
`false_of_areaCertificate` by the existing rational area-dual consumer,
`q0_degree3_of_areaInput : Q0Degree3AreaInput -> Q0RunExclusion 1`, and the
unconditional unique 21-edge graph identity. Registered in TARGETS.txt.
The source q0 certificate has 11 rational mu intervals, lambda interval,
`upper < pi`, and graph with 21 edges / hub degrees 3 and 10.

Hashes:
- `SevenClassQ0Deg3.lean`: `48d41f5d3a71c41adc3ff0af26f86740b2f4ed82383a037d182aac0f16075b61`
- `SEVEN-CLASS-PLAN.md`: `6fe46e91214c51314df41742f1d5e6a1e790709b4c0e5ddcd3822b04e127a381`
- `TARGETS.txt`: `d9b85ba463267e28f121c21abfd980b9b8e2e68a442c17b884455b1f1c2b1964`
- `audit_q0_degree3_area.py`: `4553deb61f05bf1af61e67241bb0c3714d3b6e4b39ed6bc28c5889165a73104a`
- `q0-degree3-area-audit.json`: `bc3ec28e2594b338bcdf0baa78079590d35e1ace545c515681997ebc13076627`

**Checks.** `audit_q0_degree3_area.py` PASS (source interval/graph only);
`project_status.py --check` PASS (handoff declarations only); no Lean build.
`SevenClassQ0Deg3` remains DRAFTED, CI PENDING.

## 2026-10-28 — C450 completion modules (frozen, CI pending)

**Did.** Drafted `C450ChainCompletion.lean` and `C450ChainCompletionMain.lean`
via `emit_chain_completion.py`, assembling the 36 segments, 25 transfers, and
the telescope to the stage-1 residual interface. Static verifier checks the
36-segment data index, 25-transfer chain, telescope, direct import closure,
two-entry TARGETS order, determinism, forbidden tokens, and module byte hashes.
Do not edit these modules while CI is pending (supervisor freeze).

Module hashes:
- `C450ChainCompletion.lean`: `935dcd6a0078ad0216e8e195e092c033cf2be7b46deb0d22b7d7cbd05000f191`
- `C450ChainCompletionMain.lean`: `942dd90f69781a7ce1d57c5a393c3c11626cfe4135b30c5834fb2656ca3b6c03`
- `verify_chain_completion.py`: `a33579b0b398c677875910481a598d5542e6ccff6168e1ca16c8a56cdef50bc3`

**Checks.** `verify_chain_completion.py` PASS (static source/interface audit);
`emit_chain_completion.py --check` PASS; isolated Lean probes timed out and are
NOT evidence. Both modules remain DRAFTED, CI PENDING. `LATEST.md` currently
reports an incomplete/cancelled CI run, no successful build log.

**Next CI step.** Inspect lane-A targets. If green, ask supervisor to replace
the two `HARK-MISSING` imports at root `N11Formalization.lean:1952-1953` and run
a serial root build. If red, patch only from the first Lean error line.

## 2026-10-28 — q0(4,9) graph/layout audit

**Did.** `extract_finite_class_tables.py` reconstructs `q0Faces 2` as the
two-fan graph split at 2 and writes `q0-degree4-graph-match.json`; verifies the
11-face multiset, 21 canonical edges, 112 certificate coefficients, z-slot and
symbolic-atom group multiplicities, and factor layout/order.

Hashes:
- `extract_finite_class_tables.py`: `d636abc43b0011fcc5846c7375fda5bafa21a272466bc59eba4b60b922986891`
- `q0-degree4-graph-match.json`: `a2b52d4edbd2bbb20e3512e0d18cacca0e2878327f43b6871937b5515e93da02`

**Still unproved.** Source `z` values are nine-decimal approximations; no exact
rational lift, balance proof, multiplier proof, or factor-bound Lean module.
The atom-key/field bijection is not yet emitted.

## C450 / SevenClass history (condensed)

- `SEVEN-CLASS-PLAN.md` records the seven Q0/Q1 exclusions; all remain unpaid.
- `audit_q0_degree3_area.py` independently audits the source q0 interval table.
- `extract_finite_class_tables.py` audits q0(4,9) finite graph/layout only.
- C450 modules and verifier are static-audited but never kernel checked.
- `ROOT-IMPORT REQUEST` for C450Main after CI green; no root edit by lane A.

## 2026-10-29 — q0 degree-three feasible 8-bin node family

**Did.** Added `probe_q0_degree3_piecewise.py` and
`q0-degree3-piecewise-8.json`. The node is constant on eight equal q-bins with
exact rational values:

`239/1250, 239/1250, 133/625, 2721/10000, 643/2000, 897/2500, 191/500, 1949/5000`.

Each value is the least denominator-10000 rational selected by exact bisection
against `sinLoNLag a >= max capQ` on its bin. The manifest stores exact source
multiplier midpoints, bin endpoints/thresholds, 21 edge maxima with grid
witnesses, 9 sector maxima with grid witnesses, `totalUpper`, and the exact
positive slack. Exact result: all 2049 grid nodes are `NodeValid`, and
`totalUpper < RatInterval.piLo`; relative slack is approximately
`0.0038492865576 * piLo` (the exact fraction is in the JSON).

**Checks (scope).** `timeout 180s python3 probe_q0_degree3_piecewise.py`: PASS,
exact `Fraction` arithmetic over the source interval midpoints and N=2048 grid;
it asserts every node inequality, all maxima are attained on the grid, and the
final strict inequality. `python3 -m py_compile`: PASS. This is a candidate-data
audit only; no Lean elaboration, kernel check, or CI claim.

Hashes:
- `probe_q0_degree3_piecewise.py`: `262fd25a50fd1d3e06e7eda2dde08ff69ae0944e885e8dc418d8a1ec710bd036`
- `q0-degree3-piecewise-8.json`: `22e49d9dc6962602100f47668ebaaf3d7b3defd3fc126567fbdd7b9084cb6996`
- source `degree3_area_certificate.json`: `fe73e1f3e78b7041d563de4fde94b235226ab460210949f59888fb623d89ceb2`

**Still unproved.** No Lean module yet defines this node or proves
`Degree3AreaCertificate`; `Q0Degree3AreaInput` remains uninhabited. The maxima
are exact rational grid witnesses, but their all-node bounds and the bin
`NodeValid` implications still need Lean proofs. Existing C450 modules remain
frozen/CI-pending per supervisor instruction.

**Next concrete step.** Emit a table module for the eight constants and prove
`NodeValid` per bin using rational threshold comparison plus `capQ`
monotonicity. Then split each of the 21 edge and 9 sector all-node bounds into
small monotone subintervals (avoid any 2049-literal `decide`), instantiate
`Degree3AreaCertificate`, and add only the resulting new module to
`TARGETS.txt` for CI.

## 2026-10-29 (part 2) — q0 deg3: per-bin endpoint reduction checked

**Did.** Added `probe_q0_degree3_binmax.py` (exact `Fraction`). It partitions all
2049 grid nodes into the eight existing bins (no overlap, full coverage), checks
for each bin that `capQ` attains its grid maximum exactly at the bin's last node
(`kHi`, whose q equals the exact bin `qHi`), and records the exact positive
`sinLoNLag a - capQ(qHi)` margin. Thus the `NodeValid` obligation over
`Fin 2049` reduces to 8 endpoint comparisons *provided* `capQ` is monotone on
each bin (that monotonicity is NOT checked and remains to be proved in Lean).
Minimum exact margin (all positive; exact fraction in JSON):
`277922260153149832458652959035620408410554828194697398625334509669382088268179002957611323326117355433047119206676837749851 / 81128399449723602539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000`.

**Checks (scope).** `timeout 120s python3 probe_q0_degree3_binmax.py`: PASS,
exact rational arithmetic over the source interval midpoints and the N=2048
grid; covers all 2049 nodes; asserts positive margin per bin. No Lean
elaboration/build/kernel check; `q0-degree3-binmax.json` is a data audit only.

Hashes:
- `probe_q0_degree3_binmax.py`: `bc4efb69f3a15fda546e01af1353dd1ca03db77e039e4688eebd6eb8c173b872`
- `q0-degree3-binmax.json`: `f582c26c9e0688526078881f12ce2b3be54231b595a3d6eda54fd8c86a82add0`

**Still unproved.** No Lean module defines `nodeBin`/proves `NodeValid`;
`Q0Degree3AreaInput` remains uninhabited; `capQ` monotonicity on bins unproved;
the 21 edge / 9 sector all-node maxima unproved in Lean. C450 modules remain
frozen/CI-pending (LATEST.md still shows no successful lane-A build).

**Next concrete step.** Emit `SevenClassQ0Deg3Bins.lean`: define `nodeBin :
Fin 2049 → ℚ` from the 8 constants and prove `∀ k, NodeValid (nodeQ piHi 2048 k)
(nodeBin k)` via 8 endpoint comparisons plus a `capQ` monotonicity lemma (find
`sinHiNLag` monotone lemmas in `IntervalsHighLag`/`Interval/Trig`; fall back to
splitting each bin into monotone subintervals). Add only that new module to
TARGETS.txt; do not touch the frozen C450 files.

Lead for next step: `grep sinHiNLag.*mono` found no direct monotonicity lemma;
only `IntervalsHighLag.lean:172` uses `Real.monotoneOn_sin`. Expect to prove
`capQ` monotonicity from `sinHiNLag_le_sin`/`sin_le_sinHiNLag` and
`Real.monotoneOn_sin` on `[0, piHi/2]`, or subdivide bins further.

## 2026-10-29 (part 3) — q0 deg3 eight-bin Lean reduction drafted

**Did.** Added `SevenClassQ0Deg3Bins.lean`, defining `binIndex`, `binHi`,
`nodeBinAt`, `nodeBin` and proving `nodeBinAt_mem`. The theorem
`node_valid_of_grid_cap` reduces all 2049 `NodeValid` obligations to two named
unpaid premises: `CapMonotoneOnGrid` (grid cap at `k` ≤ cap at its bin endpoint)
and `EndpointValid` (the eight exact endpoint comparisons). Added only this new
module to lane-A `TARGETS.txt`; frozen C450 modules untouched.

Also tested the alternative small-`Fin` kernel route in mathlib-probe with the
same rational definitions: `decide +kernel` over 8 nodes did not finish within
90 s, and `norm_num` on one node did not finish within 60 s. Scope: isolated
Mathlib probe, no project imports/build; these are engineering negatives, not
proofs.

Hashes:
- `SevenClassQ0Deg3Bins.lean`: `71c27a8d1083f66d861facd3f112fbe499c820ba7aeb5f0b63d6dd69c8f170f8`
- `TARGETS.txt`: `713fd7cf247684cc81dfc762e0bbe7d731a7f376db6916bba2980eaf23064270`

**Checks (scope).** No local Lean project build was run (per weak-host rule).
CI pending for all four lane-A targets listed in `TARGETS.txt`. Python audits
from part 2 remain PASS, exact rational data only.

**Still unproved.** Both `CapMonotoneOnGrid` and `EndpointValid` are uninhabited.
`Q0Degree3AreaInput` remains uninhabited; the 21 edge/9 sector maxima and strict
total still need Lean proofs. No axiom claim is made for the new module.

**Next concrete step.** Prove the eight `EndpointValid` conjunctions by
`norm_num [EndpointValid,binHi,nodeBinAt,capQ,nodeQ,sinLoNLag,sinHiNLag,sinTQ]`
if tractable on CI; otherwise emit denominator-cleared polynomial endpoint
lemmas. Then attack `CapMonotoneOnGrid` via `Real.monotoneOn_sin` and Taylor
remainders, splitting bins if needed.

## 2026-10-29 (part 4) — endpoint obligations separated; probe blocked

**Did.** Split the eight-conjunction endpoint target into a named
`EndpointCheck (j : Fin 8)` plus `endpointValid_of_eight`, so each rational
Taylor endpoint comparison is an independent Lean goal. This is a structural
reduction only; none of the eight checks has been proved.

Attempted an isolated one-endpoint probe of `19/100 ≤ sinLoNLag (239/1250)`
with copied `sinLoNLag`/`sinTQ` definitions. The sandbox Mathlib-probe has no
built `Mathlib.olean` (`unknown module prefix 'Mathlib'`), so this probe
produced no mathematical evidence. Do not count the prior 60/90 s probe
negatives as current evidence either until the probe cache is inspected.

**Checks (scope).** `python3 tools/project_status.py --check`: exits 0,
handoff status only. No Lean build/elaboration/kernel check for the edited
module. CI remains pending.

Hash:
- `SevenClassQ0Deg3Bins.lean`: `ce88107a561a1ab57de9d7715200ff3aa723c264b9da6a392169e56c25f11a55`

**Still unproved.** All eight `EndpointCheck` goals, `CapMonotoneOnGrid`,
the edge/sector maxima, strict total, and inhabitation of
`Q0Degree3AreaInput`. C450 remains frozen/CI-pending.

**Next concrete step.** Inspect `/workspace/tools/mathlib-probe/.lake` to
restore a usable probe (or compile only `Mathlib.Data.Rat.Defs`), then test
endpoint 0. Prefer a coarse rational chain: bound `capQ` by
`(19/50)*max (1/2) (q/2)` and compare against a low-degree Taylor lower bound,
rather than expanding the full 29th-degree `sinTQ 14` expression.
