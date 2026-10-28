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
