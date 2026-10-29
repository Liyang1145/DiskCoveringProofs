# Lane C notes

## Standing guidance

- SUPERVISOR (2026-10-29 12:20 CST): CI cancelled; stop polling Actions.
  TARGETS stay `FrozenCapRationalCore`, `PaidCellCertificateM`,
  `PaidCellCertificateMCap`; do not target `FrozenCapCertificates` until the
  core is green.
- EXPERT: M/MCap are sound but pay no energy count. The seven `excluded_*`
  theorems remain conditional without `hnode : p.nodeID = <id>` and proved
  `row_cap_<id>` lemmas. Test one id locally first; then bridge
  `FrozenCapCertificates` to the rational core. Do not claim class/energy credit
  while 382 public residual records remain absent.

## Condensed history through 2026-10-29 part 18

- `PaidCellCertificateM` generalizes the 16-field packet to arbitrary DBM-row
  count; `PaidCellCertificateMCap` proves weighted reduced-cost transport and
  `not_valid_of_frozen_cap` exactly. Both remain **CI pending**; neither reduces
  the energy count.
- `recompute_next512_formulas.py` checks 512 public records exactly: 505 pass and
  seven fail (`1409,2337,2341,2356,2360,2368,2370`). Extra DBM rows do not
  rescue them. `certify_next512_row_cap.py` proves all 100 ordered-pair caps for
  an arbitrary row count, tightest Python slack `7.388363154221271e-7` at 2356.
- `build_residual389_census.py` reconstructs 389 residual IDs, but only seven
  have public `g/f0Lo/weights`; 382 HOST records are absent. Census SHA256:
  `747447E233634FBC9D9321824148165AC866105FE0367AED27F6F8D9A2E07F46`.
- `FrozenCapRationalCore.lean` was emitted as an early, narrow-import target.
  Earlier lane-C-first CI exposed a missing `Fintype (Fin 9)` import, repaired.
  Subsequent large M/MCap builds hit dependency OOM/exit 137. The core's current
  declarations have no kernel verdict because later runs were cancelled.
- The probe contains only the top-level `Mathlib.olean`; narrower oleans are
  absent. `lake env lean LaneCProbeTiny.lean` timed out at 120 s while loading
  Mathlib. This is an environment limitation, not a Lean error verdict.
- Core emitter checks all seven frozen records with exact `Fraction` arithmetic:
  nonnegative/unit-sum weights, `H = y*E`, frozen margins, and hash-pinned
  constants. Current core SHA256:
  `C48270A5017006F8276C4ECA4367DBA712EA405A965F3C8508F3FD34865B7A5A`.

## 2026-10-29 — parts 19–22 (condensed; superseded by later checks)

- `emit_frozen_cap_row_caps.py` emitted all seven row-cap modules after an
  exact 700/700 inequality check; `FrozenCapRowCapTreeBridges.lean` links the
  copied matrices to `DBMSourceTree.data` by kernel `decide`. Both remain
  **CI pending**. Local Mathlib probing was unavailable (stub olean).

## 2026-10-29 — sessions part 23–24 (exact support threshold <=4; no row rescue)

Did:
- Confirmed no local Lean elaboration: Mathlib olean is a 1128-byte stub; CI is
  the only kernel authority. numpy/scipy also absent, so all searches are exact.
- Recognised the 100 ordered-pair caps are interval sums in `y`. On a fixed
  support they collapse to at most `2^k-1` half-spaces, allowing exhaustive
  rational vertex enumeration. `residual_mixture_faces.py` then excluded every
  <=2-field mixture for all seven public ids.
- Added `residual_mixture_faces3.py` and `residual_mixture_faces4.py`. For every
  id they enumerate all 84 triples / 126 quadruples and every polytope vertex
  exactly, asserting all 100 caps and `Σy=1`, `y>=0`. Result: **all <=3- and
  <=4-field faces are infeasible**. Hence any cap-feasible mixture for these ids
  has support >=5; the existing five/six-field certificates attain that bound.
- Re-ran `certify_next512_row_cap.py`: exit 0, 7/7 exact arbitrary-row-count
  exclusions, all 100 ordered pairs, strict margins `7.39e-7` to `4.97e-5`.
  Thus there is no passing packet to emit, and the former LANES-C row-extension
  plan is mathematically dead for these seven. Any rescue must change the
  certified cap/row set, not just its size.

Files: `residual_mixture_faces3.py` SHA256 `b7768e0c...e0794f`,
`residual-mixture-faces3.json` `e773e520...72b668b`,
`residual_mixture_faces4.py` `579c1c72...e332e01`,
`residual-mixture-faces4.json` `34bce5b7...0f860551`; `TARGETS.txt` unchanged.

Checks run (scope stated):
- `python3 residual_mixture_faces3.py`: exit 0, 7x84 faces, `pass_count=0`.
- `python3 residual_mixture_faces4.py`: exit 0, 7x126 faces, `pass_count=0`.
- `certify_next512_row_cap.py`: exit 0, 512 inspected, 7 excluded, 100 caps each.
- `py_compile` both new scripts: exit 0. `git diff --check`: exit 0. No Lean.

Still unproved / missing:
- The <=3/<=4 support results are Python exact-rational evidence, not kernel
  theorems. Core/M/MCap/row caps/bridges remain CI pending. The 382 absent HOST
  records still block the global energy count; no exclusion is unconditional.

## 2026-10-29 — sessions 25–26 (seven node-pinned exclusion wrappers)

- Added `FrozenCapExcludedTree{1409,2337,2341,2356,2360,2368,2370}.lean`.
  Each fixes `p.nodeID` to its frozen node, derives every row cap from the exact
  `row_cap` certificate via the source-tree bridge, and applies the matching
  `FrozenCapCertificates.excluded_*`. Packet `hf0`/`hg` remain explicit; none of
  the seven exclusions is unconditional.
- Wrapper SHA256: 1409 `e801dfe92443ea05c2b90143ea2e4f75d23a888e6c96341ed19c40f4aba3f36b`;
  2337 `0003985c0af1700b979e8babc781a69f340bf9962b8cdca16d1cc3119ea37c18`;
  2341 `07105ea763d2b5c7750ed8d1a712e95122703bbb8d1c07647392e8d8156e4614`;
  2356 `3feb38e6e0c95455397e14c3c5335edf575cd65d8b5449bf423235c692da691b`;
  2360 `703b0a8b16294bc0626b96351e528694cab299d8046bdc8cd5e8f25ffb077973`;
  2368 `d2163c41ba093eaa9d8008fede1a926a20bb93ca411bafacdd086b0a4984b879`;
  2370 `73fbc36151574be9c3347d5f71c25324b0ef5401a2ad242420bbbc8a967754eb`.
- Checks: emitter/id/import/theorem substitution assertions exit 0; forbidden
  token scan clean; `git diff --check` exit 0. All wrappers **CI pending**.

## 2026-10-29 — session part 27 (row-cap exact rerun)

Did:
- Re-ran `python3 ops/lanes/C/emit_frozen_cap_row_caps.py` (the script has no
  argument parser; even `--help` regenerates). It deterministically rewrote the
  seven `FrozenCapRowCap<id>.lean` modules from the hash-pinned source matrices.
- Exact self-check passed: 7 modules × 100 ordered pairs = 700 caps, with
  `global_min_slack = 0`. Every module reports `dbm_sha256
  BD4E71CB29804A5A3D5953727558F4656D23253A83B69F5C3D6E25EEB4EA8ED5`.
- Current row-cap SHA256: 1409 `A41DC2BD8220550E0A76B60FF8F621C8DE6B8A9CECA6F7CF444FCE3F1BF284EB`;
  2337 `6B5DB3392BF8A0FF24C897469516D7077008716B2EC48F58519C86ACD0B50409`;
  2341 `27C184EA60E2A2F2DF41EA077220EA4746E9AE2B58F99DB7B148F45B052D077F`;
  2356 `21588672F99257A63E3084EC2592DE03AE996AD48707331E3836764984F389C9`;
  2360 `2A0579653E679A38BE5AD2A3462F0D7E28087C3AF2EB8C20BE1DBC109F95583C`;
  2368 `944C57D4FB501AF1B6E74869E937168A3AE8005569722468F2F31938BEA21DC3`;
  2370 `2FABE7633E2F45ABA8C940BCA4BA063265227E2A0FE395D9E14020F35AD92D0C`.
- Static audit confirms all seven wrappers have three imports, explicit
  `hf0`/`hg` packet hypotheses, and conclude `False`; the 1409 wrapper's hcap
  proof rewrites `p.nodeID`, unfolds `DBMMinorantDual.db`, and applies the exact
  tree bridge plus `row_cap`.

Checks run (scope stated):
- Emitter exact Fraction arithmetic: exit 0, 700/700 caps, minimum slack 0.
- `git diff --check`: see final session check; no Lean elaboration locally.

Still unproved / missing:
- Python cap checks are not kernel proofs. Core/M/MCap/row caps/bridges/wrappers
  remain **CI pending**; `hf0`/`hg` and 382 HOST records remain absent.

Very next concrete step: on the next session/CI verdict, route only
`FrozenCapRationalCore`; if green, route `FrozenCapRowCap1409` and inspect the
first error before adding the bridge and 1409 wrapper.

## 2026-10-29 — session part 28 (bounded local core elaboration attempts)
- `project_status.py --check` passed (declarations only); project/probe Lean
  timed out. Core then `c48270a5...65b7a5a`; no kernel verdict.

## 2026-10-29 — session part 29 (CI red diagnosed; two compile fixes)

Did:
- Inspected run `40818062141` / job `123308953128`. Its API/job conclusion is
  `success`, but the job log has `=== EXIT FrozenCapRationalCore 1`,
  `PaidCellCertificateM 1`, and `PaidCellCertificateMCap 1`. The workflow's
  unconditional `true` at the end of the build step masks target failures; the
  run is **CI red** for lane C and the success badge must not be cited.
- Core failure cause: all 14 uses of `Fin.sum_univ_succ` failed as an unknown
  constant because the generated import list omitted
  `Mathlib.Algebra.BigOperators.Fin`.
- `PaidCellCertificateM.of7_valid` failed at lines 65/68/69 because `simpa only`
  did not unfold `Paid16CellCertificate.PA/PB/W/slopeQ/interQ`. MCap's own build
  was then blocked by the missing M olean, not by a separate diagnostic.

Changes:
- `ops/lanes/C/emit_frozen_cap_rational_core.py`: added the missing import; reran
  it, which regenerated the core deterministically.
- `lean/N11Formalization/PaidCellCertificateM.lean`: added the source namespace
  definitions to the three `simpa only` sets.

Files (SHA256):
- `lean/N11Formalization/FrozenCapRationalCore.lean`
  `3ed6bb5026d4eeb00c6bc8cc3f350fb8d522c0414c592370fd3a91f36fc4e7c4`
- `lean/N11Formalization/PaidCellCertificateM.lean`
  `b0c1f6d583b5c4d748a281e14dc7289d75c2d761a95748fb59977fb8afa44072`
- `ops/lanes/C/emit_frozen_cap_rational_core.py`
  `10ecb5500eff5b22366910c4c01f4d3299bf4e5c841f917efe2c7e7ca1a87d93`

Checks run (scope stated):
- Core emitter: exit 0, deterministic output and frozen-source hashes printed.
- `git diff --check`: exit 0; forbidden-token scan over core/M/MCap: clean.
- No local Lean elaboration (Mathlib probe olean remains a 1128-byte stub), so
  the fixes are **CI pending**, not paid.

Still unproved / missing:
- Core, M, MCap, row caps, tree bridges, and seven wrappers still have no green
  kernel verdict. `hf0`/`hg` packet inputs and 382 residual HOST records remain
  absent; no energy count changes.

Very next concrete step: rerun CI and require `=== EXIT
N11Formalization.FrozenCapRationalCore 0`, then M and MCap 0; only after that add
`N11Formalization.FrozenCapRowCap1409` alone to `TARGETS.txt`. Do not infer a
green target from the workflow's overall badge.

## 2026-10-29 — sessions 30-32 (condensed; corrected CI still pending)

- Old run `40818062141` was red at all three targets due to the now-repaired
  missing `Mathlib.Algebra.BigOperators.Fin` import and old `of7_valid`
  simplifications. Pinned Mathlib `0df444a...` does define `Fin.sum_univ_succ`.
- Corrected run `40857762507` (head `0cb4f8de`, job `123392944402`) has had its
  `Build` step in progress throughout sessions 30-32. No target exit exists, so
  core/M/MCap remain **CI pending**, not green.
- Emitter reran twice after the fixes (exit 0): all seven records passed exact
  `Fraction` nonnegativity, unit-sum, frozen-source, weighted-term, and strict
  margin checks; regenerated core stayed byte-identical. Frozen inputs checked:
  `FlashCosineLeaf318` `08F36489...788A`, `Interval/Trig` `FB3DF66D...A04C`,
  `FlashCosineLeaf284Bridge` `C001704C...B1F8`.
- MCap transport was audited against `lower = f0Lo - lamB + rmin` and
  `rho = sum_a lam_a * rowA`; the weighted reduction, `lamB` bound, and
  strict-gain contradiction are algebraically sound.

SHA256: core `3ed6bb50...e7c4`, M `b0c1f6d5...4072`, MCap
`1697c1be...f6ea`, emitter `10ecb550...7d93`.
Checks: emitter exit 0, static declaration audit, `git diff --check` exit 0,
forbidden-token scan clean. No Lean kernel verdict.

Still unproved: no green core/M/MCap verdict; row caps, bridges, tree wrappers,
packet `hf0`/`hg`, and 382 HOST records remain unpaid.

## 2026-10-29 — session part 33 (bounded local check attempted)

Did: polled run `40857762507`; job `123392944402` is still `in_progress`, with
only `Build` marked `in_progress` and no target exit. Confirmed current core/M/
MCap SHA256 values exactly as above, `git diff --check` exit 0, and no forbidden
tokens in those three modules. Attempted bounded direct elaboration from
`n11-work/lean`: `timeout 110s lake env lean N11Formalization/FrozenCapRationalCore.lean`.
It exited 124 after ~110 s while Lake reported `info: mathlib: cloning
https://github.com/leanprover-community/mathlib4`; scope was local core only and
it produced **no Lean verdict**. The CI build remains the only candidate kernel
check.

Still unproved: same as above; in particular the core theorem set, M/MCap, all
seven row caps and tree wrappers, `hf0`/`hg`, and 382 HOST records.

Very next concrete step: read `=== EXIT N11Formalization.FrozenCapRationalCore`,
then M and MCap, from run `40857762507`. If all are 0, add only
`N11Formalization.FrozenCapRowCap1409` to `TARGETS.txt`; otherwise patch the
first reported core/M/MCap diagnostic. Do not treat local timeout as red.
