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

- Emitters generated exact row-cap modules for 1409 and then all seven public
  ids, checking 700 ordered-pair inequalities over `Fraction` before output:
  `emit_frozen_cap_row_caps.py` and `FrozenCapRowCap{1409,2337,2341,2356,2360,2368,2370}.lean`.
- `FrozenCapRowCapTreeBridges.lean` connects all seven copied matrices to
  `DBMSourceTree.data` using `decide +kernel`; all bridge/row-cap modules remain
  **CI pending**. Earlier one-off 1409 emitter/output hashes are superseded.
- Local Lean probing was unavailable: the Mathlib probe olean is a stub; a
  150-second attempt exited 124 without a verdict. No paid claim follows.

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

Files / SHA256 (current bytes, uppercase in manifest when needed):
- `ops/lanes/C/residual_mixture_faces3.py`
  `b7768e0c6ea15b4f64f875275a0eb0787338a3ef232701bae0b3edc032e0794f`
- `ops/lanes/C/residual-mixture-faces3.json`
  `e773e520f89475689c89e0e7b67c78d7d7f925982a5d128c4abb4d53472b668b`
- `ops/lanes/C/residual_mixture_faces4.py`
  `579c1c7244ff452ad8a7a65d0f18c4b69f22c9596cf6f02dc241b7d42e332e01`
- `ops/lanes/C/residual-mixture-faces4.json`
  `34bce5b7c91692d8e8c8d5cb5144e2d01c465d08750fcf56488a76bc0f860551`
- `TARGETS.txt` unchanged.

Checks run (scope stated):
- `python3 residual_mixture_faces3.py`: exit 0, 7x84 faces, `pass_count=0`.
- `python3 residual_mixture_faces4.py`: exit 0, 7x126 faces, `pass_count=0`.
- `certify_next512_row_cap.py`: exit 0, 512 inspected, 7 excluded, 100 caps each.
- `py_compile` both new scripts: exit 0. `git diff --check`: exit 0. No Lean.

Still unproved / missing:
- The <=3/<=4 support results are Python exact-rational evidence, not kernel
  theorems. Core/M/MCap/row caps/bridges remain CI pending. The 382 absent HOST
  records still block the global energy count; no exclusion is unconditional.

## 2026-10-29 — session part 25 (tree-pinned 1409 exclusion wrapper)

Did:
- Added `lean/N11Formalization/FrozenCapExcludedTree1409.lean`. It applies
  `FrozenCapCertificates.excluded_1409` after fixing `p.nodeID = 1409` and
  deriving every row cap from `FrozenCapRowCap1409.row_cap` through
  `FrozenCapRowCapTreeBridges.db_eq_tree_1409`.
- This closes only the node/row-database wiring for 1409. The packet hypotheses
  `hf0` and `hg` remain explicit; no `excluded_1409` instance is unconditional.

File SHA256:
- `lean/N11Formalization/FrozenCapExcludedTree1409.lean`
  `3EEBE24D7FD4DA84A134DF97404C5001498E4E5D802903C946B05DF5D1A94B5C`.

Checks run (scope stated):
- `git diff --check`: exit 0. Placeholder scan: clean (no forbidden tactics or
  declarations). No Lean elaboration locally; module is **CI pending**.
- `TARGETS.txt` unchanged per the standing instruction to wait for the core.
- `timeout 60 python tools/project_status.py --check`: exit 0; this validates
  handoff-index/manifest declarations only, not mathematics or file integrity.

Still unproved / missing:
- Core/M/MCap/row caps/bridges remain CI pending. `hf0`/`hg` must be supplied by
  actual packets, and 382 residual HOST records remain absent.

Very next concrete step: after core is CI green, route this module alone and
inspect the first elaboration diagnostic; then generate the same wrapper for
2337–2370 only if 1409 is green.
## 2026-10-29 — session part 26 (seven node-pinned exclusion wrappers)

Did:
- Generalized the 1409 wrapper to all seven public ids with one uniform,
  deterministic lane-C generation pass. Each `FrozenCapExcludedTree<id>.lean`
  imports the id's exact row-cap module and `FrozenCapRowCapTreeBridges`, fixes
  `p.nodeID = id`, derives all row caps from `row_cap` plus
  `db_eq_tree_<id>`, and applies `FrozenCapCertificates.excluded_<id>`.
- `hf0` and `hg` remain explicit packet hypotheses. No exclusion is
  unconditional, and `TARGETS.txt` remains unchanged pending core CI green.
- The 1409 file was regenerated with the same template; current bytes differ
  from part 25 because the template comment/import list is now explicit. It is
  not kernel-checked.

Files (SHA256):
- `lean/N11Formalization/FrozenCapExcludedTree1409.lean`
  `e801dfe92443ea05c2b90143ea2e4f75d23a888e6c96341ed19c40f4aba3f36b`
- `.../FrozenCapExcludedTree2337.lean`
  `0003985c0af1700b979e8babc781a69f340bf9962b8cdca16d1cc3119ea37c18`
- `.../FrozenCapExcludedTree2341.lean`
  `07105ea763d2b5c7750ed8d1a712e95122703bbb8d1c07647392e8d8156e4614`
- `.../FrozenCapExcludedTree2356.lean`
  `3feb38e6e0c95455397e14c3c5335edf575cd65d8b5449bf423235c692da691b`
- `.../FrozenCapExcludedTree2360.lean`
  `703b0a8b16294bc0626b96351e528694cab299d8046bdc8cd5e8f25ffb077973`
- `.../FrozenCapExcludedTree2368.lean`
  `d2163c41ba093eaa9d8008fede1a926a20bb93ca411bafacdd086b0a4984b879`
- `.../FrozenCapExcludedTree2370.lean`
  `73fbc36151574be9c3347d5f71c25324b0ef5401a2ad242420bbbc8a967754eb`

Checks run (scope stated):
- Generation and id/import/theorem substitution asserts: exit 0, 7 files.
- Forbidden-token scan over all seven wrappers: clean.
- `git diff --check`: exit 0. No Lean elaboration locally; all wrappers **CI pending**.

Still unproved / missing:
- Core/M/MCap/row caps/bridges/wrappers have no kernel verdict. Actual packets
  must supply `hf0`/`hg`; 382 HOST residual records remain absent.

Very next concrete step: once `FrozenCapRationalCore` is CI green, add
`FrozenCapRowCap1409` and then its tree bridge/wrapper alone to `TARGETS.txt`;
inspect first diagnostics before routing the other six.

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

Did:
- Re-read guidance, lane C scope, notes, and `ops/ci/LATEST.md`; ran
  `python3 tools/project_status.py --check` (exit 0, handoff declarations only).
- Audited current `TARGETS.txt`: still exactly `FrozenCapRationalCore`,
  `PaidCellCertificateM`, `PaidCellCertificateMCap`.
- Tried the Mathlib-only `FrozenCapRationalCore.lean` alone, not the project:
  project `lake env lean` timed out at 90 s while fetching Mathlib (no Lean
  verdict); `/workspace/tools/mathlib-probe` `lake env lean` timed out at 120 s
  with zero diagnostics (no Lean verdict).

File:
- `lean/N11Formalization/FrozenCapRationalCore.lean`, unchanged, SHA256
  `c48270a5017006f8276c4eca4367dba712ea405a965f3c8508f3fd34865b7a5a`.

Checks run (scope stated):
- `tools/project_status.py --check`: exit 0; manifest/index declarations only.
- `git diff --check`: exit 0.
- No local Lean elaboration succeeded; core remains **CI pending**.

Still unproved / missing:
- Core/M/MCap/row caps/bridges/wrappers have no kernel verdict; `hf0`/`hg`
  packet inputs and 382 residual HOST records remain absent.

Very next concrete step: inspect the current CI run's first diagnostic for
`FrozenCapRationalCore`; if green, add only `FrozenCapRowCap1409` to
`TARGETS.txt`, otherwise patch the reported core error.
