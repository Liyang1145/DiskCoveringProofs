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

## 2026-10-29 — session part 19 (first exact row-cap module)

Did:
- Added `emit_frozen_cap_row_cap_1409.py`. It parses
  `DBMSourceTree.node1409` from the frozen source, records the full DBM source
  SHA256, fail-closes against the certificate's pinned DBM hash, and
  exact-`Fraction`-checks all 100 ordered pairs before emission.
- Generated `FrozenCapRowCap1409.lean`: a standalone module importing the
  rational core (not the OOM-heavy packet chain), with the hash-checked 10x10
  copied matrix and a single theorem `row_cap (i j : Fin 10)` covering all 100
  pairs via `fin_cases i <;> fin_cases j <;> norm_num`.
- Left `TARGETS.txt` unchanged per supervisor guidance. The new module is
  **CI pending**, not paid, and is not yet routed to CI.

Files / SHA256 (current bytes):
- `ops/lanes/C/emit_frozen_cap_row_cap_1409.py`
  `4197E63F34CB0179563BBCE0468AB4BEB5682D255E567635290188FFDEA0FD10`
- `lean/N11Formalization/FrozenCapRowCap1409.lean`
  `178A5FD4B1C48E054844E0C3B7D47098E73ADEC7C22DEB3D614D8A2C88AEE3C0`
- DBM source checked:
  `BD4E71CB29804A5A3D5953727558F4656D23253A83B69F5C3D6E25EEB4EA8ED5`

Checks run (scope stated):
- `python3 emit_frozen_cap_row_cap_1409.py`: exit 0; all 100 ordered-pair caps
  exact, minimum slack 0. `py_compile`: exit 0. `git diff --check`: exit 0.
- Placeholder scan found only the intended `#print axioms` audit line; no
  `sorry`, `admit`, added axiom, `native_decide`, `ofReduceBool`, or
  `implemented_by`.
- No Lean elaboration locally: usable Mathlib oleans are absent. The exact
  `norm_num` inequality proofs are unverified by a kernel.

Still unproved / missing:
- Core weight/term/strict-gain declarations and the new row-cap theorem are
  **CI pending**. The frozen matrix copy is not yet bridged by definitional
  equality to `DBMMinorantDual.db`; no `excluded_<id>` is unconditional.
- Six remaining public row-cap ids and all 382 absent residual records remain
  unpaid.

Very next concrete step: after `FrozenCapRationalCore` is CI green, add
`FrozenCapRowCap1409` to `TARGETS.txt` and inspect its first diagnostic. If
green, emit the other six row-cap modules from the same generator pattern, then
add `hnode` and the real `db` bridge before citing an exclusion.

## 2026-10-29 — session part 20 (all seven exact row-cap modules)

Did:
- Replaced the one-off pilot emitter with deterministic
  `emit_frozen_cap_row_caps.py`. It pins the DBM source SHA256, extracts all
  seven `DBMSourceTree.node<id>` matrices, validates each frozen certificate's
  9 nonnegative unit-sum weights, and exact-`Fraction`-checks all 100 ordered
  row caps per id (700 total) before emission.
- Generated `FrozenCapRowCap{1409,2337,2341,2356,2360,2368,2370}.lean`.
  Each module imports only `FrozenCapRationalCore`, copies its hash-checked
  10x10 integer matrix, and proves `row_cap (i j : Fin 10)` for every pair by
  `fin_cases`/`norm_num`. Removed the superseded one-off emitter.
- Left `TARGETS.txt` unchanged per the standing supervisor instruction: the
  rational core is still CI pending. These seven modules are **CI pending /
  not routed**, not paid.

Files / SHA256 (current bytes):
- `ops/lanes/C/emit_frozen_cap_row_caps.py`
  `22AB0C050BE87A2464B995E19FB528AC61EE116C61AF956BF60A5A48DC0208D3`
- Lean modules: `1409 A41DC2BD8220550E0A76B60FF8F621C8DE6B8A9CECA6F7CF444FCE3F1BF284EB`;
  `2337 6B5DB3392BF8A0FF24C897469516D7077008716B2EC48F58519C86ACD0B50409`;
  `2341 27C184EA60E2A2F2DF41EA077220EA4746E9AE2B58F99DB7B148F45B052D077F`;
  `2356 21588672F99257A63E3084EC2592DE03AE996AD48707331E3836764984F389C9`;
  `2360 2A0579653E679A38BE5AD2A3462F0D7E28087C3AF2EB8C20BE1DBC109F95583C`;
  `2368 944C57D4FB501AF1B6E74869E937168A3AE8005569722468F2F31938BEA21DC3`;
  `2370 2FABE7633E2F45ABA8C940BCA4BA063265227E2A0FE395D9E14020F35AD92D0C`.
- Frozen DBM source checked for all seven:
  `BD4E71CB29804A5A3D5953727558F4656D23253A83B69F5C3D6E25EEB4EA8ED5`.

Checks run (scope stated):
- `python3 emit_frozen_cap_row_caps.py`: exit 0; 7 modules, 700 ordered-pair
  caps exact, global minimum slack 0. `py_compile`: exit 0.
- Re-ran the emitter and `sha256sum -c` against all seven pre-run bytes: every
  file identical. `git diff --check`: exit 0.
- Placeholder scan over new Lean modules and emitter found no `sorry`, `admit`,
  added `axiom`, `native_decide`, `ofReduceBool`, or `implemented_by`.
- No Lean elaboration locally because project Mathlib oleans are unavailable.
  Kernel truth of all seven `row_cap` theorems remains unverified.

Still unproved / missing:
- `FrozenCapRationalCore`, all seven row-cap theorems, and M/MCap remain CI
  pending. Matrix copies are not yet definitionally bridged to
  `DBMMinorantDual.db`; no `excluded_<id>` is unconditional. The 382 absent
  public residual records remain missing.

Very next concrete step: once `FrozenCapRationalCore` is CI green, add only
`N11Formalization.FrozenCapRowCap1409` to `TARGETS.txt` and inspect its first
CI diagnostic. If the pilot is green, route the remaining six similarly; keep
the `hnode`/`DBMMinorantDual.db` bridge as a separate follow-up.

## 2026-10-29 — session part 21 (source-tree bridge for all seven row caps)

Did:
- Added `lean/N11Formalization/FrozenCapRowCapTreeBridges.lean`. It imports the
  seven frozen row-cap modules plus `DBMSourceTreeData` and states one bridge
  per id: for all `i j : Fin 10`,
  `((DBMSourceTree.data (id : Fin 5011)).db i j : ℚ) / 4096` equals the copied
  `FrozenCapRowCap<id>.db i j`. Each of the seven proofs is `decide +kernel`,
  following the existing `Patch120K5Consumer` bridge precedent.
- Did not edit the frozen source or row-cap copy modules. Did not change
  `TARGETS.txt`: the rational core is still CI pending and the standing
  supervisor instruction remains to pilot only after it is green.

File SHA256 (current bytes):
- `lean/N11Formalization/FrozenCapRowCapTreeBridges.lean`
  `2A42E2F9B950312C4FF0AE46DA59CF146B42C121AAB0C73E7EBDC01729433080`.

Checks run (scope stated):
- Placeholder scan over the new module: no `sorry`, `admit`, added `axiom`,
  `native_decide`, `ofReduceBool`, or `implemented_by`.
- `git diff --check`: exit 0. No Lean elaboration locally: project Mathlib
  oleans are unavailable. All seven bridge theorems are **CI pending**.

Still unproved / missing:
- Core, M/MCap, row caps and these bridges have no kernel verdict yet. The
  `p.nodeID = id` and packet-to-rational-core wiring are still absent, so no
  `excluded_<id>` theorem is unconditional. The 382 absent residual records
  still block any energy-count claim.

Very next concrete step: when `FrozenCapRationalCore` is CI green, add
`N11Formalization.FrozenCapRowCap1409` alone to `TARGETS.txt`; if green, then
add `FrozenCapRowCapTreeBridges` to validate the source-tree identity. Only
after that add the six remaining row caps, then implement `hnode` wiring.

## 2026-10-29 — session part 22 (local probe attempt for rational core)

Did:
- Since `FrozenCapRationalCore.lean` imports only Mathlib, copied it unchanged
  into `/workspace/tools/mathlib-probe/N11Formalization/` and attempted a real
  local elaboration there to obtain a kernel verdict ahead of CI.
- No source/lane files changed; `TARGETS.txt` unchanged (core remains CI
  pending, row caps/bridges still not routed).

Checks run (scope stated):
- `timeout 150 lake env lean N11Formalization/FrozenCapRationalCore.lean`
  (after `source /workspace/tools/env.sh`): exit 124 = **timed out**, no
  diagnostic and no `.olean`; this is NOT a pass or a failure. Scope was only
  the copied core module against cached Mathlib, not the project build.
- No new bytes emitted, so no new SHA256 to pin.

Very next concrete step: split the local probe by importing the core after a
first pass with per-id core fragments (or raise the bound once on the 2-core
probe if time allows), to find which `strict_gain_*`/huge-rational declaration
dominates. Keep CI as the authority; when CI reports the core green, add
`FrozenCapRowCap1409` alone to `TARGETS.txt`.
