# Lane C notes

## Condensed history through 2026-10-29 part 10

- `PaidCellCertificateM.lean` generalizes the 16-field packet from `Fin 7` to
  an arbitrary nonnegative DBM-row count; `PaidCellCertificateMCap.lean` adds
  weighted reduced-cost transport and `not_valid_of_frozen_cap`. Both were
  **CI pending**; no lane-C module has yet been confirmed kernel-green.
- `recompute_next512_formulas.py` recomputes all 512 public next512 records
  with exact `Fraction`; 505 pass and seven fail: `1409, 2337, 2341, 2356,
  2360, 2368, 2370`.
- `certify_next512_row_cap.py` checks all 100 ordered pairs, so these seven are
  excluded for an arbitrary number of rows. Tightest Python margin
  `7.388363154221271e-7` at node 2356. This is exact Python evidence, not
  kernel credit.
- `build_residual389_census.py` reconstructs 389 residual terminal IDs. Only
  seven are in the public artifact; 382 HOST records are absent locally, so no
  payment transfers across the whole residual. Census SHA256
  `747447E233634FBC9D9321824148165AC866105FE0367AED27F6F8D9A2E07F46`.
- `emit_frozen_cap_certificates.py` emits exact `F0`, `G`, `y`, `E`, endpoint
  and strict-gain facts plus conditional `excluded_<id>` theorems for the seven
  public nodes. The module remained CI pending. Run `40736931996` was externally
  cancelled at 18:38 UTC before reaching lane C; its log had no Lean `error:`.

## 2026-10-29 — session part 11 (standalone rational core)

Did:
- Added a new early CI target `N11Formalization.FrozenCapRationalCore`, emitted
  by `ops/lanes/C/emit_frozen_cap_rational_core.py`.
- The module imports `Mathlib` directly (not the large project packet chain) and
  contains exact constants, seven `F0/G/y/E` records, nonnegativity/unit-sum
  weights, and seven `strict_gain_<id>` rational inequalities. Expected exact
  gain/margin identities are fail-closed against the frozen certificate JSON.
- `ops/lanes/C/TARGETS.txt` now lists the core first, then M, MCap, and the
  full FrozenCapCertificates target.

Files / SHA256 (current bytes):
- `ops/lanes/C/emit_frozen_cap_rational_core.py`
  `DC452729FFBE8881A57A7B930429411C66BF08AD91A7D66A32CCBCFF9EA5AFFB`
- `lean/N11Formalization/FrozenCapRationalCore.lean`
  `7AB84DCB44780929F65B273CE45AEDB90B6BE77960610E677C86E000846A2756`
- `ops/lanes/C/TARGETS.txt`
  `BED53B62E9339CEB40615595E1203AE8293C035B056C12EAAA582892564C18AD`

Checks run (scope stated):
- `python3 -m py_compile emit_frozen_cap_rational_core.py`: exit 0.
- `python3 emit_frozen_cap_rational_core.py`: exit 0; all seven records passed
  exact `Fraction` weight/margin checks and the module was regenerated.
- Forbidden-token grep over the generator and Lean module: no hits.
- `git diff --check`: exit 0.
- `python tools/project_status.py --check`: PASS; navigation/index scope only.
- No Lean build locally (project/Mathlib oleans absent). The new module is
  **CI pending**, not paid.

Still unproved / missing:
- The seven `strict_gain_*` proofs are closed over the emitted literal `E`
  vectors but have not been kernel-checked. The bridge
  `endpointLo Dq DQ (G q) = E q` remains in the older full module.
- Frozen `f0Lo`/`g` identities and arbitrary-row cap facts are still explicit
  hypotheses; no concrete packet is instantiated. All 389 residual terminals
  remain unpaid and 382 source records remain absent.

Very next step: inspect serial CI for `FrozenCapRationalCore` first. If green,
replace the full module's duplicated heavy endpoint/strict-gain proofs with
small bridge theorems to the core; if red, fix the first `norm_num`/elaboration
error in the core before touching the packet chain.

## 2026-10-29 — session part 12 (CI triage + narrow imports)

Did:
- Downloaded and inspected the actual job log for run `40736931996` (`gh` is
  absent; used the public GitHub jobs/logs API). It contains no Lean `error:`
  from lane C: the job was killed while building lane A, ending with runner
  shutdown / exit 143 at 18:37:58 UTC. Thus the run is an infrastructure
  failure, not a red lane-C module.
- Replaced the standalone core's blanket `import Mathlib` with the five
  modules actually used: `Data.Rat.Defs`, `Data.Fin.VecNotation`,
  `Algebra.BigOperators.Group.Finset.Basic`, `Tactic.NormNum`, and
  `Tactic.FinCases`. Regenerated the Lean file from the deterministic emitter.

Files / SHA256 (current bytes):
- `ops/lanes/C/emit_frozen_cap_rational_core.py`
  `EC617EDF75772882162BA7015D48D0D6C0459578B2B034E9215CA12F23AC2731`
- `lean/N11Formalization/FrozenCapRationalCore.lean`
  `DCAEFF8CEEE7A514E2B13E3A260A8B0B1FB18025BE53A01FBD04794024113862`
- `ops/lanes/C/TARGETS.txt` unchanged at
  `BED53B62E9339CEB40615595E1203AE8293C035B056C12EAAA582892564C18AD`

Checks run (scope stated):
- `python3 -m py_compile emit_frozen_cap_rational_core.py` and rerun of the
  emitter: exit 0; all seven records passed exact `Fraction` checks.
- Forbidden-token grep over generator/core: no hits; `git diff --check`: exit 0;
  `python tools/project_status.py --check`: PASS (index/manifest scope only).
- Bounded local probe of the full core: timeout after 150 s, no Lean
  diagnostic. Even the narrowed imports do not load within the weak sandbox;
  this is NOT a build verdict. Core remains **CI pending**.

Still unproved / missing:
- No Lean kernel check of `weights_nonneg_*`, `weights_sum_*`, or
  `strict_gain_*`. The endpoint bridge and packet hypotheses remain explicit;
  all 389 residual IDs remain unpaid; 382 source records remain absent.

Very next step: on the next `n11-lean-build` that actually starts lane C,
inspect `FrozenCapRationalCore` first. If green, replace the seven duplicated
endpoint/strict-gain blocks in `FrozenCapCertificates` with bridges to the core.
If red, fix the first reported declaration only. If lane C is still not reached
because lane A consumes the runner, ask the supervisor to run a lane-C-only
serial build before extending any packet emission.

## 2026-10-29 — session part 13 (probe blocker isolated)

Did:
- Rechecked the current core and emitter bytes; no source change was needed.
- Attempted a bounded probe-only check of the core. The probe contains a
  partial Mathlib tree but lacks `Mathlib/Data/Rat/Defs.olean`; adding a local
  empty root `Mathlib.olean` shifted the error to that exact missing narrow
  olean. This is an environment limitation, not a Lean diagnostic.

Current hashes:
- `ops/lanes/C/emit_frozen_cap_rational_core.py`
  `EC617EDF75772882162BA7015D48D0D6C0459578B2B034E9215CA12F23AC2731`
- `lean/N11Formalization/FrozenCapRationalCore.lean`
  `DCAEFF8CEEE7A514E2B13E3A260A8B0B1FB18025BE53A01FBD04794024113862`
- `ops/lanes/C/TARGETS.txt`
  `BED53B62E9339CEB40615595E1203AE8293C035B056C12EAAA582892564C18AD`

Checks run (scope stated):
- `lake env lean FrozenCapRationalCore.lean` in `/workspace/tools/mathlib-probe`
  failed at import resolution because `Mathlib/Data/Rat/Defs.olean` is absent;
  no declaration was elaborated. Core remains **CI pending**, not paid.

Still unproved / missing:
- All seven weight nonnegativity/sum and strict-gain declarations remain
  un-kernel-checked. Endpoint bridges and packet hypotheses are still explicit;
  all 389 residual IDs remain unpaid and 382 source records are absent.

Very next concrete step: run/inspect a lane-C-only `n11-lean-build` for
`N11Formalization.FrozenCapRationalCore`; do not edit packet emission until CI
returns the first declaration-level result.

## 2026-10-29 — session part 14 (CI triage + public-record coverage audit)

Did:
- Pulled the complete log for run `40797575073` / job `123204085190`. It used
  the pre-`ebc9d4ce` target order, built lane A first, reached
  `N11Formalization.C450Identify`, then died from runner shutdown (exit 143)
  at 01:52:34 UTC. It never started a lane-C target; there is still no
  kernel verdict for any lane-C module.
- Recursively parsed every JSON file under `evidence-20261014`,
  `evidence-20261028`, and `assets/replay/n11-wip`, looking for residual IDs
  carrying `g`, `f0Lo`, or `weights`. Exactly the same seven IDs are present:
  `1409, 2337, 2341, 2356, 2360, 2368, 2370`; all 382 other residual IDs have
  no public field record. This independently confirms the census gap rather
  than merely repeating its manifest claim.
- Confirmed the old run executed target order A, A, ..., B, ..., C. The current
  workflow at supervisor commit `ebc9d4ce` reads lane C first; run
  `40802064355` (head `2f5a2d11`) started at 01:52:36 UTC and is the first run
  that can reach the core first. It was still in Mathlib-cache setup when this
  session ended.
- Local probe setup remains unavailable: `lake exe cache get` rebuilt the cache
  executable, then exceeded bounded timeout while computing the requested
  module closure; no Mathlib olean was fetched and no Lean declaration was
  elaborated. This is an environment failure, not a red proof.

Checks run (scope stated):
- Public JSON coverage scan over the three listed evidence trees: 389 target
  IDs, 7 present, 382 absent. Scope is local public bytes only.
- CI log scan: no lane-C `error:` exists in run `40797575073`; absence of an
  error is not a build pass because lane C was never reached.
- `git diff --check`: exit 0. `python tools/project_status.py --check`: PASS
  (index/manifest scope only).

Still unproved / missing:
- `FrozenCapRationalCore` remains draft/CI pending. The seven strict-gain
  inequalities, weight facts, endpoint bridges, and arbitrary-row exclusions
  have no kernel verdict. All 389 residual IDs remain unpaid; 382 lack the
  public field record needed even for a Python dual audit.

Very next concrete step: read run `40802064355` as soon as its first lane-C
target reports. If `FrozenCapRationalCore` is green, replace duplicated
`FrozenCapCertificates` rational proofs with core lemmas; if red, fix only the
first declaration-level error. If the runner again dies before lane C, ask the
supervisor for a lane-C-only workflow invocation rather than another serial
all-lane run.
