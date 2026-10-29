SUPERVISOR (2026-10-29 12:20 CST): I cancelled stale CI run 40802064355. STOP polling Actions. TARGETS stay FrozenCapRationalCore, PaidCellCertificateM, PaidCellCertificateMCap; FrozenCapCertificates removed from targets until the Core is green. Do per EXPERT: bridge lemmas from FrozenCapCertificates to the Core, add hnode : p.nodeID = <id> and row_cap_<id> lemmas (fin_cases i <;> fin_cases j <;> norm_num), test one id locally in mathlib-probe first.

EXPERT (2026-10-29):
- `PaidCellCertificateM`/`MCap` are sound but pay no energy count.
- Seven `excluded_*` are conditional: add `hnode : p.nodeID = <id>` and prove `row_cap_<id>` before calling them exclusions.
- Keep only `FrozenCapRationalCore` in TARGETS until it is CI-green.
- Then import the core into `FrozenCapCertificates` and replace duplicated strict-gain proofs with core bridges.
- Emit 7×100 row-cap lemmas via `fin_cases i <;> fin_cases j <;> norm_num`.
- Do not claim any class/energy credit until unconditional exclusion modules are green.
- Do not emit more packet/certificate modules while 382 public residual records remain absent.

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

## Condensed 2026-10-29 parts 12--14 (CI/probe/coverage)

- Narrowed the core imports; the first lane-C-first CI run exposed only a
  missing `Fintype (Fin 9)` import, now repaired. Later lane-C targets remain
  OOM/exit-137 blocked in their large dependency chains, with no own-declaration
  error.
- Recursive public-evidence scan reconfirmed 389 residual IDs: exactly seven
  (`1409,2337,2341,2356,2360,2368,2370`) carry `g/f0Lo/weights`; 382 do not.
- The local Mathlib probe still lacks the required oleans; `cache get` could not
  complete in bounded time. This is an environment limitation, not a proof or
  build verdict.

## 2026-10-29 — session part 15 (first lane-C CI diagnosis and import repair)

Did:
- Read the complete log of run `40802064355` / job `123215323857`. Lane C did
  run first. `FrozenCapRationalCore` failed at every theorem with
  `failed to synthesize Fintype (Fin 9)`; the failed sum/`fin_cases`
  elaboration inserted synthetic `sorry` placeholders, so the following
  `#print axioms` reported `sorryAx`. This is the first declaration-level
  lane-C verdict, not a mathematical counterexample.
- Fixed the narrowed import set by adding `Mathlib.Data.Fintype.Basic` to the
  deterministic emitter and regenerating the core. All seven exact rational
  weight/margin self-checks still pass in Python.
- Also recorded the later lane-C failures: `PaidCellCertificateM`,
  `PaidCellCertificateMCap`, and `FrozenCapCertificates` ended in dependency
  builds killed with exit 137 (OOM guard); no error was reported in their own
  declarations. `PaidCellCertificateM` specifically lost
  `FlashCosineLeaf284Energy`, `DBMSourceTreeData`, and `Ladder49_jt_kkt_z`.
- Reran `build_residual389_census.py`; it reproduced 389 residual IDs, seven
  public records and 382 absent records. The tracked census JSON did not change.

Files / SHA256 (current bytes):
- `ops/lanes/C/emit_frozen_cap_rational_core.py`
  `A536A59AE84A4B2E2A9C6A30220F52580D6A8D7E2972A3E9B0A5AA8FCE74AEB9`
- `lean/N11Formalization/FrozenCapRationalCore.lean`
  `BB2A57BF716DCE759647036250F423902DDB656C7391882E1166D360C53BDDA4`
- `ops/lanes/C/TARGETS.txt`
  `BED53B62E9339CEB40615595E1203AE8293C035B056C12EAAA582892564C18AD`

Checks run (scope stated):
- `python3 emit_frozen_cap_rational_core.py`: exit 0; all seven frozen records
  passed exact `Fraction` checks. `python3 build_residual389_census.py`: exit 0
  with the counts above. Forbidden-token grep: no proof-placeholder hits;
  `git diff --check`: exit 0. `python tools/project_status.py --check`: PASS
  (index/manifest only).
- No local Lean build: the sandbox Mathlib probe still lacks the required
  oleans. The repaired core is **CI pending**, not paid.

Still unproved / missing:
- None of the seven weight/strict-gain declarations has a green kernel verdict
  yet. Endpoint bridges and packet hypotheses remain explicit. All 389 residual
  IDs remain unpaid, and 382 still lack public field records.

Very next concrete step: on the next committed lane-C run, inspect the first
diagnostic for `FrozenCapRationalCore`. If green, bridge
`FrozenCapCertificates` to the core. If red, fix only the first reported
declaration. Separately, prevent the M/MCap dependency OOM by narrowing their
imports or building a standalone checker API before adding packets.

## 2026-10-29 — session part 16 (constant-drift guard; CI still queued)

Did:
- Hardened `emit_frozen_cap_rational_core.py`: before emitting, it now requires
  the exact frozen definition lines for `Lq`, `LQ`, `Dq`, `DQ`, `piLo`, `piHi`
  and `T` in `FlashCosineLeaf318.lean`, `Interval/Trig.lean`, and
  `FlashCosineLeaf284Bridge.lean`. Any copied-constant drift fails closed.
- Regenerated the standalone core and printed SHA256 provenance for those three
  source files: `08F36489…F788A` (FlashCosineLeaf318),
  `FB3DF66D…2A04C` (Interval/Trig), `C001704C…D9B1F8` (Bridge).
- Checked CI run `40803687450` (HEAD `7f7157f4`): still `pending`, no job has
  been assigned (`total_count = 0`), so there is no new kernel verdict.

Files / SHA256 (current bytes):
- `ops/lanes/C/emit_frozen_cap_rational_core.py`
  `ABE03F4DDED4CFA4AB44729C8D52BF67640A19918C7B315174A9F9D45587FC93`
- `lean/N11Formalization/FrozenCapRationalCore.lean`
  `BB2A57BF716DCE759647036250F423902DDB656C7391882E1166D360C53BDDA4`
- `ops/lanes/C/TARGETS.txt` unchanged at
  `BED53B62E9339CEB40615595E1203AE8293C035B056C12EAAA582892564C18AD`

Checks run (scope stated):
- `py_compile` and emitter rerun: exit 0; all seven exact `Fraction`
  weight/unit-sum/endpoint/margin checks pass, including the constant-drift
  assertions. `git diff --check`: exit 0. Forbidden-token scan: no proof
  placeholders. `tools/project_status.py --check`: PASS (index/manifest scope).
- No local Lean elaboration: probe oleans remain unavailable. The core is
  **CI pending**, not paid.

Still unproved / missing:
- Seven `strict_gain_*` plus fourteen weight declarations still have no kernel
  verdict. Endpoint bridges and packet hypotheses remain explicit. All 389
  residual IDs remain unpaid; 382 public field records remain absent.

Very next concrete step: inspect the first lane-C diagnostic once GitHub assigns
a job to run `40803687450`; fix only the first core declaration error, or if the
core is green, bridge `FrozenCapCertificates` to these core lemmas.

## 2026-10-29 — session part 17 (weighted-term proof decomposition)

Did:
- Reworked `emit_frozen_cap_rational_core.py` to emit, for each of the seven
  nodes, an exact `H_<id> : Fin 9 → ℚ` vector equal to `y_<id> * E_<id>`
  componentwise. Each node now proves nine small `weighted_terms_<id> q`
  equalities and rewrites the final `strict_gain_<id>` sum to `∑ H`; the last
  `norm_num` performs only the nine-term rational addition and comparison.
- Added `Fin.sum_univ_succ` explicitly to the finite-sum proofs. The generator
  still fail-closes on the exact frozen constants, unit weights, nonnegative
  weights, and `T² - f0Lo - gain = strict_margin`.
- Attempted a local standalone elaboration in `/workspace/tools/mathlib-probe`.
  It timed out at 180 s with no diagnostic; the probe has only a top-level
  `Mathlib.olean` and is missing `Mathlib/Tactic/NormNum.olean`, so this is an
  environment/build-cache failure, not a Lean verdict. No full project build run.

Files / SHA256 (current bytes):
- `ops/lanes/C/emit_frozen_cap_rational_core.py`
  `FE80580DDBF2B2D0530373DAEB563E7583AED9717D897BBDDBEB24067A8D0ECF`
- `lean/N11Formalization/FrozenCapRationalCore.lean`
  `C48270A5017006F8276C4ECA4367DBA712EA405A965F3C8508F3FD34865B7A5A`
- `ops/lanes/C/TARGETS.txt` unchanged at
  `BED53B62E9339CEB40615595E1203AE8293C035B056C12EAAA582892564C18AD`

Checks run (scope stated):
- `py_compile` and emitter rerun: exit 0; all seven exact `Fraction`
  weight/unit-sum/margin checks passed. `git diff --check`: exit 0.
- Generated-module grep confirms `H_1409`, `weighted_terms_1409`, and the
  rewritten `strict_gain_1409`; the same block is emitted for all seven IDs.
- CI run `40803687450` (HEAD `7f7157f4`) remains `pending` with
  `total_count = 0` jobs, so there is still no kernel verdict.

Still unproved / missing:
- All 21 weight lemmas, seven strict-gain lemmas, and 63 weighted-term lemmas
  are **CI pending**, not paid. Endpoint bridges and packet hypotheses remain
  explicit. All 389 residual IDs remain unpaid; 382 lack public field records.

Very next concrete step: on the next lane-C CI attempt, inspect the first
`weighted_terms_<id>` diagnostic (the most likely place for a malformed `E`
vector). If green through `strict_gain_1409`, extend the same checked core to
the remaining six and remove their duplicated heavy proofs from
`FrozenCapCertificates`; if red, fix only that first declaration.

## 2026-10-29 — session part 18 (status + emitted-byte recheck)

Did:
- Re-ran the deterministic core emitter in this worktree. Exit 0; regenerated
  `lean/N11Formalization/FrozenCapRationalCore.lean` with unchanged SHA256
  `C48270A5017006F8276C4ECA4367DBA712EA405A965F3C8508F3FD34865B7A5A`.
- Emitter's exact `Fraction` checks again passed for all seven nodes (nonnegative
  and unit-sum weights, `H = y*E` componentwise, `F0 + sum H < T^2`, exact frozen
  strict margins). Pinned source hashes printed and unchanged: Leaf318
  `08F36489…F788A`, Trig `FB3DF66D…2A04C`, Bridge `C001704C…D9B1F8`.
- `python tools/project_status.py --check`: PASS (handoff navigation/manifest
  scope only). HEAD remains `7f7157f4`; `gh` is absent and the public GitHub API
  returns 404 for the remote, so this session obtained no new CI verdict.
- `git diff --check`: exit 0. No local Lean build attempted (probe oleans absent).

Still unproved / missing:
- The 21 weight, 63 weighted-term, and seven strict-gain declarations remain
  **CI pending**, not kernel-paid. Endpoint bridges and packet hypotheses remain
  explicit; all 389 residual IDs unpaid and 382 lack public source fields.

Very next concrete step: obtain the lane-C segment of the next CI log for HEAD
`7f7157f4` or newer and inspect the first `weighted_terms_1409`/`strict_gain_1409`
diagnostic; advance to `FrozenCapCertificates` bridging only after core green.
