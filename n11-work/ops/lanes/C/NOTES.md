EXPERT (2026-11-02):
- Actual energy remains 2013/2386 (373 open). The 389->334 chain is conditional set algebra, not 55 paid ids; do not quote 334/332 as paid.
- Stop adding census links. 232 serial targets cannot reliably reach the tail in the 5-hour CI budget; park 3578/3738 and later links.
- The 334 note overclaims static PASS: there is no committed `verify_census_334.py` or audit JSON. Add that independent exact-complement check.
- Highest leverage: make `EnergyRefineN0038` real, then the wrapper and `ResidualRadiusCertificate 38`; require `new_radius` and `paid_radius` green with clean axioms.
- Removing `maxHeartbeats 0` is not a repair: drafts retain `maxRecDepth 100000` and 12-13 KB rational literals with 13-36 giant `decide +kernel` checks.
- Split each `validN : MValid pkN` by the eight `MValid` fields and packet leaves: `fin_cases` over `Fin 16/36/9/7`, then exact `norm_num` on closed comparisons.
- Gate one id per CI cycle, smallest first (0038), and preserve the first owning error; no further bridge until one id is paid.
- Keep the original root and toolchain untouched; this lane earns energy credit only through the B13 consumer.

# Lane C notes

## Standing constraints

- Kernel credit requires CI exit 0 and a mathematical consumer. Exact rational
  audits, static scans, and hash/tree audits are diagnostics only.
- No `sorry`/`admit`/new `axiom`/`native_decide`/`ofReduceBool`/
  `implemented_by`/`maxHeartbeats 0`; do not edit frozen modules, root,
  lakefile, toolchain, or manifest.
- Preserve green `FrozenCapRationalCore`, `PaidCellCertificateM`,
  `PaidCellCertificateMCap`, and `FrozenCapWideFieldWitnesses` unchanged.
- `ExcludedTree` is not a bridge to `RemainingTerminalRadius`; it pays no id.
- Scan forbidden tokens without relying on `\b` under POSIX `rg`.

## Condensed history

- The frozen B13 census is terminal - sharp - 1997 paid = 389 ids. Only seven
  ids have public tree payloads; the other 382 are absent. Row caps exclude
  those seven for any row count, so wider LP work cannot rescue them. No id paid.
- CI `41201323694` is green for `RefineFourteen` (`paid_count = 2011`) and
  `RefineFourteenMain`. `41217409382` is green for `RefineSixteenRepair`,
  `RefineSixteenResidual`, `RefineSixteen`, and `RefineSixteenMain`, leaving a
  373-id conditional residual. Those interfaces are equivalences, not payments.
- Earlier census failures were proof-encoding, not false ids. Large literal
  `decide +kernel` blocks exceeded kernel limits; cardinality is now structural.
- Missing throughout: radius certificates for the 373 residual ids;
  canonical/geometric packet production; 382 non-public payloads; MPacket
  validity; seven-class and energy premises; root integration.
- No historical host-side audit or byte check is kernel credit.

## 2026-10-31/11-02 - parts 202-290 (condensed)

- Conditional census chain 389->334 (`emit_census_*.py`,
  `EnergyTerminalResidualCensusRefine{350,...,334}.lean`): 55 green ids removed as a
  conditional B13 map, no payment; static verifiers PASS, **CI pending**. Low-id
  repair `EnergyRefineN0039Repair`; archive drafts 3578/3738 + wrappers. Inventory:
  773 files, 7 public payloads, 382 missing, 62/389 source-complete. No id paid.

## 2026-11-03 - parts 291-295 (condensed)

- CI `41449154413`/`41656715257`/`41706645384` `cancelled`; stored run
  `41706645384` (sha `bd5573e5`) exit map: `CensusBase`=0, `C01`-`C04`=1, all
  consumers=1, rest of ~200 lane-C targets 0 -> C01-C04 are the owning reds.
  `chunk0..3` (100/100/100/89) match `residual389-census.json` (static PASS).
  Local bisection INFEASIBLE (`import Mathlib` > 190 s in the probe). No id paid.

## 2026-11-03/04 - parts 296-303 (condensed; C01-C04 kernel hardening)

- parts 296-299: split each 100-index block into 5011 per-index theorems
  `mem_iff_id_<id>` (`emit_census_c01_c04.py`), each a single closed
  `decide +kernel`; block lemmas delegate via `interval_cases` + bullets.
  Interface `mem_iff_blockNN`, the 51 consumer calls, `chunk0..chunk3`
  unchanged. Independent static verifier `verify_census_c01_c04.py` PASSes the
  exact-complement check vs `residual389-census.json` (SOURCE-LEVEL only).
- part 299: real CI log (run `41769569707`) showed the owning error = heartbeat
  timeout at `decide +kernel +revert` for TERMINAL ids only; cause = kernel
  reducing the `Finset.union` *value* `s - t + t` over the full ~1997-id paid
  set (non-terminal ids short-circuited on `(data n).terminal = false`).
- parts 301/302: `simp only` with `Finset.mem_union/mem_insert/mem_singleton`
  splits every paid-chain `∪` into literal atoms BEFORE `decide`; per-index
  goal closed with `Fin.ext hn` + `subst` (no `+revert`).
- part 303: same for the CENSUS side -- added `CENSUS_SIMP =
  [residualIDs, chunk0..chunk3]` so `n ∈ residualIDs` is also split.
- Probe tooling dead-end (do NOT repeat): `/workspace/tools/mathlib-probe` has
  NO built Mathlib oleans (`import Mathlib` = local prelude stub; `Finset.Basic`
  missing). Local Lean validation impossible; CI is the only authority.


## 2026-11-03/04 - parts 296-299 (condensed)

- Part 296 rewrote C01-C04 so each source index gets its own theorem
  `mem_iff_id_<id>` (5011 total) with one `decide +kernel +revert`; each
  `mem_iff_blockNN` delegates via `interval_cases` + `exact mem_iff_id_<id> _ rfl`.
  Interface `mem_iff_block00..50` UNCHANGED. Emitter `emit_census_c01_c04.py`.
- Part 297 added independent static verifier `verify_census_c01_c04.py`.
  Part 298 extended it with the exact-complement check (chunk literals ==
  `residual389-census.json` `residual_ids[0:100]/[100:200]/[200:300]/[300:389]`,
  sorted/dedup, union == 389, `counts.residual == len`). Result:
  `PASS  per-index ids: 5011 (0..5010); blocks: 51; consumer: 51 calls;
  forbidden tokens: none`. Scope: SOURCE-LEVEL STRUCTURE ONLY.
- Part 299 fetched the REAL CI job log for run `41769569707` (sha `da6f0ed3`,
  conclusion failure, 2h51m). Exact owning error (C01, same form C02-C04):
  repeated `(deterministic) timeout at whnf, maximum number of heartbeats
  (200000)` at the `decide +kernel +revert` line of `mem_iff_id_KKKK`, hitting
  exactly the TERMINAL ids. Non-terminal ids pass (`Decidable.and` short-circuits
  at `(data n).terminal = false`). Cause: `Finset.union` value is
  `s - t + t` (`Mathlib/Data/Multiset/UnionInter.lean:45`), so deciding
  `n ∈ paidIDs` (~1997 nested literals) forces ~10^6 diff comparisons. NOT a
  false id, NOT per-index cost per se: the union *value* reduction is the blowup.

## 2026-11-05 - part 304 (CI-failure re-attribution; simp-coverage audit)

State on entry: worktree HEAD `7fe98db8`; uncommitted = part-303 C01-C04 +
`emit_census_c01_c04.py` + this NOTES (the part-303 fix is NOT yet CI-checked).

New concrete finding (`ops/ci/LATEST.md`, run `41847982412`, sha `6e67ed3a`):
that run failed in TWO distinct ways. (a) `summary.json` still lists
`EnergyTerminalResidualCensusC01..C04` exit `1` (elaboration error, not 137).
(b) the *build log tail* shows the ROOT build reaching
`[10725/10727] Building N11Formalization.SharedMomentConcreteSwitchBatch
(1002s)` then `OOM-GUARD killing lean (avail=722MB)` / `error: Lean exited
with code 137` / `=== EXIT N11Formalization 1`. So the run's overall failure is
an OOM in a lane-C-unrelated frozen-sized module, NOT the C01 heartbeat; no
per-module C01 error line is stored anywhere readable.

Simp-coverage audit (static): after the part-303 simp the paid side decomposes
to ~101 leaf `Finset` atoms -- `Paid16GeneralG01..G12.newIDs` (`univ.image
nodeID`, 21 elts; NOT unfolded), `Paid16GeneralNext505.ids00..24`,
`Paid16GeneralNext1182S01..S08.ids00..07` -- because every UNION def
(`B01..B13`, `First42`, `Remaining210`, `Next505`, `Next1182` via `new_mem`,
`S01..S08`) is in the simp list while the image/leaf defs are not. Hence the
kernel `decide` now sees `n = i`-substituted `∨`-trees of small closed
`Finset.mem` atoms (<=168 elts each), with `not_or` pushing the `∉ paidIDs`
complement, instead of a `s - t + t` union *value* over 1997 ids. Residual
risk is therefore elaboration/simp recursion depth over ~2400 literals per
per-index theorem (5011 of them), not the multiset-diff kernel blowup.

Checks run (scope): re-ran `python3 emit_census_c01_c04.py` -> rc 0, self-check
5011, output byte-identical (git diff unchanged: only 4 C01-C04 + emitter);
`python3 verify_census_c01_c04.py` -> `PASS  per-index ids: 5011 (0..5010);
blocks: 51; consumer: 51 calls; chunks==census (389); forbidden tokens: none`
(SOURCE-LEVEL STRUCTURE + exact-complement only). No Lean built locally (2
cores; probe has no Mathlib oleans), no CI triggered, no new files (FOCUS
mode). Nothing here is kernel credit.

Still unproved: CI green for C01-C04 and the 11 red census consumers; all 389
residual radius certificates; 382 non-public payloads; MPacket validity;
SevenClassExclusions; arbitrary-centre root theorem. Also unpaid (not lane C):
the root-build OOM on `SharedMomentConcreteSwitchBatch`.

Very next concrete step: request ONE CI cycle and read the FIRST owning C01
error. If it is a heartbeat at the `decide +kernel` line, the remaining heavy
atom is `(DBMSourceTree.data (i:Fin 5011)).terminal = true` (or `sharpIDs`),
not the paid set: split that atom off and decide it in its own small lemma. Do
not claim green until the job log shows exit 0 for C01-C04 with axioms
`[propext, Classical.choice, Quot.sound]`.
