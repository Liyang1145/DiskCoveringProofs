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

- Serial conditional census chain 389->334: parts 202-290 emitted `emit_census_*.py`
  + `EnergyTerminalResidualCensusRefine{350,...,334}.lean`, each removing green ids
  exactly (card 389->334, 55 removed), always a conditional B13 map, no payment.
  Static `verify_census_*.py` PASS; **CI pending** throughout.
- Low-id repair: `EnergyRefineN0039Repair` restored; `repair_refine_0039_40.py`,
  `repair_census_membership_chains.py`; `False.elim` for false leaves, 25-block Next505
  nonmembership, namespace `N0040`.
- 336->334 added archive drafts 3578/3738 (byte-restored minus the banned unbounded-
  heartbeat directive) + conditional wrapper/Main triples; TARGETS orders them after 336.
- Inventory: 773 files, 7 public payloads, 382 missing, 62/389 ids complete source,
  327 source-missing. No host-side audit or byte check is kernel credit.
- Unproved remains: CI through 334, all 334 radius certificates, canonical/geometric
  packet production, MPacket validity, SevenClassExclusions, arbitrary-centre theorem.


## 2026-11-03 - parts 291-295 (condensed)

- CI `41449154413`/`41656715257`/`41706645384` all `cancelled`; stored
  `LATEST.md` = run `41706645384` (sha `bd5573e5`). Exit map: `CensusBase`=0,
  but `C01`,`C02`,`C03`,`C04`=1 and every consumer (`Census`, `Refine0039*`,
  `Refine0037Refine3149`, `RefineSixteen*Census*`) =1; the rest of the
  ~200 lane-C targets are 0. So C01-C04 are the owning reds.
- Static checks: the four `chunk0..chunk3` literals (100/100/100/89) match
  `residual389-census.json` exactly (`verify_census_334.py` PASS; part-293).
  `C01..C04` tile the 51 blocks `[100NN,100NN+100)` covering `[0,5011)`.
  `mem_iff_blockNN` closes with `rw [B13.mem_residualIDs_iff] <;>
  decide +kernel +revert`, so the kernel must decide `(data n).terminal`
  (4 MB `data` def) plus `n ∉ paidIDs` (`B12 ∪ Next1182`, ~1997 literals)
  for all 5011 indices - a per-declaration accumulation that violates the
  GUIDANCE kernel-scale rule (~170-500 literals) and is the likely exit-1
  cause. Memory in the cancelled run grew to ~11.9 GB (later Refine352).
- Probe `/workspace/tools/mathlib-probe` cannot even load `import Mathlib`
  inside 190 s (`rc=124`), so local kernel-scale bisection is INFEASIBLE.
- No exit-code/error text is stored for C01-C04 (`LATEST.md` keeps only a
  build-log tail), so the fix must be robust to heartbeat AND memory.
- Unchanged: no id paid; 334 bridge conditional only.

## 2026-11-03 - part 296 (C01-C04 rewritten: per-index kernel isolation)

Re-read GUIDANCE/LANES/C-NOTES/LATEST (run `41706645384`, sha `bd5573e5`).
Lane-C reds are exactly `C01..C04` plus their consumers; `CensusBase` is green.

Action (new emitter `n11-work/ops/lanes/C/emit_census_c01_c04.py`, deterministic,
self-checking): regenerated the four modules so that each source index gets its
own theorem `mem_iff_id_<id>` (5011 total) with a single `decide +kernel +revert`
in its own declaration (its own heartbeat budget). Each `mem_iff_blockNN` now
covers 100 indices but delegates to those per-index lemmas via explicit bullets
(`interval_cases k` then `exact mem_iff_id_<id> _ rfl`), so NO declaration
accumulates 100 heavy kernel decisions. Per-index proof shape:
`rcases n with ⟨k,hk⟩; change k = <id> at hn; subst hn;
rw [B13.mem_residualIDs_iff]; decide +kernel +revert`. Exported interface
(`mem_iff_block00..50`, signature `(n) (hlo) (hhi)`) is UNCHANGED, so
`EnergyTerminalResidualCensus.lean` needs no edit. Only C01-C04 touched; Base,
assembly, root, lakefile, toolchain, frozen modules untouched.

Files: `n11-work/lean/N11Formalization/EnergyTerminalResidualCensusC0{1,2,3,4}.lean`
(now ~386/386/360/356 KB), `n11-work/ops/lanes/C/emit_census_c01_c04.py`.
Checks (scope: source/static only, NOT elaboration or kernel credit):
- emitter self-check: 13+13+13+12 blocks, 5011 unique ids, total = 5011.
- independent parse: ids = 0..5010 exactly (no dup/gap); 51 blocks; each block
  bullet list == `range(100*b, min(100*b+100,5011))`; STRUCTURE OK.
- forbidden-token scan of the four files: none (no sorry/admit/axiom/
  native_decide/ofReduceBool/implemented_by/maxHeartbeats).
- `TARGETS.txt` already lists C01-C04 (parts-293 edit); unchanged.

Scope/limits: this is a scale/robustness repair, not a proof of new
mathematics; the per-index `decide` still unfolds `data` and `paidIDs` once
per index. **CI pending** (sha will be the supervisor commit): C01-C04 and all
downstream consumers (Census, Refine0039*, Refine0037Refine3149,
RefineSixteen*Census*) must go exit 0 with axioms
`[propext, Classical.choice, Quot.sound]`. If a per-index `decide` itself is
still red, the next step is the part-295 hierarchical `mem_paidIDs_iff` split
(`mem_union`/`new_mem`/`fin_cases`) so no single decision sees the 1997-literal
`paidIDs`, and, for `data`, precompute a `terminalIDs` literal lemma.

Still unproved (unchanged, nothing here is kernel credit): CI green for
C01-C04 + assembly; the 7 red Refine0039/RefineSixteen/Refine385 modules; all
residual radius certificates; 327 source-missing ids; canonical/geometric
packet production; MPacket validity; SevenClassExclusions; arbitrary-centre
theorem. Next concrete step: after CI, if C01-C04 are green, mark lane-C
TARGET-DONE; if still red, read the first owning error line and apply the
hierarchical paidIDs/data split above.

## 2026-11-04 - part 297 (independent C01-C04 structure audit)

Re-read GUIDANCE/LANES/C-NOTES/LATEST (run `41706645384`, sha `bd5573e5`);
part-296 per-index split is on disk (uncommitted; C01-C04 ~370-400 KB,
`emit_census_c01_c04.py` present) but CI has NOT re-run, so C01-C04 remain
**CI pending** (last stored exits were 1 for C01-C04 + consumers).

Action: committed an INDEPENDENT static verifier (separate from the emitter's
own self-check, per the EXPERT note asking for an independent check)
`n11-work/ops/lanes/C/verify_census_c01_c04.py`. It parses the four generated
modules and checks, from source text only:
- `mem_iff_id_<id>` theorems exist for exactly ids 0..5010, unique, no gap;
  each theorem's name matches its declared `n.val = <id>`;
- each `mem_iff_blockNN` has interval `[100*NN, min(100*NN+100,5011))` and its
  bullets reference exactly the ids of that interval (5011 ids total, 51 blocks);
- consumer `EnergyTerminalResidualCensus.lean` references `mem_iff_block00..50`
  exactly once each (interface unchanged);
- forbidden-token scan (sorry/admit/axiom/native_decide/ofReduceBool/
  implemented_by/maxHeartbeats; `#print axioms` lines excluded, `axiom` matched
  word-bounded).

Check result: `python3 verify_census_c01_c04.py` -> `PASS  per-index ids: 5011
(0..5010); blocks: 51; consumer: 51 calls; forbidden tokens: none`.
Scope: SOURCE-LEVEL STRUCTURE ONLY, not elaboration and not kernel credit.

Still unproved (unchanged, nothing here is kernel credit): CI green for C01-C04
+ the red consumers (`Census`, `Refine0039*`, `Refine0037Refine3149`,
`RefineSixteen*Census*`); the 7 red Refine0039/RefineSixteen/Refine385 modules;
all residual radius certificates; 327 source-missing ids; canonical/geometric
packet production; MPacket validity; SevenClassExclusions; arbitrary-centre
root theorem.

Very next concrete step: after the supervisor commits and CI runs, read the
first owning error line for C01. If green -> mark lane-C TARGET-DONE. If still
red with a kernel/`decide` blowup, apply the part-295 hierarchical split:
replace the single `decide +kernel` on `n ∈ EnergyTerminalBatchB13.residualIDs`
with `EnergyTerminalBatchB13.mem_residualIDs_iff` decomposed structurally --
`Paid16GeneralNext1182.new_mem` (8-way disjunction) + per-part `mem`/interval
lemmas + B12 split -- so no `decide` ever sees the 1997-literal `paidIDs`; keep
`decide +kernel` only for `(DBMSourceTree.data n).terminal` and `sharpIDs`.
