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

## 2026-11-03 - part 296 (C01-C04 rewritten: per-index kernel isolation)

Part 296 rewrote C01-C04 so each source index gets its own theorem
`mem_iff_id_<id>` (5011 total) with one `decide +kernel +revert` in its own
declaration; each `mem_iff_blockNN` delegates to 100 per-index lemmas via
`interval_cases k` + `exact mem_iff_id_<id> _ rfl`. Interface
(`mem_iff_block00..50`) UNCHANGED. Emitter `emit_census_c01_c04.py`; only
C01-C04 touched. Static checks (source only): 5011 unique ids, 51 blocks,
bullet lists == `range(100*b, min(100*b+100,5011))`, STRUCTURE OK. Part 299
below shows this was still **CI red** (whnf heartbeat timeouts).

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

## 2026-11-04 - part 298 (independent exact-complement check)

Re-read GUIDANCE/LANES/C-NOTES/LATEST. Key correction of my earlier reading:
the stored CI run `41706645384` (sha `bd5573e5`) is dated 2026-11-03T19:48Z,
BEFORE the part-296 per-index split commit (`da6f0ed3`, 2026-11-04 03:47). So
its exit map (C01-C04 = 1, plus the red consumers) is the PRE-part-296 state;
part-296 is **CI pending**, not confirmed red. Its build tail shows lane C
still reaching `EnergyTerminalResidualCensusRefine352` at ~11.9 GB before the
run was cancelled, i.e. the serial 232-target load + memory is itself a risk.

Action this session: extended the independent verifier
`n11-work/ops/lanes/C/verify_census_c01_c04.py` (existing lane-C file, no new
Lean modules) with the exact-complement check the EXPERT asked for. It now
parses the four `chunkN` literals out of
`n11-work/lean/N11Formalization/EnergyTerminalResidualCensusBase.lean` and,
independently of the emitter, asserts:
- `chunk0..3` equal `residual389-census.json` `residual_ids[0:100]/[100:200]/
  [200:300]/[300:389]` exactly (as ordered lists);
- `residual_ids` is strictly sorted and duplicate-free;
- the four-chunk union equals the census `residual_ids` (389) and the chunk
  total has no overlap (389);
- `counts.residual == len(residual_ids)`;
- (retained) per-index ids 0..5010 exactly once; 51 blocks with the right
  intervals/bullets; consumer calls block00..50 once; forbidden-token scan.

Check result: `cd n11-work/ops/lanes/C && python3 verify_census_c01_c04.py` ->
`PASS  per-index ids: 5011 (0..5010); blocks: 51; consumer: 51 calls;
chunks==census (389); forbidden tokens: none` (rc=0). Scope: SOURCE-LEVEL
EXACT-COMPLEMENT + STRUCTURE ONLY -- not elaboration, not kernel credit. This
closes the "no committed independent exact-complement check" gap for the
chunk literals; it does NOT pay any id.

Kernel-scale diagnosis (unchanged, unproved locally): each `mem_iff_id_KKKK`
still runs one `decide +kernel +revert` over `(data KKKK).terminal ∧
KKKK ∉ sharpIDs ∧ KKKK ∉ paidIDs`; the `paidIDs` union has 1997 literals and
`data` is the 4 MB source table, so per-declaration cost is still above the
GUIDANCE ~170-500-literal bound for the ~2506 terminal indices. Local bisection
is infeasible (`import Mathlib` > 190 s in the probe). CI is the authority.

Still unproved (nothing here is kernel credit): CI green for C01-C04 + the red
consumers (`Census`, `Refine0039*`, `Refine0037Refine3149`,
`RefineSixteen*Census*`); the 7 red Refine0039/RefineSixteen/Refine385 modules;
all 389 residual radius certificates; 327 source-missing ids;
canonical/geometric packet production; MPacket validity; SevenClassExclusions;
arbitrary-centre root theorem.

Very next concrete step (unchanged priority): once CI runs on the committed
part-296 + part-298 state, read the FIRST owning error line for C01. If green ->
mark lane-C TARGET-DONE. If still red on kernel/`decide`, apply the part-295
hierarchical split to the per-index proof: replace the single decide on
`n ∈ EnergyTerminalBatchB13.residualIDs` with a structural conjunction --
`Paid16GeneralNext1182.new_mem` (8-way disjunction) + per-part interval `mem`
lemmas + B12 split for `n ∉ paidIDs`, and a precomputed literal `terminalIDs`
lemma for `(data n).terminal` -- so no `decide` ever sees the 1997-literal
`paidIDs` or re-unfolds `data` per index.

## 2026-11-04 - part 299 (read the real CI log; exact owning error)

Re-read GUIDANCE/LANES/C-NOTES/LATEST. Fetched the ACTUAL `n11-lean-build` job
log for run `41769569707` (sha `da6f0ed3`, the part-296 commit) from the GitHub
API (`/actions/jobs/126375831147/logs`, ~25 MB; repo
`Liyang1145/DiskCoveringProofs`). Job conclusion: **failure** after 2h51m.
This replaces the guesswork in parts 295/297/298. (`LATEST.md` still showed
that run as `in_progress` and its stored summary.json was the PRE-part-296 run
`bd5573e5`; a newer run `41787355746` also failed on sha `25c66cd6`.)

Exact owning error, C01 (C02-C04 identical in form): repeated
`error: .../EnergyTerminalResidualCensusC01.lean:<line>:0: (deterministic)
timeout at whnf, maximum number of heartbeats (200000) has been reached` at the
`decide +kernel +revert` line of each `mem_iff_id_KKKK`. So the part-296
per-index split did NOT fix C01-C04: they are still **CI red**.

Failing-id pattern (C01): timeouts hit exactly `mem_iff_id_{0003,0005,0009,
...}` i.e. the TERMINAL source ids; the non-terminal ids (0000,0001,0002,0004,
0006,0007,0008,...) pass. Cause: after
`rw [EnergyTerminalBatchB13.mem_residualIDs_iff]` the goal RHS is
`(data n).terminal = true ∧ n ∉ sharpIDs ∧ n ∉ paidIDs`; `Decidable.and`
short-circuits, so non-terminal ids stop at `(data n).terminal = false` and
never touch `paidIDs`, while terminal ids must kernel-decide `n ∉ paidIDs`
(`paidIDs = B11.paidIDs ∪ Next505.newIDs`, `B12.paidIDs ∪ Next1182.newIDs`,
~1997 literal ids) and `n ∉ sharpIDs`. Verified in the probe's Mathlib
(`Mathlib/Data/Multiset/UnionInter.lean:45`): `Multiset.union s t := s - t + t`
(difference then append), and `Finset.union`'s val is that multiset union; so a
kernel `decide` of `n ∈ paidIDs` forces the quadratic differences/erases of the
nested unions (~1997^2 comparisons) -> whnf heartbeat exhaustion. Not a false
id, and not the per-index cost per se: the union *value* reduction is the blowup.

Concrete fix (next session; emitter change only, no new Lean families): stop
letting `decide` unfold `Finset.union`. Decompose membership structurally with
the already-green, already-existing pattern of
`EnergyTerminalBatchB13Refine0039.lean` (exit 0): `Finset.mem_union` for the
B12/B13 unions, `Paid16GeneralNext1182.new_mem` (8-way) + per-sub
`Paid16GeneralNext1182S0X.new_mem` / `mem_idsKK`, and the interval-bound lemmas
(`block_s01_00_bounds : 2565 ≤ n.val ≤ 2585`; the parts are consecutive
intervals; Next505 is "bounded below 2565"). Emit, per terminal index, a
`not_paid_*` / `mem_paid_*` lemma list, then a `decide +kernel` only on the
resulting atomic `n = c` / Bool comparisons (<= ~168 literals each).
Short-circuit non-terminal ids by proving `(data n).terminal = false` first.
Keep the `Census.residualIDs` literal chunks unchanged.

Checks run this session (scope noted): `git log`/`git status` (tree clean);
fetched and grepped the real job log (authoritative for exits of run
`41769569707`); no Lean build run locally (2 cores; `import Mathlib` > 190 s in
`/workspace/tools/mathlib-probe`). No files edited except this NOTES entry.
`verify_census_c01_c04.py` not re-run (no source change). Nothing here is
kernel credit.

Still unproved (unchanged): CI green for C01-C04 + the red consumers
(`Census`, `Refine0039*`, `Refine0037Refine3149`, `RefineSixteen*Census*`);
all 389 residual radius certificates; 327 source-missing ids;
canonical/geometric packet production; MPacket validity; SevenClassExclusions;
arbitrary-centre root theorem.

Very next concrete step: edit `n11-work/ops/lanes/C/emit_census_c01_c04.py` to
emit the structural `not_paid`/`mem_paid` decomposition above (reusing the
Refine0039 lemma names), regenerate C01-C04, re-run
`verify_census_c01_c04.py`, keep C01-C04 in `TARGETS.txt`, and request a CI
cycle. Do not claim green until the job log shows exit 0 for all four with
axioms `[propext, Classical.choice, Quot.sound]`.
