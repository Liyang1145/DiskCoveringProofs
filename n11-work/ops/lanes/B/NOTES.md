# Lane B notes

Durable summary through session 143:
- B13 paid count is 1,997 (B12 815 + rest1182); refined residual is 373 of
  the frozen 389 after the sixteen certified removals; terminal count is 2,506.
- The old 5,982-line structural census OOMed CI.  It was replaced by a 26-line
  interface over a 20-block terminal census plus `ResidualCard`.
- Session 143 found and fixed a symbolic-`decide` defect in the terminal-census
  emitter.  No Lean module has yet been kernel-confirmed by CI in this chain.
- Run `41312076357` (head `20fd194b`, log SHA-256 `9B905880...ADF`) never reached
  lane B: lane C's `EnergyTerminalBatchB13RefineSixteenResidualCensus` started
  after 9,344 replayed dependencies and was killed on runner shutdown (143).
  This is an execution failure, not a lane-B Lean diagnostic.

## 2026-11-01 - session 144: narrow-first target order

- Reordered the first five entries of `n11-work/ops/lanes/B/TARGETS.txt` to
  `TerminalCensus`, `ResidualCard`, `StructuralCensus`, `Structural`, then
  `StructuralMain`.  This makes CI surface the 20-block census proof before
  either the cardinality bridge or any structural aggregate consumes it.
  `TARGETS.txt` SHA-256 is
  `CFDDDFDFAC1889E4670F0703213B44EE157C86C8BD7B97876240AF1EB8DBB0C8`.
- Preserved the independently generated sources unchanged:
  `emit_terminal_census_blocks.py` SHA-256
  `C9E27D22D96A985A65636FC73769B88D3093162CE16AC11227540434732BE862`;
  `EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean` SHA-256
  `A94B42CC22AF9A04029368EC31026E1C5C05172F022375C4C2D1F7231B6A0797`;
  `EnergyTerminalBatchB13RefineSixteenResidualCard.lean` SHA-256
  `5B6C7656FB3B71AE047498AE2DD45D235C57BA5467EA95DFD9EF8E4E7F55A340`.
- Re-ran `audit_target_imports.py` after the reorder: `ok=true`, closure 1,991,
  zero missing imports, zero forbidden tokens.  `audit_terminal_census.py`:
  `ok=true`, terminal 2,506, sharp 120, B13 paid 1,997, refined residual 373,
  exact terminal/sharp-paid/residual partition.  `audit_structural_dependency_
  isolation.py`: `ok=true`, 1,969 modules, no path to lane C's named OOM target.
  Scope is source/import and exact finite-set auditing only, **not Lean
  elaboration or kernel checking**.
- Local Lean remained unavailable as an authority: the installed Lean v4.33.1
  has no `--parse-only` option, the Mathlib dispatch probe timed out at 100 s,
  and the full project must not be built on this worker.  No Lean diagnostic was
  obtained; all five leading targets are **CI pending**.
- Still unproved: kernel acceptance of the terminal census, its `card_biUnion`
  bridge, `ResidualCard`, and the structural trio; all 373 residual radii;
  packet `f0Lo`/`g`; 382 absent payload records; SevenClassExclusions (`0/7`);
  the arbitrary-centre full-disk theorem.  No radius is paid by a cardinality
  result.
- ROOT-IMPORT REQUEST remains: replace `EnergyTerminalBatchB12Main` with
  `EnergyTerminalBatchB13Main` only after this lane chain is CI green.
- Next concrete step: the supervisor must remove or repair lane C's early
  `EnergyTerminalBatchB13RefineSixteenResidualCensus` target (outside lane-B
  write authority).  On the next CI run, read the first diagnostic from
  `TerminalCensus`; if elaboration is green, proceed to `ResidualCard`, else fix
  only `emit_terminal_census_blocks.py` and regenerate.

## 2026-11-01 - session 145: newest runner OOM attributed; census-block guard

- Downloaded the full job log for run `41318867156` (head `5dc953ab`, job
  `124884637589`): 22,657,790 bytes, SHA-256
  `C16354574B61EC33161B96445DA0B31E0333FD3FC81294B00D08E15958C32539`.
  Re-ran `audit_ci_log_progress.py`; its refreshed report SHA-256 is
  `D17B48C33255B08C16E276D35076E6FA67B48C864875873381A5DF5B012E17CD`.
- Exact scope: lane C ran six targets. Four exited 0. Lane C's four literal
  `EnergyTerminalResidualCensusC01..C04` children were killed with Lean exit
  137, so `EnergyTerminalBatchB13RefineSixteenResidualCensus` exited 1; its
  `ResidualCensusMain` then began after 5,728 replayed dependencies, reached
  ~7.7 GB RSS, and was killed when the OOM guard fired (`avail` below 900 MB),
  ending in runner shutdown/exit 143. **No lane-B target started.** This is an
  execution/OOM failure, not a lane-B Lean diagnostic or proof result.
- Added `audit_terminal_census_blocks.py` (SHA-256
  `6D269CF39F93598A3D057AF51AEBCB008CD3BDDD12109075C9044EDF2BFB4FFA`)
  and `audit_terminal_census_blocks-report.json` (SHA-256
  `BAE48DE371FB4322128FDA06E16FED0A14A66D1643AFBC46B06646E9D4000FFF`).
  It statically verifies the generated terminal census has 20 contiguous
  blocks (nineteen of width 256, final 147), all 190 pairwise disjointness
  facts, both dispatcher orientations (380 calls), literal/block card equality,
  card sum 2,506, and both top-level 2,506 theorems. Result: `ok=true`; audited
  Lean source SHA-256 `A94B42CC22AF9A04029368EC31026E1C5C05172F022375C4C2D1F7231B6A0797`.
- Re-ran `audit_terminal_census.py`, `audit_target_imports.py`,
  `audit_structural_dependency_isolation.py`, and `audit_census_blocks.py`.
  All returned `ok=true`: terminal/sharp/B12/rest/B13/residual
  `2506/120/815/1182/1997/389`, refined residual 373 with exact partition;
  target closure 1,991 with no missing imports or forbidden tokens; structural
  closure does not reach the named lane-C OOM module. Scope remains static
  source/import and exact finite-set arithmetic, **not elaboration or kernel
  checking**.
- Still unproved/unpaid: kernel acceptance of `TerminalCensus`, `ResidualCard`,
  the structural trio and subsequent lane-B targets; all 373 residual radii;
  packet `f0Lo`/`g`; 382 absent payload records; SevenClassExclusions `0/7`;
  and the arbitrary-centre full-disk theorem. No radius is paid by this work.
- Next concrete step: supervisor must remove/reorder lane C's
  `EnergyTerminalResidualCensusC01..C04`/`ResidualCensus`/`ResidualCensusMain`
  targets so CI reaches lane B. Then inspect `TerminalCensus` first; if it is
  red, fix only its emitter and rerun the new block audit before regeneration.

## 2026-11-01 - session 146: terminal-census regression guard

- Hardened `emit_terminal_census_blocks.py` (SHA-256
  `08D9D46B535B57C6E96D7CFB284A0838EB8A0CAB5A2C347FF410EDA20FEB0AB0`)
  so emission fails unless every one of the 20 `census*` definitions filters
  its own correctly sized `embed*`, and every `census*_spec` is the structural
  `simp only` proof introduced in session 143.  This prevents a silent return
  to a symbolic `decide +kernel` proof or a wrong-block filter.
- Strengthened `audit_terminal_census_blocks.py` (SHA-256
  `A1570B70F3B2535B18A78E5538FB519AEA119B188AB6CC49ED0C6167562D9A38`)
  with `twenty_filtered_census_definitions` and
  `twenty_structural_census_specs`.  Regenerated the module, which remained
  byte-identical at SHA-256
  `A94B42CC22AF9A04029368EC31026E1C5C05172F022375C4C2D1F7231B6A0797`.
- Reran the block audit: all 11 checks `ok=true`, 20 blocks with widths
  nineteen 256 plus 147, 190 pairwise facts dispatched in both orders, exact
  cardinality sum 2,506.  Refreshed report SHA-256
  `38AF336EB0D4B222B668F4EC2AF6986CC8F5FBE20A8F1A45EC2FCAACE7F643AB`.
  Also reran `audit_terminal_census.py`: `ok=true` with terminal/sharp/B12/
  rest/B13/residual `2506/120/815/1182/1997/389` and refined residual 373
  partitioned exactly.  Scope is static generated-source auditing, **not Lean
  elaboration or kernel checking**.
- A Mathlib-only probe of the `fin_cases <;> fin_cases <;> first | ...`
  dispatcher could not import Mathlib within bounded local limits; it produced
  no Lean diagnostic.  The dispatcher therefore remains **CI pending**.
- Still unproved/unpaid: kernel acceptance of `TerminalCensus`, `ResidualCard`,
  the structural trio and later lane-B targets; 373 residual radii; packet
  `f0Lo`/`g`; 382 absent payload records; SevenClassExclusions `0/7`; and the
  arbitrary-centre full-disk theorem.  No radius is paid.
- Next concrete step: supervisor must reorder/remove lane C's early residual
  census targets so CI starts lane B with `TerminalCensus`; read that first
  diagnostic before changing the 256-point blocks or regenerating again.
