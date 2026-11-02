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

## 2026-11-01 sessions 144-147: census construction and decoupling

- Established B13 paid 1,997, refined residual 373/389, terminal 2,506.
  The original structural census OOMed CI; it was replaced by bounded blocks.
- Sessions 146-147 added a 20-block terminal-census guard and separated
  `ResidualCard` from the old 389 residual census.  Diagnostics and reports
  from those sessions were superseded by the session 148 rewrite below.
- All older source hashes remain recoverable from git history; no radius was
  paid by any cardinality result.

## 2026-11-02 - session 148: exact CI diagnosis and census rewrite

- Retrieved run `41352871085` (head `b1e15e83`, job `124986627384`).  The
  workflow reports job success only because its build script ends with `true`;
  target exits are authoritative.  Earlier lane-B prerequisites are CI green:
  `Paid16GeneralNext1182`, `Next505Bounds`, `DescentBounds`, `B13`, `B13Main`,
  `RefineSixteen`, and `RefineSixteenMain` all exited 0.  Exact evidence is in
  `ci-verdict-41352871085.json` (SHA-256
  `29A72CA2243E0390841F1F8861F62B06FE39AC11F59D7F76BEEEE4083D37FC79`).
- The first red node is `TerminalCensus` (exit 1).  Its diagnostics were all
  emitter defects: 20 upper-bound `simp` goals missing `omega`; `block_mem0`
  running `omega` after `simp` had closed the goal; 20 witnesses comparing
  `blockIDSi` with opaque `blockIDs ⟨i, _⟩`; vector-index `whnf` timeouts; the
  400-alternative `first` dispatcher exceeding recursion depth; and the
  `Fin 20` block-cardinality sum not being normalized.  `ResidualCard` and the
  structural trio only replayed these dependency errors.
- Rewrote only the lane-B emitter
  `emit_terminal_census_blocks.py` (SHA-256
  `E1295BDA417459AD7E58C4B5C36D845A69CB340E57150DFB71DB1BE435CA2A28`)
  and regenerated
  `EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean` (SHA-256
  `0FDEEAEC2EB0816A25566DBE3DB27FD194B9B633757CA485A8F6EF6A0D3BFBA0`).
  The output shrank from 2,995 to 1,274 lines.  It now uses 20 literal
  contiguous interval facts, one `Fin 20` interval dispatcher, and a single
  order proof for all 190 unordered block pairs; it no longer contains 190
  separate disjointness theorems or `fin_cases <;> fin_cases <;> first`.
  Membership witnesses are closed by `simpa [blockIDs]`; the cardinality sum
  uses `Fin.sum_univ_succ` recursively.
- Strengthened `audit_terminal_census_blocks.py` (SHA-256
  `1A75D24919F4255AA676A900E42D9EBDCB51F2EECF235D9C3F562D97DC24E3032`)
  to check the 20 interval facts, the 20-case generic dispatcher, the
  interval-order pairwise proof, forbidden absence of the old
  `fin_cases <;> fin_cases` scheme, and exact 2,506 cardinality data.  Report
  `audit_terminal_census_blocks-report.json` (SHA-256
  `04BDEC4DB93D7B24F2A5354331A89DAC8B11B974A7B927B45A6B5EBC369A285B`)
  has `ok=true`: 20 contiguous blocks (nineteen 256, final 147), literal card
  sum 2,506, source SHA `0FDEEAEC...FBA0`.  Scope is static source auditing,
  **not Lean elaboration or kernel checking**.
- Re-ran `audit_terminal_census.py`: `ok=true`, partition exact at
  terminal/sharp/B12/rest/B13/residual = `2506/120/815/1182/1997/389`, with
  refined residual 373.  Re-ran `audit_target_imports.py`: `ok=true`, import
  closure 1,990, zero missing imports, zero forbidden tokens.  These remain
  source/import audits only, not Lean elaboration.
- No local Lean build was run: the worker's `.lake/build/lib/lean` is absent,
  and the full project must not be built locally.  The rewritten
  `TerminalCensus` is unambiguously **CI pending**.  `ResidualCard`, the
  structural trio, all 373 residual radii, packet `f0Lo`/`g`, 382 absent
  payload records, SevenClassExclusions (`0/7`), and the arbitrary-centre
  full-disk theorem remain unproved/unpaid.  No radius is paid.
- The run also exposed `LaneBPublicResidualCrosswalk` exit 1 from the unrelated
  superseded `EnergyTerminalResidualCensusC01` timeout/deep-recursion path.
  It should be removed from the target list or ported off that import; it is
  not evidence against this census rewrite.
- Next concrete step: supervisor pushes and runs CI; inspect
  `TerminalCensus` first at SHA `0FDEEAEC...FBA0`.  If green, inspect
  `ResidualCard`; if red, do not change the census, fix only ResidualCard's
  local bridge.  In parallel, drop/port the stale public-crosswalk target so
  it cannot consume another 15-minute interval.

## 2026-11-02 - session 149: final-block dispatcher repair

- Found a concrete elaboration mismatch in the session-148 census: the generic
  `blockIDs_interval` pads block 19 to `[4864,5120)`, but the generated final
  fact stopped at `[4864,5011)`; the final `simpa` therefore could not close
  `n.val < 5120`.  Changed only the emitter's final interval fact to the padded
  bound (valid because every `Fin 5011` value is below 5011) and regenerated.
- Regenerated `EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean`: 1,274
  lines, 2,506 terminals, SHA-256
  `A06CE2E053F9D1243D2A11B943102A5462409DA63B406AD39CDC9BCE24F5A540`.
  Emitter SHA-256 `D5317C546A4EF7C9EF5A9C6CF41D22A9CF87DC8019CF2CD53B861FEC1AF567A2`;
  block audit SHA-256 `00F658F542F606E07344A21A6E2C138B8697B513F17B76AE5228ED28C909E084`.
- `audit_terminal_census_blocks.py` `ok=true`: 20 padded contiguous blocks,
  literal cards sum 2,506, dispatcher orientation complete, final interval
  `(4864,5120)`.  Report SHA-256
  `51206EC377CA96A8C89E0B3CFEAED66557EF536333AC7B28F0996C251F86E729`.
  `audit_terminal_census.py` `ok=true`, exact
  terminal/sharp/B12/rest/B13/residual = `2506/120/815/1182/1997/389`,
  refined residual 373.  Scope remains static source/finite-set auditing,
  **not Lean elaboration or kernel checking**.
- The census remains **CI pending** at the new SHA.  No local project build was
  run.  `audit_target_imports.py` completed `ok=true`, closure 1,990, zero
  missing imports, zero forbidden tokens; report SHA-256
  `2670DF161C730A18BD5A2BA2907DCB2BED4E3B321F4CFB6C3EE7F67B27354959`.
  All 373 residual radii, packet `f0Lo`/`g`, 382 absent payload records,
  SevenClassExclusions (`0/7`), and the arbitrary-centre full-disk theorem
  remain unpaid.
- Next: push/run CI on `TerminalCensus` at `A06CE2E0...A540`; if green inspect
  `ResidualCard`, otherwise read the first diagnostic and fix only the emitter.

## 2026-11-02 - session 150: padding repair, ResidualCard decoupling, target hygiene

- Session 149's final padded interval fix is present in
  `EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean` (1,292 lines,
  SHA-256 `A06CE2E053F9D1243D2A11B943102A5462409DA63B406AD39CDC9BCE24F5A540`).
  `audit_terminal_census_blocks.py` reports `ok=true`: twenty blocks
  (19 x 256 + 147), padded final interval `[4864,5120)`, literal card sum 2,506,
  and source hash above.  This is static source auditing, **not elaboration or
  kernel checking**; the census remains **CI pending**.
- Removed the stale `N11Formalization.LaneBPublicResidualCrosswalk` target.
  `TARGETS.txt` now has 31 targets, SHA-256
  `036056ACABBB35108AA7B61097F05EE2E42842138E2F49B3388FFC501E0AD647`.
- `ResidualCard.lean` is now decoupled from `...ResidualCensusSdiff`: it carries
  the sixteen literal removed ids, proves their union identity with B13 paid ids
  by `tauto`, and proves disjointness from the 120 sharp ids by sixteen bounded
  `decide +kernel` facts.  Current SHA-256
  `E0415B0EBD46DB0BA9B3A5A792EA506EBAAA2C91BEFAAB8DD119EB5667FB6F40`.
  `audit_residualcard_decoupling.py` reports `ok=true` (16 ids, disjoint from
  120 sharp ids, old census absent, terminal census present, closure 625).
  This is source/import/literal-id auditing only; `ResidualCard` is **CI pending**.
- Re-ran `audit_terminal_census.py`: `ok=true`, exact
  terminal/sharp/B12/rest/B13/residual = `2506/120/815/1182/1997/389`,
  refined residual 373.  `audit_target_imports.py` exceeded its 60 s bound and
  produced no fresh verdict in this session.
- A Mathlib-probe harness for the exact `Fin 20` cardinality normalization
  timed out at 120 s while importing Mathlib, so it gave no Lean verdict.
  No full project build was run (worker constraint).
- Still unpaid: kernel acceptance of the census and `ResidualCard`; structural
  trio; all 373 residual radii; packet `f0Lo`/`g`; 382 absent payload records;
  SevenClassExclusions (`0/7`); arbitrary-centre full-disk theorem.
- Next concrete step: CI on the new hashes, inspecting `TerminalCensus` first.
  If it is green, inspect `ResidualCard`; if red, fix only the first generated
  proof and keep the literal terminal data frozen.
