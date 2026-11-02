# Lane B notes

Durable state through session 155 (2026-11-02):
- B13 paid count is 1,997 (B12 815 + rest1182).  The sixteen certified removals
  leave a refined residual of 373 of the frozen 389 terminal ids; terminal count
  is 2,506.  No cardinality result pays a radius.
- Prior CI run `41352871085` (head `b1e15e83`) was green for `Paid16GeneralNext1182`,
  `Next505Bounds`, `DescentBounds`, `B13`, `B13Main`, `RefineSixteen`, and
  `RefineSixteenMain`; its first lane-B red node was the old `TerminalCensus`.
- That census was rewritten as twenty blocks (19 x 256 + 147), each with one
  bounded `decide +kernel`, interval facts, a generic pairwise-disjointness proof,
  and one `card_biUnion` sum.  Current source SHA-256 is
  `2FC5650F32D662D5105489214F5A09E7956C64066A55A9D1C98FC484372AFB83`.
- `TerminalCensus` and `ResidualCard` remain **CI pending**.  All 373 residual
  radii, packet payloads, 382 absent payload records, SevenClassExclusions
  (0/7), and the arbitrary-centre full-disk theorem remain unproved/unpaid.

## 2026-11-02 - sessions 155-158: census audits and proof hardening (condensed)

- Strengthened the static census auditors: they recover 5,011 declarations,
  2,506 terminal flags, and block counts
  `61,75,69,62,62,61,55,56,66,237,254,253,255,221,115,120,108,111,150,115`.
  All arithmetic audits passed, but none is Lean elaboration or kernel credit.
- Replaced the fragile recursive-sum census proof with explicit per-block
  cardinalities and `Finset.card_biUnion`; the current census source is
  `943A296C...FDBB`.  Bounded Mathlib probes timed out during import loading.
- No local full-project build was run.  `TerminalCensus`/`ResidualCard` stayed
  CI pending, as did the 373 residual radii, payloads, SevenClassExclusions
  (0/7), and the arbitrary-centre theorem.

## 2026-11-02 - session 159: exact old CI diagnostic and generated-tactic repair

- Downloaded the `41352871085` build artifact and inspected its retained
  `errors_head`.  It confirms the old census source failed in elaboration, not
  only by OOM: offset-zero `block_mem` membership proofs produced `No goals to
  be solved`, followed by `Type mismatch: After simplification`, and later
  `unsolved goals` in block-image injectivity proofs.  This diagnostic is for
  the older source, not the current tree.
- Updated `n11-work/ops/lanes/B/emit_terminal_census_blocks.py` (SHA-256
  `3BF8F363BFCF3472BBB183B1E59E60438326EDD782E35101D09BC2D75E16CB3C`) so
  subset and embed-equality proofs use `simp [embed…]; all_goals omega`.
  `all_goals` is deliberately safe when simplification closes every goal,
  including the offset-zero block, while still discharging nonzero-offset
  arithmetic goals.
- Regenerated `EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean`
  (SHA-256 `B9E98D204B7BF5D8AC5DF94913822F4B3A708BEB98BA26E6CEFD9CB080165608`,
  1,274 lines, 79 `all_goals omega` tactic occurrences, no remaining
  `<;> omega`).  The auditor
  `audit_terminal_census_blocks.py` SHA-256
  `142C6BF9F8FFEA36B9715C656FF8F7865377C754E8C7E280EA0CFD086B043FDA`
  still passes all 16 static checks; report SHA-256
  `51A9ED497D04D8500D2EE4BC4A1BC367730C9D51125C4EC6659C60BF79D815EB`.
  Scope is source parsing and generated-text structure only, not Lean
  elaboration or kernel proof credit.
- `TerminalCensus`/`ResidualCard` remain **CI pending** at the new census SHA.
  No local full-project build was run.  All 373 residual radii, packet payloads,
  382 absent payload records, SevenClassExclusions (0/7), and the
  arbitrary-centre full-disk theorem remain unproved/unpaid.
- Next concrete step: run lane-B-first CI on the updated census SHA; if the
  offset-zero/embed goals are cleared, capture the next first Lean diagnostic
  (currently most likely the `Fin.sum_univ_succ` cardinality normalization),
  then run `ResidualCard`.

## 2026-11-02 - session 160: CI routing and bounded top-card probe

- Confirmed the actual repository API path is
  `Liyang1145/DiskCoveringProofs`.  Run `41394181326` is **pending** on head
  `68d172d9adc4997225fb729efec40c34e8ddf825` (created 05:27:59Z); it has not
  started, so it gives no Lean verdict.  Run `41380560959` is still
  `in_progress` on the older head `a29e4ee1...`, so it cannot test the repaired
  census SHA `B9E98D20...5608`.
- Rechecked current artifacts: census Lean SHA `B9E98D20...5608`, emitter SHA
  `3BF8F363...CB3C`, auditor SHA `142C6BF9...3FDA`.  `TARGETS.txt` already puts
  `EnergyTerminalBatchB13RefineSixteenTerminalCensus` first; no edit needed.
- Ran `python tools/project_status.py --check`: handoff-index check passed.  Its
  stated scope is manifest declarations only, not math or full byte integrity.
- Added a Mathlib-only probe outside the repo for the exact
  `Finset.card_biUnion` statement used at `censusIDs_card`.  A 150 s bounded
  `lake env lean` run timed out while loading `Mathlib` with no elaboration
  output; therefore the rewrite pattern remains unverified, not passed.
- `TerminalCensus`/`ResidualCard` remain **CI pending**.  All 373 residual
  radii, packet payloads, 382 absent payload records, SevenClassExclusions
  (0/7), and the arbitrary-centre full-disk theorem remain unpaid.
- Next concrete step: poll run `41394181326`; once it starts, download its
  first lane-B diagnostic for the census target.  Repair only that diagnostic,
  rerun the static census auditor, then proceed to `ResidualCard`.

## 2026-11-02 - session 161: independent 389 -> 373 bridge audit

- Added `audit_refined_373_bridge.py` (SHA-256
  `7A6C0D19DF56052C4CA29599E3F392D68EBEAE1B87E1617DF68C5989F44D1CA0`).
  It independently parses the frozen terminal flags, the old 389-id literal
  census, the sixteen `removedIDs`, and the 120-element `patchID`, then checks
  the exact set identity `refined = old389 \ removed16` plus membership.
- Ran it at 60 s scope: `ok=true` for all 14 checks. Counts: 2,506 source
  terminals, 120 sharp, 389 old residual, 16 removed, 373 refined residual;
  every old/removed/refined id is terminal, removed and refined ids are
  sharp-disjoint, and the exact difference and claimed Lean cardinalities
  match. Refined-id digest is
  `7539D9214C5CAC780F027688D2BFA41D5451A0D13BA7834BBC49E9D2FAE41A6A`.
  Report `audit_refined_373_bridge-report.json` SHA-256
  `BC4064E7E1B846A6AFF010ABA864E51ABF37599033AB8054E7A6E24D2DBEFE4F`.
  Scope is static source parsing and finite set/cardinality arithmetic, **not**
  Lean elaboration or kernel proof credit.
- Re-ran `audit_terminal_census_blocks.py`: `ok=true`, census SHA remains
  `B9E98D204B7BF5D8AC5DF94913822F4B3A708BEB98BA26E6CEFD9CB080165608`.
  A 120 s Mathlib probe timed out during import loading; no tactic verdict.
  No full-project local build was run.
- n11 CI run `41399703011` is still **pending** on old head `ceb39493`; its job
  has not started, so `TerminalCensus`/`ResidualCard` remain **CI pending**.
  The earlier `41394181326` was cancelled without a Lean verdict.
- Still unpaid: all 373 residual radii, packet payload records, 382 absent
  payload records, SevenClassExclusions (0/7), and the arbitrary-centre
  full-disk theorem.
- Next concrete step: get a lane-B-first n11 CI verdict on census SHA
  `B9E98D20...5608`; repair the first Lean diagnostic, then run
  `EnergyTerminalBatchB13RefineSixteenResidualCard`.

## 2026-11-02 - session 162: census cardinality proof hardening

- Replaced the census top-card proof's dependence on recursive
  `Fin.sum_univ_succ`/`norm_num` normalization with: a literal `blockSizes`
  vector, twenty explicit `blockIDs_card_eq` cases, a small kernel-checked
  `blockSizes_sum`, and `censusIDs_card_aux` by `Finset.sum_congr`.  The public
  `censusIDs_card` is now `simpa using censusIDs_card_aux`.
- Regenerated `EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean` (1,309
  lines, SHA-256 `943A296CAFB75ECABB01A80D993016FF91D9758CF6F4CF5ADFAF0884259EFDBB`).
  Updated emitter SHA-256
  `529F1A8A8DD62627441AE1D6F63D89AD1805084D5D984F195FF38345C85EDA6A` and
  auditor SHA-256
  `30FB1AA21BF5228061F56D997BBCE46F244607BF0D1994C4D1D94EF6DB4E13F6`.
- Ran the static auditor at 60 s scope: `ok=true` for all 17 checks, including
  source-derived block sizes `61,75,69,62,62,61,55,56,66,237,254,253,255,221,115,120,108,111,150,115`,
  sum 2,506, and absence of the old sum-normalization tactic.  Report SHA-256
  `F3A731401059F9AD2F76D02A0FE6D88FC8B4498599F36B2272C0031CFC478A53`.
  Scope is generated-source/static arithmetic only, **not Lean elaboration or
  kernel proof credit**.
- Re-ran `audit_refined_373_bridge.py`: `ok=true` for all 14 checks, 2,506
  source terminals and exact 389 -> 373 difference.  Scope remains source-ID
  parsing/arithmetic only.  No local full-project build was run; the cached
  Mathlib probe still cannot load enough compiled dependencies for a useful
  local tactic verdict.
- CI run `41399703011` remains **pending** on old head `ceb39493` with zero
  jobs, so it does not test the new census SHA.  `TerminalCensus` and
  `ResidualCard` remain **CI pending**.  Unpaid: all 373 residual radii, packet
  payloads, 382 absent payload records, SevenClassExclusions (0/7), and the
  arbitrary-centre full-disk theorem.
- Next concrete step: run lane-B-first CI on census SHA `943A296C...FDBB`; if
  green, run `EnergyTerminalBatchB13RefineSixteenResidualCard`; otherwise repair
  the first Lean diagnostic only.

## 2026-11-02 - session 163: paid-set delta audit

- Added `audit_paid_delta.py` (SHA-256
  `095DC04EE51EF7FC74F5BDF5B8CF9232CEAA5DEA56C8E77AE6A4314788C70EE`).  It
  reconstructs the seven-step B13 refinement chain from Lean source, checks the
  cited singleton modules, computes the actual delta from `B13.paidIDs`, and
  compares it with the sixteen literals in `ResidualCard.removedIDs`.
- Ran it at 30 s scope: `ok=true` for all seven checks.  The exact delta is
  `{37,2337,2341,2965,3040,3112,3116,3431,3440,3573,3589,3623,3633,3777,3792,3853}`,
  matching `removedIDs`; per-module additions are `7,1,3,1,1,1,2`, and
  `1997 + 16 = 2013` matches `Repair.paid_count`.  Report SHA-256
  `80817CE8CE632F36D2E62540C8FC98EF2B677669FF12DFDF600F7E78CAB5106`.
  Scope is static Lean-source reconstruction, **not** elaboration or kernel
  proof credit.
- Checked GitHub runs by API (no `gh` installed): recent n11 `math-checks` are
  green, while the only n11 Lean run `41399703011` remains pending on old head
  `ceb39493` with no job allocated.  `TerminalCensus` and `ResidualCard` remain
  **CI pending**; no local project build was attempted.
- Still unpaid: all 373 residual radii, packet payloads, 382 absent payload
  records, SevenClassExclusions (0/7), and the arbitrary-centre theorem.
- Next concrete step: when a lane-B-first CI job starts, fix the first Lean
  diagnostic at census SHA `943A296C...FDBB`; if green, kernel-check
  `EnergyTerminalBatchB13RefineSixteenResidualCard` next.

## 2026-11-02 - session 164: exact residual target inventory

- Extended `audit_refined_373_bridge.py` to emit `residual373-ids.txt`, the
  exact sorted complement `old389 \ removed16`.  Re-ran the audit: `ok=true`;
  counts are 2,506 terminals, 120 sharp, 389 old residual, 16 removed, and 373
  refined residual; the list has exactly 373 lines.
- New artifact SHA-256: `residual373-ids.txt` =
  `ECF924976536FFCB228E56394B4D39CF776648E8AD42617E1AF8A38E26C0D4FE`.
  Updated audit source SHA-256 =
  `CB3FDA08BD5BAC12042DEE7CC4182EF4DB2C6BF2FC1701C4913B683FE3EAF2CA`;
  report SHA-256 =
  `B40434E36C1DC12352244520E9600027AEBDFDB983D221AAAF573E3A6604F256`.
  Scope is exact source-ID/arithmetic audit, not Lean elaboration or kernel
  proof credit.
- Re-ran `audit_terminal_census_blocks.py`: `ok=true` for all 17 static checks;
  census source remains `943A296CAFB75ECABB01A80D993016FF91D9758CF6F4CF5ADFAF0884259EFDBB`.
  `audit_paid_delta.py` also remains `ok=true`, with the same sixteen-id delta.
- A 90 s Mathlib-only `Finset.card_biUnion` API probe again timed out during
  import loading, so it produced no tactic verdict.  No local project build
  was run.
- CI run `41399703011` is still pending on old head `ceb39493` with no job;
  `TerminalCensus` and `ResidualCard` remain **CI pending**.  All 373 residual
  radii, packet payloads, 382 absent payload records, SevenClassExclusions
  (0/7), and the arbitrary-centre full-disk theorem remain unpaid.
- Next concrete step: use `residual373-ids.txt` to pick the first residual id
  with an existing frozen row-cap payload and emit one honest singleton radius
  wrapper; in parallel, if CI starts, repair the first census diagnostic.
- Quick inventory: residual ids with existing whole-row frozen cap modules are
  `{1409, 2356, 2360, 2368, 2370}`.  These caps alone are not radius
  certificates; the next wrapper must still derive the full packet/radius
  obligation rather than treating the cap as payment.
