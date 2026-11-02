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

## 2026-11-02 - session 155: independent source-to-census audit

- Strengthened `audit_terminal_census_blocks.py` (SHA-256
  `0CFAC3BA01C03F743480184136F7797798B23298492D4A72CB860A12B87A8AE8`).
  It now independently parses the frozen `DBMSourceTreeData.lean`, recovers all
  5,011 node declarations and 2,506 with `terminal := true`, and compares the
  source terminal cardinality in every one of the twenty blocks to the literal
  `census*_card` values.  It also cross-checks these against `blockIDs*_card`.
- Ran the audit at 60 s scope: `ok=true`.  The exact per-block source counts are
  `61,75,69,62,62,61,55,56,66,237,254,253,255,221,115,120,108,111,150,115`;
  their sum and the literal sum are both 2,506.  Report
  `audit_terminal_census_blocks-report.json` SHA-256
  `D41FD946A61B810DB7CCB6B508CDE9917657DD59A3796B7A79565837B0C27CC4`.
  Scope is static source parsing and finite arithmetic, **not Lean elaboration
  or kernel proof credit**.
- The audited Lean census is unchanged at SHA `2FC5650F...FB83`.  CI run
  `41380560959` (head `a29e4ee1`) remained in progress at the Mathlib/build
  stage and gives no verdict on this source.  No local full-project build was
  run.
- Operational issue: `.github/workflows/n11-lean-build.yml` still concatenates
  lane C targets before lane B.  The ~200 lane-C targets can exhaust the build
  window before `TerminalCensus`; the supervisor should prioritize lane B for
  the next diagnostic run.  This worktree did not edit the workflow.
- Unpaid unchanged: kernel acceptance of `TerminalCensus` and `ResidualCard`;
  structural trio; all 373 residual radii; packet `f0Lo`/`g`; 382 absent payload
  records; SevenClassExclusions (0/7); arbitrary-centre full-disk theorem.
- Next concrete step: obtain a CI verdict for
  `EnergyTerminalBatchB13RefineSixteenTerminalCensus` at SHA
  `2FC5650F...FB83`, with lane-B targets scheduled first; repair only the first
  emitted Lean diagnostic, then run `ResidualCard`.

## 2026-11-02 - session 156: census cardinality tactic split

- Repaired the emitted `censusIDs_card` proof to use the previously probed
  two-step pattern: `simp [Fin.sum_univ_succ, ..., blockIDs, blockIDs*_card]`
  followed by `norm_num`.  The prior single `norm_num [rewrites]` line had no
  independent successful probe.
- Regenerated `EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean`
  (SHA-256 `A06CE2E053F9D1243D2A11B943102A5462409DA63B406AD39CDC9BCE24F5A540`)
  with `emit_terminal_census_blocks.py` (SHA-256
  `D5317C546A4EF7C9EF5A9C6CF41D22A9CF87DC8019CF2CD53B861FEC1AF567A2`).
- Updated `audit_terminal_census_blocks.py` (SHA-256
  `142C6BF9F8FFEA36B9715C656FF8F7865377C754E8C7E280EA0CFD086B043FDA`)
  and ran it at 60 s scope: `ok=true`, 2,506 source terminals, twenty block
  cards summing to 2,506.  Report SHA-256
  `5E35F67CE01AAAA56F17B360F9C1108CA9FDBE49FDCF6FE12DC5D47BD615241D`.
  Scope remains static source parsing/arithmetic, not Lean elaboration.
- A 120 s Mathlib probe attempt timed out while loading imports; no probe
  verdict was obtained and no full-project build was run.
- `TerminalCensus`/`ResidualCard` remain **CI pending**.  Still unpaid: all 373
  residual radii, packet payloads, 382 absent records, SevenClassExclusions
  (0/7), and the arbitrary-centre full-disk theorem.
- Next concrete step: CI-kernel-check
  `N11Formalization.EnergyTerminalBatchB13RefineSixteenTerminalCensus` at SHA
  `A06CE2E0...A540` as the first lane-B target; repair the first emitted Lean
  diagnostic, then run `ResidualCard`.

## 2026-11-02 - session 157: live CI and bounded probe retry

- Re-ran `audit_terminal_census_blocks.py` at 60 s scope against census SHA
  `A06CE2E053F9D1243D2A11B943102A5462409DA63B406AD39CDC9BCE24F5A540`:
  `ok=true`, 2,506 source terminals, block cards
  `61,75,69,62,62,61,55,56,66,237,254,253,255,221,115,120,108,111,150,115`,
  sum 2,506. Report SHA-256
  `5E35F67CE01AAAA56F17B360F9C1108CA9FDBE49FDCF6FE12DC5D47BD615241D`.
  Scope is static parsing/arithmetic, not Lean elaboration.
- Queried GitHub run `41380560959`: still `in_progress`, head `a29e4ee1`,
  updated `2026-11-02T05:08:32Z`. It predates the current census SHA, so it
  cannot provide a verdict for the repaired proof.
- Retried a 90 s Mathlib-only probe of the `Fin.sum_univ_succ` +
  `norm_num` cardinality pattern. `lake env lean` timed out during import
  loading with no elaboration output; no tactic verdict. No full-project
  build was run.
- `TerminalCensus`/`ResidualCard` remain **CI pending** at census SHA
  `A06CE2E0...A540`. All 373 residual radii, packet payloads, 382 absent
  records, SevenClassExclusions (0/7), and the full-disk theorem remain
  unproved/unpaid.
- Next concrete step: request lane-B-first CI on the committed census SHA,
  capture the first Lean diagnostic, and repair only that line before running
  `ResidualCard`.

## 2026-11-02 - session 158 (part 4): Lemma-name audit of census card proof

- Concrete check against the pinned Mathlib source in
  `/workspace/tools/mathlib-probe/.lake/packages/mathlib`:
  `Fin.sum_univ_succ` is used/declared (e.g. `Geometry/Euclidean/Angle/Oriented/Rotation.lean:101`)
  and `Fin.sum_univ_zero` is referenced at `Data/Fin/Tuple/Reflection.lean:203`.
  So the two lemma names in `censusIDs_card`'s `simp` list are valid in this
  toolchain; they are not the source of a red module.
- Scope: static source grep of pinned Mathlib only. No Lean elaboration, no
  kernel credit, no build. Census SHA remains `A06CE2E0...A540`.
- `TerminalCensus`/`ResidualCard` remain CI pending; all 373 residual radii,
  packet payloads, 382 absent records, SevenClassExclusions (0/7), and the
  arbitrary-centre full-disk theorem remain unpaid.
- Next concrete step: with the lemma names cleared, get the lane-B-first CI
  verdict on `N11Formalization.EnergyTerminalBatchB13RefineSixteenTerminalCensus`
  at SHA `A06CE2E0...A540`; expect the first remaining risk to be the
  `blockIDs` disjointness/interval `omega` step, then run `ResidualCard`.

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
