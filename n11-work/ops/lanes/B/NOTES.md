# Lane B notes

Durable state (2026-11-02, unless a later entry says otherwise):
- B13 paid count is 1,997 (B12 815 + rest1182); the sixteen certified removals
  leave a refined residual of 373 of the frozen 389 terminal ids.  Terminal
  count is 2,506.  No cardinality or row-cap result pays a radius.
- Prior CI run `41352871085` (head `b1e15e83`) was green through
  `RefineSixteenMain`; its first lane-B red node was the old `TerminalCensus`.
- Local box has no project oleans; CI is the only authority for project modules.
- All 373 residual radii, their packet producers, 382 absent payload records,
  `SevenClassExclusions` (0/7), and the arbitrary-centre full-disk theorem
  remain unproved/unpaid.

## Condensed chronology 155-176
- 155-164: census 5,011 decls / 2,506 terminal flags / 20 block counts; source
  SHA-256 `943A296C...FDBB`.  `residual373-ids.txt` = exact complement, 373
  lines, SHA-256 `ECF92497...0D4FE`.  Frozen caps `{1409,2356,2360,2368,2370}`
  pay no radius.
- 165/166: `LaneBResidual373Incremental`, `LaneBResidual373Seed1409`.
- 167: `audit_1409_canonical_record.py` -- seven survey failures
  `1409,2337,2341,2356,2360,2368,2370`, all `lower - T^2` exactly negative.
- 168: `LaneBResidual346Bridge` + `EnergyRefineN0040`; `B373 = C346` + 27 green.
- 169/170: 14 All14 leaves + `LaneBArchiveRefine3And23`/`All14`; conditional
  346 -> 332.
- 171: `audit_refine_option_shape.py` -- the 14 leaves carry `maxRecDepth 100000`
  and giant lines but **zero** `maxHeartbeats 0`; nine sibling modules of
  identical shape are CI-green, so that shape is an elaboration-timeout risk only.
- 172/173: run `41706645384` was deadlocked behind lane-C
  `EnergyTerminalResidualCensusC01`; `audit_laneb_leaf_ci_verdict.py` +
  `audit_leaf_pk_invariants.py`.
- 174: `audit_laneb_target_hygiene.py` -- 0 forbidden tokens in 34 targets + 67
  closure modules; `maxRecDepth 100000` in 30 closure modules.
- 175/176: downloaded CI artifact `13290712587` (run `41706645384`) and parsed
  `summary.json` (193 exits): 4 of 34 lane-B targets reached, 2 green
  (`...Refine0037`, `...RefineTwelve`), 2 red (`EnergyTerminalResidualCensus`,
  `EnergyTerminalResidualCensusRefineSixteen`); report
  `audit_run41706645384_laneb_exits-report.json`.
- FOCUS MODE (user): one countable target per lane -- B must make every module
  in `lanes/B/TARGETS.txt` compile; no new Refine/Census files until green.

## 2026-11-04 - session 177: census chain root-cause + kernel-budget audit

- **The two lane-B reds are derived.** `EnergyTerminalResidualCensus` and
  `EnergyTerminalResidualCensusRefineSixteen` (targets 33-34) both import the
  four census chunk modules `...CensusC01..C04`; each chunk imports only
  `...CensusBase`, so all four fail *independently* (CI exit 1) and the two
  targets inherit the failure.  `...RefineSixteen` also imports `...Census`.
- **Root cause (static).** Every `mem_iff_id_NNNN` in C01..C04 is the identical
  6-line `rcases / subst / rw [EnergyTerminalBatchB13.mem_residualIDs_iff] /
  decide +kernel +revert` body.  That single kernel decision must normalise
  membership in `EnergyTerminalBatchB13.residualIDs`, i.e.
  `(DBMSourceTree.data n).terminal` **and** `n notin sharpIDs` **and**
  `n notin paidIDs` (1997 declared paid ids), so the decided literal budget is
  **1997**, ~4x GUIDANCE rule 6's <=500 limit.
- **Green sibling contrast.** `EnergyTerminalBatchB13Refine0037` proves
  `(37:Fin 5011) notin paidIDs` hierarchically: 28 bounded `decide +kernel`
  facts on `Paid16GeneralNext1182S0k.idsNN` literals + `new_mem` + `push_neg`.
  That is the reusable repair pattern; the census never uses it.
- **New lane-B files.** `ops/lanes/B/audit_census_kernel_budget.py` (SHA-256
  `ca090a10...936db`) + `audit_census_kernel_budget.json` (SHA-256
  `1c992e24...4a90a`).  Static counts: C01 1300 `mem_iff`/1300 `+revert`/11780
  lines, C02 same, C03 1211/10979, C04 1200/10875; residual literal = 389 =
  100+100+100+89; `exceeds_guidance: true` (1997 > 500); no `maxHeartbeats 0`,
  no `maxRecDepth`, max line 82 B in all four chunks.
- **Staleness.** CI run `41706645384` (head `bd5573e5`) predates lane C's
  `2026-11-04 03:47` edit of `...CensusC01.lean`, so that run's C01 verdict is
  stale; the C02-C04 exits and the `...Census`/`...RefineSixteen` exits stand.
  A fresh lane-B-first CI run is required for a verdict.
- **Probe attempt inconclusive.** `mathlib-probe/DeepRecursionProbe.lean`
  (1997-element nested-insert literal) was *blocked*, not slow: `time` reported
  user 0.34 s / sys 1.7 s over a 200 s wall run, so `lake env lean` stalled in
  the environment.  Do NOT cite it as evidence.
- Checks run: `audit_census_kernel_budget.py` exit 0 (`ok: true`); sha256 of the
  script + report recorded above.  Scope: static source/token scan only --
  **not a build, not kernel credit, not a proof**.  No Lean build attempted.
- Still unproved/unpaid: kernel acceptance of all lane-B targets; the 373/332
  residual radii; source-missing payloads; `SevenClassExclusions` (0/7); the
  arbitrary-centre full-disk theorem.
- Very next concrete step: in C01..C04 replace each per-index
  `decide +kernel +revert` with a hierarchical membership proof (bounded
  per-chunk decides for the LHS literal + the `Refine0037` `not_paid` split for
  the RHS), regenerated by a deterministic Python emitter; if the literal
  equality is not on the critical path, instead propose dropping targets 33-34
  from `lanes/B/TARGETS.txt` and let CI verify the remaining 32.

## 2026-11-04 - session 178: census root-cause confirmed structurally; repair data pipeline started

- **Structure pinned (read-only).** `EnergyTerminalResidualCensus.lean` proves
  `residualIDs_eq : residualIDs = EnergyTerminalBatchB13.residualIDs` by `Finset.ext`
  + 51 `mem_iff_blockNN` (value ranges of 100) + **5011** `mem_iff_id_NNNN` lemmas
  split 1300/1300/1211/1200 across `...CensusC01..C04`.  Each `mem_iff_id_NNNN`
  body is `rcases/subst/rw [EnergyTerminalBatchB13.mem_residualIDs_iff]/decide +kernel +revert`.
  The decided prop combines: LHS membership in the local 389-literal union (chunks
  100+100+100+89) **and** RHS `terminal=true ∧ n∉sharpIDs ∧ n∉paidIDs` where
  `paidIDs = B12.paidIDs ∪ Next1182.newIDs` (1997 literals) and
  `sharpIDs = univ.image patchID` (120, membership via `∃` over Fin 5011).
- **Cheap repair recipe identified** (reuses `EnergyTerminalBatchB13Refine0037`):
  prove `n ∉ paidIDs` hierarchically = B12→(B11→(B10→(B09→…), Remaining210), Next505),
  Next1182→S01..S08→ids00..ids63, each leaf decide ≤210 literals.  Then `mem_iff_id_NNNN`
  becomes: LHS decide on the local 389-union only (≤389 literals) + RHS assembled from
  `mem_residualIDs_iff` with the hierarchical not-paid fact.  **Key cost saving:** the
  not-paid fact is the same shape for all 5011 indices and can be emitted mechanically;
  no single `decide` needs >~210 literals.
- **`EnergyTerminalBatchB13Refine0037.lean` = exact template** (307 lines / 1 index:
  `not_next1182_partNN` + `not_next505` via `new_mem`+`push_neg`+`repeat' constructor <;> decide`,
  then `not_paid_0037` by `rw paidIDs/mem_union` cascade).  Refine0037 is already green.
- **Static cross-check (in progress).** Python parses the literal defs and rebuilds
  `paidIDs`/`sharpIDs`/census to confirm 389 = terminals \ (sharp ∪ paid) as exact sets
  (independent of Lean).  So far: chunks parse to 100+100+100+89 = **389, pairwise distinct**.
  `patchID` (120 values) parsed.  Paid chain B13→B12→B11→B10→B09→… still being resolved.
- **Probe environment still blocked.** `mathlib-probe/KernelBudgetProbe.lean` (membership
  decides at literal sizes 100/389/1997) ran 4m40s wall with user 0.26s -> `lake env lean`
  stalls in the sandbox (same as DeepRecursionProbe, session 177).  **Do NOT cite it.**
- Checks run: Python chunk parse exit 0 (389, distinct).  Scope: static source parse only --
  **not a build, not kernel credit, not a proof**.  No Lean build attempted (env blocked).
- Still unproved/unpaid: kernel acceptance of targets 33-34 and all 51 blocks; the 373/332
  residual radii; `SevenClassExclusions` (0/7); arbitrary-centre full-disk theorem.
- Very next concrete step: finish the Python cross-check (resolve B09..B00 + Remaining210
  G03..G12 + Next505 ids00..24 + Next1182 S01..08 ids00..63), then write deterministic
  emitter `ops/lanes/B/emit_census_hier.py` that regenerates C01..C04 with hierarchical
  not-paid facts (Refine0037 template) + local-only LHS decides; keep C01..C04 as fresh
  modules (do NOT edit frozen).

## 2026-11-04 - session 179: census paid-chain audit tool corrected; under-count exposed

- **Fixed a real bug in `ops/lanes/B/audit_census_fix_cost.py`.**  It assumed each
  `Paid16GeneralNext1182S0k` module defines `ids{8*(k-1)+i}` for `i<8` (8 groups each).
  Wrong: group numbering is global `ids00..ids56` (57 groups, matches
  `rest1182-emission-manifest.json` `n_groups=57`); e.g. `S08` defines only
  `ids56 : {4986,4990,4995,5000,5002,5007}` (6 ids, 1 group).  Patched `_s_ids(s)`
  to enumerate `^def ids\d+` per module.  Old script aborted with
  `AssertionError: ('Paid16GeneralNext1182S08','ids57')`; patched script now runs to
  its own assertion.
- **Exposed two further defects in the same audit (still red).**  Patched run fails
  `assert len(paid)==1997 and len(sharp)==120`: got `paid=1688, sharp=0, census=389`.
  (a) The paid chain is deeper than `B09`: read-only defs give
  `B12 = B11.paidIDs ∪ Next505.newIDs`, `B11 = B10 ∪ Remaining210`,
  `B10 = B09 ∪ First42`, `B09 = B08 ∪ Paid16Batch22Consumer.newIDs`, `B08 = B07 ∪ …`;
  `resolve()` treats `B09.paidIDs` as a base, so it drops 309 ids.  (b) `sharpIDs`
  is `Finset.univ.image patchID`, not a literal, so the literal-only parser returns
  the empty set (`sharp=0`).
- **Scope of checks:** static Python source parse of `n11-work/lean/N11Formalization`
  only; **not a build, not kernel credit, not a proof**.  No Lean run attempted
  (local env still stalls `lake env lean`, sessions 177-178).  `tools/project_status.py
  --check` exit 0 (manifest index only).
- **Still unproved/unpaid:** kernel acceptance of all 34 lane-B targets (33-34 red via
  lane-C-owned `EnergyTerminalResidualCensusC01..C04`); the 373/332 residual radii;
  source-missing payloads; `SevenClassExclusions` (0/7); arbitrary-centre full-disk
  theorem.
- **Lane ownership note (important for supervisor):** `git log` shows
  `EnergyTerminalResidualCensusC01..C04` last authored by commit `a714ed6b`
  "lane C: dsf session 2026-11-04 03:47".  Lane-B targets
  `EnergyTerminalResidualCensus` and `...RefineSixteen` import them, so lane B cannot
  green those two without either lane-C cooperation or fresh lane-B census modules
  (FOCUS MODE currently forbids new Census files).  Resolve ownership before emitting.
- **Very next concrete step:** finish `audit_census_fix_cost.py` correctness: make
  `resolve()` follow `B09→B08→…→B00` (find the terminal base module), and handle
  `Finset.univ.image patchID` by resolving `patchID` to its 120 literals; re-run and
  require `paid=1997, sharp=120, census=389` with `census ∩ paid = census ∩ sharp = ∅`.
  Only then emit `emit_census_hier.py`.

- **session 179 addendum (same run, exact numbers).**  After patching `resolve()` to
  also read `insert n (...)` literals and to expand `Finset.univ.image patchID` via the
  `![...]` vector in `Patch120DomainPacket.lean`, the audit now gets `sharp=120` and
  `census=389` correct, and `N505=505`, `N1182=1182` (both exact).  Remaining gap:
  `b10 = B09.paidIDs ∪ First42.newIDs` resolves to only **11** (should be 100) and
  `Remaining210.newIDs` resolves to **0** (should be 210).  Cause: those `newIDs` are
  `def newIDs := Finset.univ.biUnion part` with a `part : Fin k → Finset (Fin 5011) :=
  ![…]` table, which the literal-only parser cannot follow.  So `paid` comes out 1698.
  Next step (unchanged in spirit): teach `resolve()` to expand `univ.biUnion part` by
  reading the `part` vector table, then re-run; expected `paid=1997`.  Scope unchanged:
  static parse only, no build, no kernel credit.
