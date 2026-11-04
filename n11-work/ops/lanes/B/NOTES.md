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
