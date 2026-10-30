# EXPERT REVIEW - n=11 Lean lanes
**Date:** 2026-10-30 (UTC)
**Scope:** `n11/work` at `dfe0881a`; state check, lane records, completed CI
run `41037794295`, `git log --stat -8`, and the newest A/B/C Lean bytes.
No Lean proof edit, local project build, lakefile/toolchain change, or commit
was made. CI/OOM evidence was read from the public job log; audits below are
diagnostics, not mathematical credit.
## Overall
- **Completed CI:** run `41037794295` (`dfe0881a`) exits 0 for C450Main,
  all five B13 targets, six restored C refinements plus N2341, and C450's source
  chain. A is red from `Bins` onward; C's `FrozenCapPublicExcludedTree` is red.
- **C450 is genuinely 36/36.** C450Main is CI-green. The endpoint transfer uses
  `C450Source36Segment.source36_paid` to insert source 36; the empty `drop 36`
  tail is not being substituted for the final segment.
- **B13 is real formal progress, not yet accepted ledger progress.**
  `B13.paid_count = 1997` and `B13Main` are CI-green with the allowed axioms.
  The root still imports B12Main and the maintained accepted handoff still says
  310/2386, so the current *formal conditional* energy set is 1997/2386 with 389
  unpaid IDs; it is not a newly accepted 1997 count.
- **C has seven real refinements but has moved no count.** N2341, N3040, N2965,
  N3440, N3589, N3623, and N3633 each exit 0 with `new_radius` axiom-clean.
  They define isolated singleton `newIDs`; no B13 consumer imports them, so the
  paid set remains 1997 and the residual remains 389.
- **A remains 0/7.** The narrow-cosine mathematics is sound, but the newest
  `EdgeShape` bytes have no independent CI verdict: Bins, EndpointChecks,
  UpperReductionUnimodal, both suffix modules, and EdgeShape all show exit 1.
  At most five suffix facts (edges 9--13) are drafted; zero `EdgeIncTo` facts and
  zero class exclusions are paid.
- **Unpaid mathematical obligations:** 389 energy terminal IDs (382 after a
  successful seven-ID C batch), all seven metric-class exclusions, the
  arbitrary-center full-disk theorem, and C's 382 absent HOST payloads. The
  389-ID cardinal itself is not yet a CI-green census theorem.
- **Fake-progress audit:** no float LP, `sorry`, new axiom, `native_decide`,
  `ofReduceBool`, or `maxHeartbeats 0` was found in the newest lane Lean bytes.
  Hash pins, archive restoration, exact Fraction checks, tree audits, and static
  import audits were not treated as proof. C's seven certificates are real only
  because their Lean targets and axiom reports are green.
- **Checks run here:** `python tools/project_status.py --check` passed its
  manifest/index scope; A's exact rational audit passed; all lane Python files
  passed `py_compile`; B's six static audits and target-closure audit passed.
  These checks prove no additional Lean theorem and do not repair the root OOM.
## Lane A
- **Approach is sound.** The correction from `cosHiReal <= 0` to the exact
  threshold `cosHiReal <= edgeCoeff i / (19/50)^2` is necessary. The split at
  grid node 1490, use of `-131/200` on the narrow arc, and `-2/3` on the upper
  tail are mathematically coherent. `edgeDecFrom_of_antitoneOn_from_next` also
  correctly handles the one-grid-step gap from witness 1489 to 1490.
- **Newest source:** `SevenClassQ0Deg3EdgeShape.lean`,
  `a69bccf854c23daa87827583f9aaa747085db6556341fe8a70cccf62f5589899`.
  It drafts `EdgeDecFrom 9`, `10`, and `11`; `EdgeSuffixHigh` drafts 12 and 13.
  These are candidate suffix facts, not 5/42 paid because no matching CI exit 0
  exists for the current bytes.
- **Exact blocking error is not the old binder problem.** CI says at Bins line
  95: expected `k.val % 256 < 255`, supplied `< 256`. `Nat.le_of_lt` unified its
  right endpoint with 255, so the expression is ill-typed. Replace it with a
  `< 256` proof followed by `omega`, or use `Nat.le_of_lt_succ`:
  `have h := Nat.mod_lt k.val (y := 256) (by norm_num); omega`.
- **No shape credit follows yet.** `edgeWitness` and the exact 1489-step proofs
  are only useful after Bins, EndpointChecks, UpperReductionUnimodal, and both
  suffix modules compile. The 21 increasing-prefix facts remain absent, and even
  a full 42/42 shape theorem pays only one input to `Q0Degree3AreaInput`; sectors,
  strict total, and the seven exclusions remain separate.
- **Highest leverage:** make the one-line Bins type repair, then run the serial
  target order through Bins -> EndpointChecks -> UpperReductionUnimodal ->
  EdgeSuffixNonpos -> EdgeSuffixHigh -> EdgeShape. Do not add a new shape file
  or a 42-leaf `fin_cases` theorem before those exits 0.
- **After green:** split edge 14's increasing prefix into
  `SevenClassQ0Deg3EdgePrefix.lean`, with a rigorous degree-28 cosine *lower*
  bracket above the edge-14 ratio on `[0, nodeQ 486]` and
  `monotoneOn_of_deriv_nonneg`; do not reuse the rejected nonpositive shortcut.
## Lane B
- **B13 is technically sound.** `paidIDs = B12.paidIDs ∪ Next1182.newIDs`,
  disjointness is proved through the B09 split/high exclusions, and
  `card_union_of_disjoint` yields 1997. `paid_radius` dispatches to the actual
  radius theorem for each member. `B13Main` correctly composes
  `remaining_of_b13` with `remaining_of_b12` into C450Main.
- **CI evidence:** B13Main
  `521ca436a8745ef197f76fcadedce2cf232b3b3643b977b997153e463fa41837` and B13
  `3dd37313505e0e8d608d50d42d3afb1f1e08cebbdf1acd5db570f57d9dc8fd03`
  both exit 0 on `dfe0881a`; the printed axiom sets are exactly
  `[propext, Classical.choice, Quot.sound]`.
- **Static audits are now diminishing returns.** They correctly report 310,
  815, 1997, 120, 2506, and 389, but they do not add theorem credit. Re-running
  hash/import audits cannot move the ledger.
- **Highest leverage is a supervisor-only root import switch.** At
  `n11-work/lean/N11Formalization.lean:1961`, replace
  `import N11Formalization.EnergyTerminalBatchB12Main` with
  `import N11Formalization.EnergyTerminalBatchB13Main`; then require a fresh root
  CI build and update the acceptance/handoff record only if that scope is met.
  No new Lean lemma is needed for this switch; `full_disk_bound_of_energy_b13_and_seven_classes`
  already states the reduced conditional theorem.
- **Do not overclaim:** 1997 is root-reachable after the switch, not automatically
  accepted. The 389 residual, 0/7 classes, and arbitrary-center theorem remain
  unpaid until their own declarations and root build are green.
## Lane C
- **The seven refinements are real but inert.** Each module proves a scaled
  two-leaf refinement of one source node and a `new_radius` for that node; the CI
  exits and axiom reports above make these valid Lean certificates. The exact
  tree audits cover only 100 scale entries and 200 split inequalities, so they
  are diagnostics for matrix/tree shape, not substitutes for the green Lean
  targets.
- **Newest source hashes (SHA-256):** N2341
  `49a253b6429af4a68c6915678ca00ee4c3a0d7b1ce76664924d22c08a887f23f`, N3040
  `7fcd5e3b8d528dfd3602a1f84709ca66c54e78de198116caec28d8b47ac4e057`, N2965
  `fa6abd13bf6a12f0dc3b6fd90af620102c628bb307484866d20752844899306a`, N3440
  `6420041457438e3f3a9102f0995eabe64e99a48b74047c2d9391a0319a9e72b1`, N3589
  `02992f0cbc721f3f4ca087b5b28f5430ae8853513ff00e39891759c4a6362e1b`, N3623
  `7b3eca9d0c37c2889ccf4331f7ee69579be43ba9f1dd05696f2a5b5698f326ee`, N3633
  `8192fc0e83d46d600c9380f7d84da35f2b254dd1914de76e5eec12127723c59e`. Each is a 48-line
  generated certificate with large packet literals and bound `decide +kernel`;
  N3633's CI peak was about 8.3 GB, so these are not suitable for monolithic
  aggregation or repeated root rebuilds.
- **The red `FrozenCapPublicExcludedTree` is not progress.** It remains an
  additional conditional/exclusion wrapper; its row-cap leaves still time out
  or have unsolved goals. Do not revive the 700-leaf row-cap family or restore
  more archive blobs until a paid-set consumer is green.
- **Highest leverage: one consumer batch, not more certificates.** Activate
  `EnergyTerminalResidualCensus` (B13 is now green), then add
  `EnergyTerminalBatchB14.lean`:
  `def newIDs := N2341.newIDs ∪ ... ∪ N3633.newIDs`;
  prove `new_subset_residual : newIDs ⊆ B13.residualIDs` using
  `EnergyTerminalResidualCensus.residualIDs_eq` and bounded chunk0 checks for
  the seven literals; prove `disjoint_paid : Disjoint B13.paidIDs newIDs` from
  `B13.mem_residualIDs_iff`; then prove
  `paid_count : (B13.paidIDs ∪ newIDs).card = 2004`,
  `paid_radius`, and
  `remaining_of : B14.RemainingTerminalRadius -> B13.RemainingTerminalRadius`.
  Only this CI-green consumer moves energy from 1997 to 2004 (residual 389 to
  382). If the census is red, fix only its first compilation error; do not put it
  back into B13Main.
## Risks
- **Root OOM:** the root target is red at 1788 s in
  `SharedMomentConcreteSwitchBatch`, with about 14.4 GB resident and the
  863 MB guard killing Lean. This is a resource failure of an unrelated giant
  module, not a proof of B13 or a mathematical verdict; do not hide it as a
  successful root build.
- **Count conflation:** C450 36/36, B13 1997/2386, B13 residual 389, accepted
  310/2386, C exclusions 0/7, and the arbitrary-center theorem are five distinct
  scopes. A green component does not upgrade the global handoff.
- **Census conflation:** `EnergyTerminalResidualCensus` is not yet green by being
  importable; its 389 equality/cardinality claims need their own CI exit 0 before
  the residual count is kernel-proven.
- **Shape overclaim:** A's exact rational and CI-pending edge lemmas do not pay
  a sector, total, or `Q0Degree3AreaInput`; 0/7 is the only honest class count.
- **Resource blowups:** C's giant packet literals (N3633 ~8.3 GB), A's exact
  degree-28 `norm_num` checks, and row-cap leaves are OOM/heartbeat risks. Keep
  targets serial and split; never raise heartbeats or admit `maxHeartbeats 0`.
- **Artifact substitution:** hash pins, restored blobs, exact-rational audits,
  Python closure reports, and manifest checks are not kernel proofs. Keep them
  as provenance and diagnostics only.
