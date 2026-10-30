# EXPERT REVIEW - n=11 Lean lanes

**Date:** 2026-10-30 (UTC)

**Scope:** `n11/work` HEAD `a8b025f8`; latest Lean-bearing commit `cc04268c`.
Completed evidence is run `41119359460` on `6937fb90`, with run `41123531381`
still pending. I read the lane notes/targets, guidance/state, recent commits,
CI summary and full job log, and the newest A/B/C Lean files. No Lean, lakefile,
toolchain, or manifest edit; no full build; no commit.

## Overall

- The genuine gains are C450 completion and the core B13 aggregate. C450
  `36/36` is imported and CI-green. B13 is CI-green at `1997/2386` paid with
  `389` conditional residual ids; the root still imports B12, so this is not
  root-reachable current credit.
- Seven-class exclusions remain `0/7`. No lane has produced a theorem of the
  arbitrary-center full-disk statement, and no row-cap or singleton refinement
  is itself a class exclusion.
- CI “success” is not a Lean verdict: the workflow ends `true`, while
  `summary.json` records individual exits. At `6937fb90`, EndpointChecks, all
  lane-B row caps, Thirteen, and the public excluded tree exit 1; many later
  Lane A exits are dependency failures.
- Lane A's claim that EndpointChecks and all 42 edge-shape facts are green at
  `1b2fa7a8` is factually wrong. That run's summary has EndpointChecks and
  every downstream edge/sector target at exit 1. The C450 targets are green.
- No float LP, `sorry`, new axiom, `native_decide`, or `maxHeartbeats 0` was
  found in the reviewed newest files. Exact Fractions, byte hashes, tree
  audits, and manifests are diagnostics unless a kernel-green consumer uses
  them. `decide +kernel` is confined mostly to bounded literal blocks, but
  large rational tables and repeated `norm_num` remain the main build risk.

## Lane A

- **Verdict: sound reduction, currently blocked before any intended count
  reduction lands.** The q0-degree-three reduction to exact edge/sector
  maxima, cosine monotonicity, and finite witness checks are mathematically
  coherent. Only row 0 bins 0--4 are addressed, i.e. `5/72` row-bin
  obligations. There is no `SectorBinUnimodal` assembler, `SectorValid`,
  strict total bound, `Q0Degree3AreaInput`, or exclusion proof.
- **Current CI:** at `1b2fa7a8`, `SevenClassQ0Deg3EndpointChecks` and
  `UpperReductionUnimodal` are red, as are EdgeSuffix, EdgeShape, SectorPeak,
  SectorShape, SectorCalculus, BinShape, BinWitness and BinWitnessBounds by
  dependency. `SectorBin0` is also red. Bins 1--4 were added after that run
  and are CI pending; none is kernel-green.
- **Endpoint diagnosis:** at `EndpointChecks.lean:217--231`, the goals retain
  `![...] 2`, etc.; `norm_num` does not reduce those vector lookups. Lines
  245/257 then report `No goals to be solved`. This is tactic plumbing, not a
  numerical counterexample, but it stops the whole q0 chain.
- **Mathematical bug:** `SevenClassQ0Deg3SectorBin2.lean:127` allows
  `n = 543`, while the called `sectorValue_zero_dec_of_bin2` requires
  `544 ≤ k.val`. The claimed exact `543 -> 544` step is absent, so the stated
  decreasing lemma is not proved.
- **Highest leverage:** stop emitting isolated bins. First split endpoint
  scalars out of vector literals and re-green EndpointChecks, then add the
  `543 -> 544` step, then one row-0 `SectorBinUnimodal` assembler. Concrete
  forms: `theorem nodeBinAt_two_eq : nodeBinAt 2 = 133/625 := by rfl` (or
  `simp only [nodeBinAt]; rfl`), and
  `theorem sectorAt_zero_bin2_step_543 : sectorAt 0 544 ≤ sectorAt 0 543`.
  For endpoint bins, use scalar `endpointUBin0 : ℚ := ...` definitions and
  eight `simp only [...] ; norm_num` leaves; do not reuse the vector inside
  every branch.
- After that assembler is exit 0, prove `SectorValid`, then the strict total
  and edge instantiation. Do not call the q0 reduction paid before those.

## Lane B

- **Verdict: B13 is the strongest real result; the row-cap work is a dead
  end.** The B13 union/disjointness/radius chain is correct and green. The
  singleton refinements already give `N3112`, `N3116`, `N3431`, and `N3573`
  green, but they are not combined, so the ledger remains `1997/2386` with
  residual `389`.
- At `6937fb90`, core B13 and the existing Eleven/Eight/Seven wrappers are
  green, while `Refine0037`, `RefineTwelve`, and `RefineThirteen` are red. The
  old `0037` error was `omega` at line 240; the current literal-block repair is
  in the pending `cc04268c` run and is not yet credit.
- All seven `LaneBFrozenCapRowCap*` targets are red at `6937fb90`, with
  unresolved `![...] 2` lookups. Even a repaired cap would not supply the
  missing `f0Lo`/`g` hypotheses needed to pay a radius.
- **Highest leverage:** after `Refine0037` gets exit 0, create one aggregate
  `EnergyTerminalBatchB13RefineSixteen.lean` combining
  `RefineEleven.newIDs` with `N0037`, `N3112`, `N3116`, `N3431`, and `N3573`.
  Prove `paid_count = 2013`, transfer `remaining_of` to B13, and expose
  `RemainingTerminalRadius` with residual `373`. Keep the proof hierarchical:
  `newIDs := RefineEleven.newIDs ∪ N0037.newIDs ∪ ...`; use singleton
  `rw [EnergyRefineNxxxx.newIDs, Finset.mem_singleton]` and the existing
  `not_paid_*` lemmas, not a single giant `decide`.
- The supervisor-only root switch B12Main -> B13Main changes reachability, not
  the conditional residual count. Do not add row-cap content or B14 while the
  aggregate is pending.

## Lane C

- **Verdict: diagnostics are improving, but no seven-class or energy count is
  moving.** The exact row-cap generator is not a proof of `f0Lo`/`g`, and the
  public excluded-tree theorem only concludes `False` from an already-valid
  packet with fixed node, `hf0`, and `hg`.
- At `6937fb90`, `FrozenCapRowCap1409/2337/2341/2360/2368/2370` built as
  dependencies, but `FrozenCapRowCap2356` timed out at
  `FrozenCapRowCap2356.lean:33` after 200000 heartbeats; consequently
  `FrozenCapPublicExcludedTree` exits 1. This is a resource failure in a giant
  rational table, not a cap counterexample.
- Even after repairing `2356`, `excluded_*_tree` has no consumer that yields
  `RemainingTerminalRadius` or `SevenClassExclusions`. The missing bridge is
  the mathematical bottleneck; a green 700-leaf file would still pay zero.
- **Highest leverage:** state and prove (or explicitly report absent) the
  bridge from an actual terminal cell to a `PaidCellCertificateM.Valid` packet
  with frozen `F0`/`G`, then derive infeasibility via `excluded_*_tree`. A
  useful target shape is
  `theorem excluded_1409_of_cell ... : ¬ Feasible ...`, with hypotheses that
  construct the packet and `hf0`/`hg`; do not regenerate 700 leaves until this
  endpoint exists.
- If continuing the row probe, isolate only `row_cap_2356_0_0`. Replace the
  nested `![...] i j` lookup with ten scalar row definitions and prove scalar
  `db_...` equalities by `rfl` or `norm_num`; get one leaf exit 0 before
  touching the full module.
- Exact rational audits, archive hashes, and float-LP search are generation or
  diagnosis only. No manifest-derived fact counts as a Lean payment.

## Risks

- Do not read the workflow's green check as a module verdict; use
  `summary.json` and fresh `=== EXIT target 0` lines.
- Do not promote the pending `cc04268c` run or the unmerged singleton results
  into the accepted ledger. The latest completed conditional numbers remain
  B13 `1997/2386`, residual `389`, exclusions `0/7`.
- The root's `SharedMomentConcreteSwitchBatch` OOM is an infrastructure/build
  risk, not a mathematical disproof and not credit for B13.
- Giant rational literals, repeated `norm_num`, and 72 row-bin comparisons can
  hit heartbeat or memory limits. Split scalar facts and use definitional
  reduction; do not hide failures with a heartbeat increase.
- Preserve frozen certificate bytes and exact quantifiers. Hash pins, decimal
  displays, cached summaries, and byte audits cannot replace a kernel-checked
  radius or exclusion.
