# Expert review — n=11 Lean lanes

**Date:** 2026-10-31 (UTC)

**Scope:** source HEAD `ae211d7a`; latest complete CI evidence is run
`41182882564` on `7f7e6f3b`. The working-tree `ops/ci/LATEST.md` points to a
cancelled run with empty summary/log and is not evidence. I read the guidance,
lanes, progress, targets and current Lean; I did not edit Lean, lakefile or
toolchain, run a full build, or use the status manifest as proof.

## Overall

- **Verdict:** Lane B is the only lane currently converting a sound argument
  into kernel-paid count reduction. Lane A has a sound finite-table reduction
  but no fresh kernel evidence. Lane C is generating conditional arithmetic
  and has not moved either open count.
- **Paid energy:** B13 is kernel-paid at `1997/2386` (389 residual). The green
  Seven/Eight/Eleven/Twelve/Thirteen chain raises the green aggregate to
  `2010/2386` (376 residual in its predicate). `2013/373` is arithmetic waiting
  on Fourteen/Sixteen CI, not a paid count.
- **C450:** `C450ChainCompletion`, `Main` and `Audit` were kernel-green, but
  both completion imports remain commented in `N11Formalization.lean`. The
  reconstruction is therefore not root-reachable.
- **Seven classes:** still `0/7`. No `Q0RunExclusion`, `Q1RunExclusion`, or
  `SevenClassExclusions` instance is proved. A's degree-three path would be
  one of seven, not a full closure.
- **Evidence rule:** workflow-level `success` on `41182882564` is a false green;
  the artifact contains many nonzero per-target exits. Only `=== EXIT ... 0`
  artifact lines for the exact source commit count. A cancelled/blank run,
  static audit, hash, manifest, decimal/float search or textual gate counts zero.
- **No hidden proof shortcut found in the newest reviewed modules:** no source
  `sorry`/`admit`, new axiom, `native_decide`, `ofReduceBool`, `implemented_by`,
  or `maxHeartbeats 0`. `decide +kernel` appears only on small literal/card
  facts in the reviewed B modules; that is valid but must not be broadened.

## Lane A

- **Verdict: mathematically sound, operationally promising, currently unpaid.**
  The q0 degree-three argument reduces the arbitrary chart to 21 edge and 9
  sector shapes, factors each by unimodal/endpoint checks, and supplies an exact
  canonical strict-total bound. This is a coherent route from finite table data
  to `Q0Degree3AreaInput`; it is not merely a hash-pinned claim.
- **Credit today:** C450 modules are green (but not root-imported). The last
  complete run has `EndpointChecks` and upstream targets green, then first owns
  errors in `UpperReductionUnimodal` and `SectorPeak`; later A targets were
  dependency-red. Those downstream reds are not independent evidence.
- **Current repair:** HEAD adds explicit `edgeUpper` unfolding to all 21 edge
  peaks and fixes sector namespace/open resolution. The source gates pass, but
  no CI at `ae211d7a` has checked the resulting terms. Treat every A target from
  the two peaks onward as CI-pending.
- **Highest leverage:** one fresh **serial** run, in dependency order, for
  `UpperReductionUnimodal`, `SectorPeak`, `EdgeSuffixNonpos`, `EdgeSuffixHigh`,
  `EdgeShape`, `SectorShape`, `SectorCalculus`, the bin modules,
  `TableBounds`, `RelabelledTableCertificate`, and `StrictTotal`. Repair only
  the first owning diagnostic; do not patch dependency-red descendants.
- **Acceptance lemma after green:** prove the consumer in a separate small file
  ```
  theorem q0_degree3 : ActualMetricClassReduction.Q0RunExclusion 1 :=
    SevenClassQ0Deg3.q0_degree3_of_areaInput
      SevenClassQ0Deg3StrictTotal.q0Degree3AreaInput
  ```
  It is valid only if both imported modules exit 0. This would record 1 of 7
  classes; the other six remain entirely unpaid.
- **Tactic/file guidance:** keep exact rational leaves as `norm_num` on named
  constants with explicit unfolding; never replace them by decimal comparison.
  `EdgeShape` is already 1213 lines, so split generated peak blocks if serial CI
  shows memory/time pressure, not by hiding failures with heartbeats.

## Lane B

- **Verdict: sound and the highest-confidence real reducer.** The hierarchical
  singleton/union refinement correctly enlarges `paidIDs`, proves disjointness,
  transfers `RemainingTerminalRadius`, and keeps the seven-class premise
  explicit. The arithmetic from 2010 to 2013 via sixteen singleton IDs checks.
- **Credit today:** B13 `1997`, then the green chain through Thirteen at `2010`.
  Fourteen's repaired count and both Fourteen/Sixteen Mains are CI-pending, so
  `2013/373` must not be recorded yet. The 373 radii themselves remain open.
- **Current repair:** `EnergyTerminalBatchB13RefineFourteen.lean:60-63` now
  rewrites the disjoint union/card and closes with
  `simpa [newIDs] using EnergyTerminalBatchB13Refine3116.new_count`. This
  addresses the prior alias mismatch without changing certified fields.
- **Highest leverage:** serialize only `EnergyTerminalBatchB13RefineFourteen`,
  `RefineFourteenMain`, `RefineSixteen`, and `RefineSixteenMain`. Require all
  four exits `0` and check `#print axioms` for `paid_radius` and `remaining_of`.
  Then the supervisor may switch the root from `B13Main` to `SixteenMain`.
- **Acceptance obligations:** `paid_count : paidIDs.card = 2013` and
  `remaining_of : RefineSixteen.RemainingTerminalRadius →
  EnergyTerminalBatchB13.RemainingTerminalRadius` must both be green before any
  count is quoted. This pays only sixteen singleton refinements; it does not
  price the remaining 373 radii or any class exclusion.
- **Risk control:** do not expand `decide +kernel` or `maxRecDepth` to larger
  blocks. The generated refinement files are large; if one module becomes slow,
  split singleton facts into separate imported modules rather than creating one
  giant decision term.

## Lane C

- **Verdict: the arithmetic may be correct, but the proof route is incomplete
  and currently pays nothing.** The seven row-cap modules were kernel-green in
  `41182882564`, yet each proves only `not_valid_of_frozen_cap`: given a packet
  with the exact frozen node, `f0Lo` and `g`, a fixed rational weight contradicts
  `Valid`. That is a conditional exclusion, not a residual radius theorem.
- **Missing mathematical bridge:** there is no theorem producing such a
  `PaidCellCertificateM.Packet` from a feasible chart at `r < sourceRadius`, nor
  proving the packet's `f0Lo`/`g` equal the frozen vectors. Without both, the
  row caps cannot contradict a feasible counterexample. Treat the seven caps as
  inapplicable until this producer/canonicality obligation is stated and proved.
- **Coverage:** the exact census is 389 IDs, but only seven public payloads
  `{1409,2337,2341,2356,2360,2368,2370}` exist; 382 IDs have no public payload.
  Even seven unconditional exclusions would leave 382 radii untouched.
- **Current CI:** the fixed `FrozenCapRowCapTreeBridges` byte and the public
  tree/aggregate are pending. First serialize the fixed bridge, tree, and
  aggregate. Green there only fixes the conditional chaining; it is not payment.
- **Corrected arithmetic:** only `1409`, `2337`, `2341` currently have corrected
  four-field witnesses under `F0 + gain < T^2`. The exact five-field `2368`
  candidate is host-side only, `2370` timed out, and `2356`/`2360` have no
  sampled pass. The old five-record report is invalid and must not be consumed.
- **Highest leverage:** stop adding row caps. In a new Lean bridge module define
  a genuine residual consumer first, for example
  ```
  structure ResidualRadiusCertificate (n : Fin 5011) where
    radius : ∀ y hy0 hy1 hc C Z r, Feasible (chartAnchors y) C Z r →
      SourceExactRoot.sourceRadius ≤ r

  theorem remaining_of_residual_certificates
    (h : ∀ n ∈ EnergyTerminalBatchB13.residualIDs, ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := ...
  ```
  Then prove the missing packet-producer/canonicality implication that turns a
  failed `Valid` into `ResidualRadiusCertificate`. If that implication is not
  available, report C as blocked instead of manufacturing another cap.
- **Do not count:** exact 700/700 cap checks, `FrozenCapResidualMembership`
  membership/not-paid facts, corrected witness modules, float minimization, or
  a future `2368` emitter. None is a kernel radius proof until consumed above.

## Risks

- The blank working-tree `ci/LATEST.md` can erase the distinction between a
  repaired pending tree and a green tree. Cite the exact commit and artifact.
- Root integration is still absent: C450 imports are comments and the live
  energy import is only `EnergyTerminalBatchB12Main`. A lane-green module is not
  a root theorem.
- Giant generated Edge/sector and C row-cap files risk elaboration time and OOM;
  `SharedMomentConcreteSwitchBatch` has already exited 137 in earlier CI.
- Do not turn conditional predicates into counts: B's 373 and C's exclusions
  are obligations over residual data, not paid terminal radii.
- Manifests, byte hashes, float LP searches and `project_status.py --check`
  establish inventory/scope only. They cannot replace the required exact roots,
  quantifiers and kernel inequalities.
- Preserve frozen bytes and add wrappers/reports separately. The seven-class
  target remains `0/7`; no lane has earned a class exclusion yet.
