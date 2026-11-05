EXPERT (2026-11-02):
- Treat C450 as complete pending supervisor root import; stop spending cycles on it.
- Highest leverage (once FOCUS lifts the q0 pause): `SevenClassQ0Deg3Q0Exclusion.q0_degree3 : Q0RunExclusion 1`; put it first in A CI and hold other new targets.
- Required green endpoints: `q0Degree3AreaInput`, `q0_degree3`, clean axioms; this is at most 1/7.
- On red repair the first `SectorPeak00..08` or edge-peak owner only; split each failed peak into its own module.
- Replace failed 2k-bit `decide +kernel` leaves by explicit `sectorUpper`/`edgeUpper` unfolding plus denominator-normalized `norm_num`; no decimals or heartbeats.
- Freeze q0(5,8): its source is 9-decimal rounded float LP data with an external interval certificate, not an exact Lean dual proof.
- q0(5,8) may resume only after a concrete `ClosureFactorBounds` instance: 11 face, 9 switch, 9 sector bounds and a strict rational total.
- Do not report q0(5,8) or local arithmetic audits as class-exclusion credit.

# Lane A notes

CURRENT (session 196, 2026-11-05): **TARGET-DONE and now CI-GREEN.**  Lane-A
FOCUS target = restore `C450ChainCompletion` + `C450ChainCompletionMain` (root
`-- HARK-MISSING` lines 1952--1953).  Both modules exist and, per the FULL CI
job log of run 41847982412 (sha `6e67ed3a`, job `126636432190`), the build loop
recorded

    === EXIT N11Formalization.C450ChainCompletion 0
    === EXIT N11Formalization.C450ChainCompletionMain 0
    === EXIT N11Formalization.C450ChainCompletionAudit 0

so the lane-A FOCUS target is now **paid by a kernel verdict**, not merely
source-audited.  All C450 `depends on axioms` reports in that log are exactly
`[propext, Classical.choice, Quot.sound]` (0 dirty).  Only the supervisor-only
root edit remains.

## Ledger

- CI-GREEN lane-A targets: `C450ChainCompletion`, `C450ChainCompletionMain`,
  `C450ChainCompletionAudit`, `SevenClassQ0Deg3Cos`, `...Mono`, `...Bins`,
  `...EndpointChecks`, `...UpperReductionUnimodalBase`, `Peak00`, `Peak01`.
- Why earlier sessions said "no kernel verdict": `ops/ci/LATEST.md` embeds only
  the first 6000 chars of `summary.json` (workflow prints `json.dumps(s)[:6000]`),
  and the loop order is C,B,A,BUILD_TARGETS,root -- so lane A's exits fall off
  the end of that dump.  Reading LATEST.md alone can never show lane-A verdicts.
- `LATEST.md` run-conclusion "success" is NOT a math verdict: the Build step ends
  with `true`, so the step succeeds even when 136 targets exit 1.
- Root `N11Formalization` exits 1 in the same run, but NOT from lane A: the root
  build was OOM-GUARD-killed on `SharedMomentConcreteSwitchBatch` (a lane B/C
  generated table) at step 10725/10727 after 1002 s.  Fixing that is B/C scope.

ROOT-IMPORT REQUEST: import the CI-green `C450ChainCompletion` and
`C450ChainCompletionMain` in the stage-1 root (supervisor-only edit).  The two
imports themselves are already kernel-green; nothing else in lane A is pending.

## New tooling this session (STATIC / log-observation, not new kernel runs)

- `audit_c450_ci_kernel_verdict.py` -> `c450-ci-kernel-verdict.json`: fetches the
  FULL job log (read-only GitHub API) or parses a local copy (`--offline LOG`),
  reports the exact lane-A `=== EXIT` lines, aggregate exit counts (211 zero /
  136 nonzero / 347 total) and every C450 axiom report (18 181 decls seen, 0
  outside `[propext, Classical.choice, Quot.sound]`).
- `audit_ci_target_order_starvation.py` -> `ci-target-order-starvation.json`: lane
  A's first target is position 270/346 (269 targets precede it), so a run killed
  early starves lane A; run 41847982412 completed all 347 exits, so it did reach
  lane A.  `audit_ci_lane_a_reachability_empirical.py` confirms runs 41794012819
  and 41769569707 stopped mid-lane-B before reaching lane A.

## Condensed history

- Pre-session-175 (115--153): exactly audited 21 edge peaks, 21 discrete peaks,
  18 441 sector points, 72/72 bins, 18 369 within-bin steps, 63/63 jumps, bin-3
  (256 nodes / 32 640 pairs).  Global sector unimodality refuted; valid route is
  bin-wise.  142--153 split 21 edge + 9 sector peaks; C450/Main/Audit, `Cos`,
  `Mono`, `Bins`, `EndpointChecks`, `UpperTables` reported CI-green; root still
  carried both HARK markers.  158--167: `SevenClassQ0Deg3Repaired.lean` = frozen
  SHA `48d41f5d...5b61` + census import + ear-count open; direct import of
  `SevenClassQ0Deg3` fixed the closure audit (PASS, 115 refs / 76 modules).
- 175--184 (q0(5,8) closure): q0(5,8) stores 121 coefficients as decimal strings
  and `z` as floats (not a Lean source).  `reconstruct_q0_degree5_exact.py` ->
  `q0-degree5-exact-source.json` (SHA `900d2186...f41d`);
  `emit_q0_degree5_source_data.py` -> `Q0Degree5SourceData.lean` (121 exact
  rationals).  Interface obstruction: canonical formula lacks the `Fin 9` closure
  field; exact `canonical_minus_source = 195718067274616349/100000000000000000`.
  `Q0Degree5ClosureExtension.lean` adds `ClosureSectorCoordinates`,
  `ClosureFactorBounds`, `ClosureCertificate`, `total_lt_pi` and proves box
  nonnegativity + `[0,pi]` ranges -- all CI **pending**.
- 185--195 (C450 chain restore + static audits, all SOURCE-static, NOT kernel
  verdicts at the time): `verify_chain_completion.py`,
  `audit_c450_import_closure.py` (closure 1769, missing `[]`),
  `audit_c450_root_import_safety.py` (26/26, 2481 modules),
  `audit_c450_transfer_shapes.py` (58 checks),
  `audit_c450_consumer_signatures.py` (13/13),
  `audit_c450_import_paths.py` (closure 1816, all three `maxHeartbeats 0`
  modules reachable only via `SourceExactRoot`),
  `audit_c450_chain_wiring.py` (26/26 segments, 25 transfer edges, targets
  11--35), `audit_c450_decl_collisions.py` (streams >3 MB files;
  `PASS_C450_DECL_NO_COLLISION`, 2480 modules, 0 collisions of the 10 new
  fully-qualified names), `audit_root_maxheartbeat_exposure.py` (root already
  imports all three `maxHeartbeats 0` modules directly, so the chain imports add
  no new exposure), `audit_q0_degree5_static.py` (2/2 PASS).

## Chain architecture (verified against the live source this session)

`c450Segs` has 36 entries.  Each module `C450XSegment` defines
`remainingSegs := c450Segs.drop k` and `RemainingSourceObligation :=
∀ s ∈ remainingSegs, SegmentNormalized s`.  The base `C450Source36Segment` has
`drop 36 = []` (vacuous) and proves `source36_paid` directly; its
`source35_remaining_of_remaining` adds `source36` via `source35_remaining_split`.
The same pattern (`sourceNN_remaining_split : C450Source(NN)Segment.remainingSegs
= source(NN+1) :: remainingSegs`) runs 36 down to 11; `h450` is the 25-step
nested application and lands on `C450Source11Segment.RemainingSourceObligation`.
`C450Source11Segment.source_of_remaining` then descends 11->10->...->1 via
`C450FirstSegment.first_paid` and each `X_paid`.  `C450ChainCompletionAudit`
proves `source36 ∈ C450Source11Segment.remainingSegs`, i.e. the empty drop-36 tail
does not itself pay source36 -- the last segment is added by the 35-to-36
transfer, as PROJECT_STATE warns.

## Still unproved / unpaid (lane A view)

q0(5,8) `ClosureFactorBounds` (11 face, 9 switch, 9 sector + strict total);
q0(3)/q1 tables and `q0Degree3AreaInput`; the seven metric-class exclusions;
energy residual 389; the arbitrary-centre full-disk theorem.  q0 stays PAUSED
per FOCUS until C450 is root-imported and green.

## Very next concrete step

Supervisor-only: apply `root-import-c450.patch` (uncomment root lines
1952--1953), push, let `n11-lean-build` finish.  The C450 imports themselves are
already kernel-green; the root will still exit 1 until lane B/C fix the
`SharedMomentConcreteSwitchBatch` OOM.  On green, lift the q0 pause and resume
lane A at `SevenClassQ0Deg3Q0Exclusion.q0_degree3`.
