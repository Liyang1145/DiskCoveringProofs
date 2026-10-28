# Lanes (one dsf worker each)

## Lane A — C450 chain completion (restore the two HARK-MISSING modules)
Goal: write `N11Formalization/C450ChainCompletion.lean` and `C450ChainCompletionMain.lean`
that assemble all 36 C450 segments (`C450FirstSegment…C450NinthSegment`,
`C450Source11Segment…C450Source36Segment`) into the chain theorem the stage-1 root expects.
Steps: (1) grep how earlier C450 aggregate/"Main" modules combine segments (e.g. any
`C450*Chain*`, `C450*Main*`, telescoping in `evidence-20261014/c450-emit-20261014/verify_telescope.py`,
`segment_gate_verdict.py`); (2) infer the exact statement consumers need (grep for uses of
the residual `C45025`/C450 remaining credit, `C450Source13Segment` pilot integration);
(3) emit both modules (prefer a python emitter), add them to lanes/A/TARGETS.txt, and request the root re-import.

## Lane B — energy stage 2 top aggregate + B13 (HANDOFF §5, exact steps)
1. `Paid16GeneralNext1182.lean`: `newIDs := Finset.univ.biUnion part`,
   `part : Fin 8 → Finset (Fin 5011) := ![S01.newIDs, …, S08.newIDs]`; `new_count` by
   `Finset.card_biUnion` + 28 pairwise `decide +kernel` disjointness facts (≤168×168 each);
   dispatch membership by `mem_biUnion` + `fin_cases`.
2. `EnergyTerminalBatchB13.lean`: `paidIDs := B12.paidIDs ∪ Next1182.newIDs`, `paid_radius`,
   `RemainingTerminalRadius` over 389, `remaining_of : B13.Remaining → B12.Remaining`.
   Disjointness B12 vs Next1182 is NOT interval-separable: split it hierarchically
   (B12 = B11 ∪ Next505 parts; Next1182 = 8 parts → many small pairwise decides).
3. `EnergyTerminalBatchB13Main`: `B13.Remaining → SevenClassExclusions → N11MainStatement`.
   Add targets to lanes/B/TARGETS.txt; request root import of B13Main.
Inputs: `evidence-20261028/evidence/{emit_aggregate_hier.py, Paid16GeneralNext1182-hier-manifest.json, rest1182-emission-manifest.json}`.

## Lane C — energy residual 389 (raise the dual-row cap)
Census: 354 method failures + 35 zero-dual ids; near-miss deficits ≤ 6.8e-5, in `f0Lo − lamB`.
`CertifiedFieldMixtures.radius_of_dual {n m}` is generic; only `Paid16CellCertificate.Packet`
hard-codes `Fin 16` fields / `Fin 7` rows. Task: (1) python, exact rationals: for the failing
records re-solve the dual LP with m = 10/12/16 rows (scipy/highs float search, then exact
rational rounding + exact recheck `lower − gap = T²`, pass ⇔ gap > 0); report how many of the
354 become passing; (2) design `PaidCellCertificateM` (generic rows) reusing the same checker
lemma; (3) emit packets for newly passing records in small modules. Leads:
`evidence/codex-handoff/harmonic-fields-b01-proposal.json`, `-b02-`.
Never fake a pass: every claimed record needs an exact-rational recheck script committed.
