# energy line — C921 energy terminals (henergy = EnergyTerminalBatchB11.RemainingTerminalRadius)

Nothing here is paid. Python/core-Lean results are PRE-VALIDATION only; WIP-format Lean is uncompiled.

## Inventory (step 1)
* Obligation (wip/lean/N11Formalization/EnergyTerminalBatchB11.lean): for every terminal node n of
  `DBMSourceTree.data` (Fin 5011) not in `Patch120SharpDispatch.sharpIDs` (120) and not in `paidIDs` (310),
  every y in the closed Fin9 simplex whose `tlift` lies in the node's DBM cell (scale 4096) and every
  Feasible (C,Z,r) gives sourceRadius ≤ r.
* Terminals: 2506 = 2386 energy + 120 sharp; paid 310; remaining 2076 (parse.py → ids.json). Matches HANDOFF.
* Paid certificate types: 274/310 use the Paid16 packet (Paid16CellCertificate.Packet/Valid:
  16 paid harmonic fields, rounded weights, 36 cosine line packets, ≤7 DBM dual rows, rmin, strict T² check)
  — Paid16GeneralG01..G12 (252) + Paid16Batch22Packet (22). The other 36 are bespoke
  (EnergyCommonChart 284/562/4348, 984, 1112, 2166, 2162, Lambda0Batch7, Lambda0TangentChordC01,
  CuttingPlaneBatch7, 3436, 4179, 4265, 4267).
* The "1687 candidate routes" are HOST proposals (wip/STATUS.md: "next512 gives 505, rest1515 gives 1182").
  They are NOT shipped in n11-wip-0001 nor in the n11-supplement release (supplement = C450 logs/inputs only;
  supp/n11-supplement-FILES.jsonl.gz, sha256 e7fca1ae…bca4 verified). So I regenerated certificates.

## Files
* parse.py → parsed.json (tree 5011 nodes, paid packets, weights), ids.json
* checker.py — exact Fraction transcription of Paid16CellCertificate.Valid (+ all helper defs)
* control.py → control-results.json (positive 274/274, 10/10 negative controls rejected)
* gen.py → certs/<node>.json (single-cell packet or failure), ledger.jsonl
* refine.py → refine/<node>.json (long saddle iteration + Kelley upper bound diagnostic)
* split.py → split/<node>.json (refinement tree by DBMTreeKernel split rule, leaf packets checked exactly)
* emit_lean.py → lean-wip/N11Formalization/Paid16GeneralH001..H083, HAgg01..09, HAll, EnergyTerminalBatchB12 (+MANIFEST.json)
* roundtrip.py → roundtrip-results.json (emitted Lean text re-parsed and re-checked: 1734/1734)
* emit_split.py → lean-wip/…/EnergyRefineNxxxx, EnergyRefineAgg*, EnergyRefineAll, EnergyTerminalBatchB13 (DRAFT)
* lean-wip/N11Formalization/Paid16MatrixCellCertificate.lean — DRAFT generic explicit-matrix certificate + refinement consumer
* lean-core/EnergyReplay/{Kernel,Weights,Controls}.lean, Grp/*.lean — core-Lean kernel replay (validB_sound → ValidQ)
* gen_core.py, runlean.py, logs/core-build.jsonl
* summarize.py → RESULTS.json, classification.csv
