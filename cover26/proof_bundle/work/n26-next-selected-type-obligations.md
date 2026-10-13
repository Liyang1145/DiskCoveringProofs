# Latest continuation: conditional stage v1 + seven new complete type exclusions

2026-10-10. Goal ACTIVE. This goal turn made substantial ACCEPTED progress:
167 new whole-subtree exclusions, seven new full canonical types excluded,
legacy difficult-type OPEN boxes reduced31->16, actual current binding passed.
n26 global optimality NOT proved; n27 NOT started. This top section supersedes
all chronology below. Never edit frozen or audit-bound sources in place.

## Authoritative accepted state

1. outputs/n26-conditional-force-stage-v1:
   Source is accepted Rstar conditional partial forest3916, NOT original U.
   2400 events SPLIT1900 FORCE41 FORCE_TREE17 AREA109 EMPTY321 TERMINAL12.
   167 new strict radius-conditional whole transport subtrees excluded.
   Pending B14/B15/B16/B17=284/823/1757/1359=4223; terminal paths12.
   Native session3872 actually passed2400 events. Exact Windows session47924
   passed; actual published Windows session9371 passed and reports matched.
   outputs/n26-conditional-force-stage-published-replay-v1.json.
   Screen threshold U remains234701/1000000, but source/output scope is
   at-most-same-root-Rstar-not-original-U. New verifier explicitly distinguishes
   these and rejects scope promotion. 9 rejection controls passed.
   work/build_conditional_force_stage.py builds proper wrapper and keeps frozen
   base verify_force_stage arithmetic unchanged.

2. outputs/n26-conditional-terminal-catalog-v1:
   All12 current full terminal paths reconstructed, fresh one-node native solves,
   dictionary/BFS canonical codes, all vertex maps/boundary cycles/face images.
   11 distinct types: candidate group10, ten competitors groups0..9.
   Actual published replay matched:
   outputs/n26-conditional-terminal-catalog-published-replay-v1.json.
   Seven NEW competitor codes groups0..6, each one path.
   New groups7/8/9 have identical FULL canonical specs to legacy groups3/4/5;
   group9 has two paths. Never transport by group number alone.

3. Legacy old-source selected type v3:
   outputs/n26-selected-type-sharp-trees-v3 and actual published replay
   outputs/n26-selected-type-sharp-trees-published-replay-v3.json passed/matched.
   Source catalogue is still OLD selected-terminal-catalog-v2 (10 paths7 types).
   14234 nodes; old groups0/1/2 remain excluded. Old groups3/4/5 OPEN7/5/4=16.
   Counts old3:4317 nodes SPLIT2158 DIRECT862 CORRELATED1290 OPEN7.
   old4:4315 SPLIT2157 DIRECT563 CORRELATED1590 OPEN5.
   old5:4313 SPLIT2156 DIRECT538 CORRELATED1615 OPEN4.
   v2->v3 paid-node check outputs/n26-selected-type-continuation-v2.json:
   all8189 prior non-OPEN nodes and closed splits unchanged, added6014 nodes,
   old OPEN still OPEN9; no newly complete old type.
   Joint-angle rod optimization suggested29 exact whole-box integer-flow
   certificates among45 exploratory v4 OPEN; all29 paid through SAME existing
   correlated-force semantics, not numeric-radius acceptance.
   Discovery work/n26-selected-type-tree-proposals-v6-joint.json.
   Diagnostics work/n26-selected-all-pending-joint-diagnostics-v2.json.

4. Seven NEW complete types accepted:
   outputs/n26-expanded-type-registry-v1 and actual published replay
   outputs/n26-expanded-type-registry-published-replay-v1.json passed/matched.
   New types0..6 exactly replayed from full sharp roots: 255 nodes,
   124 SPLIT,131 CORRELATED_FORCE,0 OPEN.
   Other three current types7..9 explicitly REUSE old accepted v3 full type
   proofs (same full spec, root endpoint, caps and independently regenerated
   matrix, prior actual replay bound; NOT falsely called rerun).
   All10 current competitors accounted for. Candidate group10 positive control.
   11 rejection controls and force positive controls passed.
   Exactly7 current complete terminal paths removed from a new conditional copy.
   LATEST Rstar frontier=284/823/1750/1359=4216, terminal paths5 including
   unique known34-face candidate. Unresolved current competitors3, OPEN16.
   Source current catalogue remains the12-path pre-filter snapshot, correctly
   bound to conditional stage-v1.
   Original U stage-v12 frontier STILL3922 and10 terminals, unchanged.

5. Current audits:
   outputs/n26-conditional-stage-current-bundle-audit-v1.json actually passed;
   it semantically replays all2400 new stage events, new current catalogue,
   actual published replays, v3 pool and paid-node preservation. 25360 bound files.
   LATEST outputs/n26-expanded-registry-current-bundle-audit-v1.json
   actually passed; all25400 file digests rehashed after success.
   New type semantics and current partition reconstructed, prior full semantic
   replay remains bound to unchanged bytes. No claim to rerun old search.

Latest narrative:
outputs/n26-conditional-stage-and-refined-type-progress-20261010.md
outputs/n26-expanded-terminal-type-progress-20261010.md.
Old STATUS and all older supplements remain unchanged/frozen.

## LIVE process — never restart a confirmed live handle

Next conditional COMBINATORIAL discovery session7453:
work/propose_force_stage.py
--source outputs/n26-expanded-type-registry-v1/RSTAR-COMPETITOR-FRONTIER.json
--source-acceptance outputs/n26-expanded-type-registry-v1/VERIFIED.json
--output work/n26-conditional-stage-proposals-v2.json
--steps2400 --angle-checks7
--candidate-control outputs/n26-candidate-transport-control-v1.
Last confirmed live at2080 events, with64 unresolved terminal events already;
these are UNACCEPTED discovery. Source4216 and5 terminals.
After actual finish:

1. Use work/build_conditional_force_stage.py, NOT ordinary unconditional builder:
   --proposal work/n26-conditional-stage-proposals-v2.json
   --source-replay outputs/n26-expanded-type-registry-published-replay-v1.json
   --radius-basis outputs/n26-selected-type-sharp-trees-v3
   --radius-basis-replay outputs/n26-selected-type-sharp-trees-published-replay-v3.json
   --output outputs/n26-conditional-force-stage-v2.
2. Native audit, sealed verify_conditional_force_stage.py exact acceptance,
   actual published replay and compare. Native requires WSL Ubuntu2204.
   New conditional verifier is portable and DID pass on Windows; legacy full
   history still needs WSL because older manifests read /mnt/c paths directly.
3. Build fresh current terminal catalogue with unchanged build_terminal_catalog,
   fresh one-node native checks, actual published replay. Old generic catalogue
   proof has NO fixed10 assumption. Candidate control same original accepted one.
4. New current type proofs: map by (B, canonical_faces), never group index.
   Existing expanded_type_registry supports generic current catalogue + original
   selected type pool v3 protocol. It can replay new TREE proofs and REUSE old
   identical full types. It currently expects at least one TREE and REUSE in its
   rejection harness (true in latest dataset); handle future zero-case datasets
   with a NEW extension file if needed, not in-place edits.
5. Fresh current audit extension needed: existing current audit scripts hardcode
   previous dataset counts3916/4223. Do not blindly reuse those for v2 source4216.
   Bind all25400 prior bytes, actual new replay, all new siblings and terminals,
   and any new type filter to the actual source. Do not revert to an older
   frontier while omitting newer accepted closures.

## Finished explorations — do not restart or confuse with accepted state

- Breadth-only session44282 FINISHED:
  work/n26-selected-type-tree-proposals-v5-breadth.json.
  Old group3 nodes10199 OPEN1899, old4 nodes10285 OPEN1985,
  old5 nodes9905 OPEN1605. Still unaccepted; preserve it.
  Breadth alone made many small cells but no complete type. Accepted v3 instead
  follows v4 + joint-flow refinement and has only16 OPEN.
- Joint diagnostics session96723 and refinement61222 finished.
- Expanded seed session5691 and discovery8842 finished:
  work/n26-expanded-type-seed-v1.json maps legacy3/4/5 to current7/8/9.
  work/n26-expanded-type-proposals-v1.json contains complete new0..6 trees and
  extra unaccepted DFS refinements of old7..9 (OPEN17/11/12).
  Accepted expanded registry intentionally REUSES pool-v3 OPEN7/5/4, rather than
  pretending these different unaccepted DFS refinements passed. Both raw
  exploratory branches preserved.

## Research priorities toward actual global closure

Three difficult complete types remain; candidate103 OPEN boxes also remain.
Joint stationary-angle flow proposals were markedly better than midpoint-only
flow on old pending boxes (29/45 whole boxes paid without new splits).
Useful next discovery: hybrid midpoint + joint flow, then choose a split by
exact bounds on both children under inherited force candidates, not only width.
All accepted semantics can remain unchanged integer g/f/mu exact replay.
Unpaid joint coefficients currently are not retained by JointAngleSolver;
only paid ones are stored. The numeric helper is unbound in latest audits
(verify before editing), or make a fresh diagnostic copy returning multipliers/
unpaid flows for numerical Hessian/energy research. Numerical local minima
.2391463/.2382976/.2365413 are NOT global bounds.

Candidate continuation requires a NEW semantic loader for current continued-leaf
angles-v1. Existing n26_current_leaf_angle_source reconstructs only leaf-v2;
do NOT feed continued-leaf-v1 into it. First replay old leaf-v2, then use sealed
verify_continued_leaf_angles proposal_gate/replay_and_close to reproduce current
2161-node certificate/pending/ledger, then continue its103 OPEN while preserving
all old non-OPEN nodes and closed splits. Original100+5 HULL_LOCAL and all
force leaves must remain. Keep unchanged52-coordinate allowance7/800000.

Potential competitor weighted-Schur-energy route: test numerically before proof.
Candidate's fixed-energy angular Hessian was negative (~-.0443723), so shrinking
intervals cannot make that SAME reference convex. Different competitor stress
weights might help, but any accepted bound needs exact positive weights, exact
Dirichlet elimination, whole-domain Hessian/linear-dual bounds and strict
energy >Rplus^2 sum(weights), not floating eigenvalues.

## Frozen sources and scope

Newly bound work files include verify_conditional_force_stage.py,
audit_conditional_stage_current_bundle.py, expanded_type_registry.py,
audit_expanded_registry_current_bundle.py, plus all previously listed math
checkers. Do not edit in place; use fresh extensions.
New reports distinguish Rstar scope from conservative U screening. Original
U queues and all previous frozen bundles remain unchanged.
WSL sometimes exits1 silently before START. We checked no live foreground
process/target before retrying; it later recovered. Never restart a live task,
and do not restart global WSL services (unrelated API services run there).
Scientific Python C:/热爱单机但萌新/dependencies/python/python.exe.

Rstar strict interval and local allowance unchanged; Fejes Toth eight-disk lower
bound remains explicit external dependency. Full four-family catalogue, final
arbitrary-cover reduction joint acceptance and global same-root synthesis remain
incomplete. Only after full n26 global acceptance start n27.

---

# Earlier continuation: accepted stage-v12 plus sharp partial forest

2026-10-10. Goal ACTIVE. Last goal turn and this goal turn made genuine accepted
progress. n26 global optimality NOT proved; n27 NOT started. This top section
supersedes all chronological notes below. Never edit frozen or audit-bound files.

## Authoritative new accepted state

1. Original U stage-v12 accepted and actual published replay matched:
   outputs/n26-force-stage-v12/VERIFIED.json
   outputs/n26-force-stage-published-replay-v12.json.
   2400 events: SPLIT1931 FORCE16 FORCE_TREE4 AREA102 EMPTY337 TERMINAL10.
   122 new strict whole-subtree exclusions. Original U pending
   B14/B15/B16/B17=283/797/1578/1264, total3922, all10 terminals retained.
   Native session6822 and exact82122 and actual replay41055 all actually passed.

2. Complete type proofs transported independently to stage-v12:
   outputs/n26-stage-v12-Rstar-frontier-v1 and its actual published replay
   outputs/n26-stage-v12-Rstar-frontier-published-replay-v1.json passed/matched.
   All10 old selected terminal prefixes independently re-resolved on NEW stage,
   all state fields/faces/canonical codes/vertex maps/boundary cycles checked.
   Type0/1/2 exclusions remove exactly5 terminal paths from a separate conditional
   copy: 283/797/1573/1264=3917, 5 retained terminals including candidate.
   Original U frontier unchanged. Six rejection controls passed.
   Current audit outputs/n26-twelfth-stage-Rstar-current-bundle-audit-v1.json
   passed; all20310 bound digests rehashed after success.

3. Accepted SHARP PARTIAL FOREST:
   outputs/n26-sharp-partial-forest-v1/VERIFIED.json and actual published replay
   outputs/n26-sharp-partial-forest-published-replay-v1.json passed/matched.
   80 exact actual partial roots, 1656 tree nodes. One B16 existing28-face
   nonterminal subtree fully excluded: raw original source_index2602, 2 SPLIT
   and3 CORRELATED_FORCE leaves, no OPEN.
   This proof uses ONLY already-present rods, so valid for every completion.
   It is NOT misuse of a full-type local proof on an ancestor.
   79 other attempted roots and509 OPEN closed boxes preserved.
   New conditional frontier283/797/1572/1264=3916; retained terminals5.
   Original U remains3922 and10 terminals. 7 rejection controls and all ring/
   nonzero-dual positive controls passed. All matrices and leaf boxes independently
   reconstructed.
   Discovery work/n26-sharp-partial-forest-proposal-v1.json also independently
   scanned all3922 source sharp matrices; none empty. This full scan itself
   is discovery, not a claim made by the accepted80-root forest.

4. outputs/n26-partial-matrix-candidate-controls-v1.json actually passed:
   same-root isolation/cover and tiny-angle containment rechecked; all35 exact
   candidate partial prefix states rebuilt. BFS/Floyd vs all-pairs/Bellman-Ford
   agree at each prefix; completed sharp matrix implies each partial matrix;
   entire exact root tiny angle box survives all35 partial matrices.

5. Latest full current audit:
   outputs/n26-sharp-partial-current-bundle-audit-v1.json
   actually passed; all20355 file digests rehashed afterward.
   It keeps earlier complete semantic replays bound to unchanged bytes and
   actually reconstructs all new partial domains, trees, ledgers and partition.
   It binds both actual new standalone replays and all35 partial positive controls.
   Max candidate hull error and unchanged52-coordinate allowance7/800000 retained.

Latest user-facing supplements:
outputs/n26-twelfth-stage-and-type-transfer-progress-20261010.md
outputs/n26-sharp-partial-subtree-progress-20261010.md.
Old STATUS and all earlier supplements remain unchanged and still bound.

## LIVE processes — poll exact handles, never restart if live

A. Fair breadth-first selected type discovery, session44282:
   work/propose_selected_type_breadth.py
   --catalog outputs/n26-selected-terminal-catalog-v2
   --caps outputs/n26-sharp-radius-angle-caps-v2
   --seed work/n26-selected-type-tree-proposals-v4.json
   --output work/n26-selected-type-tree-proposals-v5-breadth.json
   --checks-per-type4000 --branch-depth20.
   Last live, group3 had1250 checks and721 queued boxes. It is UNACCEPTED.
   Motivation: DFS spent thousands of checks in one branch; many retained boxes
   still had widths0.03..0.20 turns. Breadth-first fairly visits all retained boxes.
   Previous v4 session87861 FINISHED. It has no new closed types:
   group3:4317 nodes OPEN17, group4:4315 OPEN15, group5:4313 OPEN13.
   v4 remains unaccepted discovery; it preserves earlier nodes by construction,
   and BFS seed gate replays it exactly. Do not report45 discovery boxes as the
   current accepted selected-type count (acceptedv2 still31).

B. New CONDITIONAL combinatorial discovery, session4207:
   work/propose_force_stage.py
   --source outputs/n26-sharp-partial-forest-v1/RSTAR-COMPETITOR-FRONTIER.json
   --source-acceptance outputs/n26-sharp-partial-forest-v1/VERIFIED.json
   --output work/n26-conditional-stage-proposals-v1.json
   --steps2400 --angle-checks7
   --candidate-control outputs/n26-candidate-transport-control-v1.
   Last live at680 events. Its source has3916 nodes and5 terminals.
   IMPORTANT: this continues a Rstar-CONDITIONAL frontier, NOT original U.
   Old discovery writes radius_threshold=U because force/area/angular payments use
   conservative U bounds; that field is the screening threshold, NOT permission
   to label the new reduced partition unconditional U.
   Output is UNACCEPTED; do NOT run the ordinary unconditional stage acceptance.

## Next acceptance work (conditional stage)

Keep the original U stage-v12 untouched. The conditional source is rigorously
accepted and already removes type5 terminal paths +1 partial subtree.
Existing proposer works on its exact pending-state rows. For proper acceptance,
build a fresh conditional stage wrapper/new verifier (do NOT edit frozen base):

- Reuse accepted verify_force_stage.replay_trace and frozen native event checks.
  Every original U screen, force>U bound, complete U-angular tree or U-area
  exclusion also holds on radius<=Rstar because Rstar<U.
- Replace only the source input gate/scope labels: source report must have
  radius_scope==at-most-same-root-Rstar-not-original-U, accepted source frontier
  families are source_report['conditional_frontier_families'] (not ['families']),
  bind source acceptance + its ACTUAL published replay, and certified Rstar
  endpoint from unchanged selected-type-v2 same-root acceptance.
- The source forest frontier has scope and exact actual pending_states; all old
  paid exclusions are already reflected in the source. Reconstruct every source
  state and every native sibling just as base stage verifier does.
- Publish output frontier/report with explicit Rstar conditional scope and
  radius_upper, while keeping screen_radius_threshold=U separate. Never claim
  missing source nodes are U exclusions. Check unique known candidate full
  terminal remains and every unresolved terminal/sibling retained.
- Existing build_force_stage_bundle can supply frozen kernel/base arithmetic,
  but its unconditional verifier will fail this source's missing ['families'].
  A fresh conditional builder should add sealed wrapper/proof and correct scope
  manifest; do not pretend base acceptance passed.
- Fresh native audit, exact acceptance, actual standalone replay, and a new
  current audit must bind previous20355-file chain plus new partition.

If new selected types close in BFS, accept with unchanged build_selected_type_trees,
actual published replay and verify_selected_type_continuation vs acceptedv2.
For a CURRENT conditional stage, old excluded5 paths are legitimately absent;
new transfer must only pay newly closed member paths still pending, and must
account for previously removed paths using prior accepted ledger. The helper
verify_successive_Rstar_frontier currently requires all10 in original U input,
so do not apply it blindly to a reduced conditional source.

## Newly bound sources — keep immutable

Work files now bound include verify_successive_Rstar_frontier.py,
audit_successive_Rstar_current_bundle.py, n26_sharp_partial_domains.py,
verify_sharp_partial_forest.py, verify_partial_matrix_candidate_controls.py,
audit_sharp_partial_current_bundle.py, plus earlier bound selected-type sources.
Use fresh extension files. All existing standalone verifiers are standard library.
Scientific discovery uses C:/热爱单机但萌新/dependencies/python/python.exe;
WSL Ubuntu2204 needed for historical native/full-stage workflows, whose system
python lacks numpy. WSL may silently exit before launch; check handle/process and
output existence before retrying. Never restart a confirmed live process.

Global n26 catalogue, candidate103 OPEN boxes, remaining selected competitor
types, final unrestricted reduction acceptance and global same-root synthesis
all remain incomplete. Fejes Toth eight-disk theorem remains an explicit external
dependency, not re-proved. Do not start n27 before full global acceptance.

---

# Earlier continuation: accepted selected type certificates and conditional frontier v2

2026-10-10. Goal ACTIVE. n26 global optimality NOT proved; n27 NOT started.
This turn made accepted mathematical progress. This top section supersedes the
older chronological notes below. Do not edit any bound source or frozen bundle.

## New authoritative accepted state

`outputs/n26-selected-type-sharp-trees-v2` and its actual published replay
`outputs/n26-selected-type-sharp-trees-published-replay-v2.json` passed and matched.
Every selected noncandidate group 0..5 accounted for; candidate group 6 excluded
from competitors and positively checked in source and reflected canonical gauges.

Groups 0/1/2 fully excluded for radius <=Rstar, covering 5 explicit complete
terminal paths (group sizes 1,1,3). Remaining groups 3/4/5 have 7/7/17 OPEN
closed boxes, total 31. Candidate angle tree independently retains 103 OPEN.
All bounds use the same certified Rstar upper endpoint, NOT original U.

Trees per group:
0: 125 nodes, SPLIT62 DIRECT5 CORRELATED58 OPEN0.
1: 63 nodes, SPLIT31 DIRECT0 CORRELATED32 OPEN0.
2: 1101 nodes, SPLIT550 DIRECT65 CORRELATED486 OPEN0.
3: 2307 nodes, SPLIT1153 DIRECT409 CORRELATED738 OPEN7.
4: 2307 nodes, SPLIT1153 DIRECT295 CORRELATED852 OPEN7.
5: 2317 nodes, SPLIT1158 DIRECT322 CORRELATED820 OPEN17.

New standard-library standalone verifier replays original/modified root
isolation, strict nested boxes, omitted-contact transport, same-root full disk
cover, all sine margins, selected terminal canonical evidence, all vertex maps,
BFS/Floyd vs all-pairs/Bellman-Ford matrices, independent BFS vs DFS closed leaf
boxes, exact strict direct/correlated force and all OPEN. 14 rejection controls
and ring/nonzero-dual positive controls actually passed.

`outputs/n26-selected-type-continuation-v1.json` checks v1->v2:
all 3388 old non-OPEN nodes and closed splits unchanged, 4786 added nodes;
all old unvisited OPEN retained. Accepted v1 and its audit remain bound.

`outputs/n26-selected-Rstar-competitor-frontier-v2` and actual published replay
`outputs/n26-selected-Rstar-competitor-frontier-published-replay-v2.json`
passed and matched. A SEPARATE conditional frontier only:
B14/B15/B16/B17=285/755/1312/1213, total3565, 5 retained terminals including
known candidate. Original U stage-v11 frontier unchanged at 3570 and10 terminals.
Only fully certified exact terminal members removed; no ancestor prefix reuse.

Current composite audit:
`outputs/n26-selected-types-current-bundle-audit-v2.json`
actually passed; all 15448 file digests rehashed after success.
It includes original full-chain semantic replay with all still-identical bound
bytes, new actual type and partition published replays, and paid-node
continuation. It does NOT pretend to rerun old search when reusing intact replay.
All earlier full-chain audits including leaf stage-v11 actually completed.
Max candidate hull error <8333/10^9 < unchanged7/800000 checked.

New user-facing narrative:
`outputs/n26-selected-type-and-conditional-frontier-progress-20261010-v2.md`.
Old `outputs/n26-STATUS.md` intentionally left unchanged because all audits bind
its exact bytes; use new supplement, not an in-place edit.

## LIVE / pending work — poll rather than restart

1. Selected-type exploration v4, session87861:
   work/propose_selected_type_trees.py with seed
   work/n26-selected-type-tree-proposals-v3.json, output
   work/n26-selected-type-tree-proposals-v4.json,
   --checks-per-type2000 --branch-depth44.
   Last confirmed running. Its eventual result is UNACCEPTED.
   Publish with unchanged work/build_selected_type_trees.py into fresh v3,
   standalone replay, paid-node preservation vs accepted v2, fresh conditional
   frontier and current audit. Do NOT change any old sealed source.

2. Broad next-stage discovery session75396 FINISHED successfully:
   `work/n26-force-stage-proposals-v11.json` (proposal for stage-v12).
   2400 events: SPLIT1931 FORCE16 FORCE_TREE4 AREA102 EMPTY337 TERMINAL10.
   Discovery suggests122 strict exclusions and pending283/797/1578/1264=3922.
   NOT accepted yet.
   WSL build of `outputs/n26-force-stage-v12` completed, preserved fresh bundle.
   Native event audit session6822 FINISHED and actually passed all2400 events:
   wsl Ubuntu2204 --exec python3 outputs/n26-force-stage-v12/audit_force_forest_native.py
   --input outputs/n26-force-stage-v12 (all paths absolute /mnt/c).
   Sealed exact stage-v12 acceptance is now LIVE session82122:
   wsl Ubuntu2204 --exec python3 stage-v12/verify_force_stage.py
   --input... --area-bundle outputs/n26-multislope-area-lower-v1
   --report stage-v12/VERIFIED.json. Poll; never restart a live process.
   After actual pass, run published replay to a fresh
   outputs/n26-force-stage-published-replay-v12.json, and compare reports.
   Historical audits use WSL. Scientific discovery uses Windows bundled Python;
   WSL system python lacks numpy (failed safely before proposal started).

Stage-v12 source remains ORIGINAL U stage-v11, not the conditional frontier.
If applying accepted selected types to stage-v12, must reconstruct a newly
accepted selected terminal catalogue or independently bind exact member paths
and isomorphisms to new source. Do not relabel v2 conditional frontier as a
partition of stage-v12, and do not alter original U queues.

## Frozen-source caution

Work files now bound by current audits include verify_selected_type_trees.py,
verify_selected_Rstar_frontier.py, audit_selected_types_current_bundle.py,
verify_selected_type_continuation.py and audit_selected_type_continuation_current_bundle.py.
Do not edit them in place. New extension uses a fresh file.
Both build scripts are copied into frozen bundles but their work originals are
not necessarily bound; still prefer unchanged reuse when sufficient.

All old numerical evidence and reduction cautions below still apply.

---

# Earlier chronological notes (superseded above)

Goal active. n26 global optimality NOT proved; n27 NOT started.
This goal turn made genuine progress, not a status-only turn.

## Accepted state

outputs/n26-continued-leaf-candidate-angles-v1:
2,161 nodes; 1,080 SPLIT, 215 FORCE, 549 SHARP_FORCE,
93 SHARP_CORRELATED_FORCE, 13 LOCAL, 105 SHARP_HULL_LOCAL,
3 SHARP_EMPTY, 103 OPEN. New payments: 473 strict direct-force leaves,
5 hull-local leaves; 504 complete closed splits. Old non-OPEN nodes unchanged.
857 total force leaves, 450 recorded bounds <= old U.
Maximum hull-local center error <8.333e-6 <7/800000.
The published replay actually passed and matched exactly.

outputs/n26-force-stage-v11:
2,400 events from accepted 3,331 source subtrees:
1,841 splits, 36 force, 6 force_tree, 115 area, 392 empty,
10 reprocessed inherited terminal events.
157 new strict whole-subtree exclusions.
Pending B14/B15/B16/B17=285/755/1317/1213, total 3,570.
All 10 terminals remain in B16 pending. Candidate owner is uniquely its
complete 34-step terminal, not the old two-face [24,40] owner.
Native audit, exact acceptance and published replay all actually passed.

outputs/n26-selected-terminal-catalog-v2:
Exactly the 10 explicit retained terminal paths were reconstructed and given
native one-node canonical solves plus dictionary/queue Python canonical codes.
All explicit vertex bijections, boundary cycles, face images, codes and
stabilizers matched. They form 7 distinct canonical types. Candidate type has
1 path (group 6); other 9 paths are 6 types (groups 0..5).
Group membership sizes [1,1,3,1,1,2,1].
No node was removed and no geometric lower bound was paid by this catalogue.
The published replay actually passed and matched.
v1 is a preserved incomplete build: node limit 1 failed at the first call.
v2 uses limit 2 while verifying that actual calls==1.

Latest full current audit:
work/audit_continued_leaf_stage_current_bundle.py
outputs/n26-continued-leaf-stage-current-bundle-audit-v1.json
It was started in WSL; handle 26247. Check its actual handle/output before
claiming completion, then rehash every files digest. Never restart if live.
Status and latest narrative were written BEFORE this audit started and have
not been edited since.

## Important next task: accept selected strict Rstar type trees

work/n26-selected-type-tree-proposals-v1.json is UNACCEPTED discovery.
Every noncandidate canonical group 0..5 was attempted, none silently skipped.
Full radius-conditional necessary trees:

- group 0: 125 nodes, 62 SPLIT, 5 DIRECT_FORCE, 58 CORRELATED_FORCE, 0 OPEN;
- group 1: 63 nodes, 31 SPLIT, 32 CORRELATED_FORCE, 0 OPEN;
- group 2: 307 nodes, 7 OPEN;
- group 3: 311 nodes, 11 OPEN;
- group 4: 313 nodes, 13 OPEN;
- group 5: 311 nodes, 11 OPEN.

Groups 0/1 are COMPLETE in discovery replay, but not independently published
as accepted type exclusions. Do not remove any current terminal yet.
work/n26-selected-type-tree-proposals-v2.json was started from the v1 seed,
500 extra checks per unresolved type, branch depth 36; handle 6554.
Check actual completion. Existing paid nodes are left intact; all unvisited
OPEN boxes are retained. n26_sharp_type_tree.py reconstructs root bounds at
scale 10^40, every closed split, and exact direct/correlated force payments.

Required acceptance:

1. Reconstruct selected catalogue from its bound stage and native evidence;
   verify canonical full-complex maps and every affected member path.
2. Bind Rstar upper endpoint to accepted same-root stress/cover sources.
   Recheck four cap sine margins; independently rebuild each type's sharp
   matrix from canonical face masks and graph paths.
3. Replay every tree semantically, including all closed boundaries and OPEN.
   Require force lower bound > certified Rstar upper endpoint at every
   nonempty paid leaf. A type is excluded only with no OPEN leaves.
4. Save all still-unclosed types and boxes, all exact ledgers, frozen
   standard-library standalone replayer, rejection controls and actual
   published replay.
5. These exclusions apply ONLY to radius <=Rstar, not physical U-domain
   emptiness. Do not label them ordinary unconditional EMPTY/FORCE closures.
   Keep the original U frontier and all old queues immutable.
6. A separate Rstar-competitor frontier may remove fully certified terminal
   members using explicit canonical isomorphisms, while keeping all siblings,
   unclosed types and the known feasible candidate. That needs its own
   accepted partition and current full-chain audit.

## Numerical diagnostics, NOT proofs

work/n26-selected-terminal-free-rod-discovery-v1.json:
joint free-angle/rod searches by groups 0..6 gave approximate radii
0.246436632, 0.250478623, 0.243443399, 0.239146312,
0.238297558, 0.236541287, 0.2347000904. No improvement was proposed.
They are local numerical solutions, NOT global minima or coverage certificates.
Internal witness coordinates are now retained for any future independent
continuous-cover certification if a genuinely better numerical cover appears.

Further Schur check at the candidate itself was numerically negative:
smallest angular energy Hessian eigenvalue about -0.0443723, even at zero
angle-box width. This is the FIXED positive reference energy relaxation,
not the existing unrestricted local covering barrier. It suggests mere
interval tightening cannot make this same energy globally convex.
It does not disprove the candidate local optimality.
No exact negative-curvature certificate was published; do not promote this
floating observation to a theorem. Any augmented energy/SOS route needs
new exact arithmetic and continuous hypotheses.

## Cautions

To continue current candidate angles, use n26_current_leaf_angle_source:
it replays the leaf-v2 source through correlated/sharp history and all 100
hulls, then verify_continued_leaf_angles replays the continued full tree.
Do not pass the continued tree into older source gates that do not know its
semantic lineage. Preserve all old non-OPEN nodes and closed halves.

The full mathematical goal remains unchanged: all four families, every
competing type, unrestricted reduction final acceptance, and same-root global
synthesis must close before n27. Partial selected catalogues and numerical
successes are not global completion.

WSL may silently exit before starting. Inspect process and target existence
before retrying; never restart a confirmed live process. Explicit Ubuntu2204
and either --exec python3 or -- python3 can be used. Historical full chains
must run in WSL because some old manifests read /mnt/c paths directly.
