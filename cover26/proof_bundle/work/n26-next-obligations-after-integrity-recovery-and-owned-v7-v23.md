# Continuation after complete integrity recovery and owned-v7 final rehash

Observed 2026-10-11 09:08:24 Asia/Shanghai. Goal ACTIVE.
This note supersedes v22's live/current sections and the prior corruption summary.
No subagents authorized. Preserve frozen/bound originals, all failed bundles and
all corrupt-byte snapshots. Do not restart confirmed live tasks or WSL/services.
Python C:/热爱单机但萌新/dependencies/python/python.exe.

## Current COMPLETE source

outputs/n26-current-candidate-owned-current-audit-v7.json
SHA 6a46131202a5d2dd732b88622b1cec0e072c7b6ef888f37e70f420b291590203.
outputs/n26-current-candidate-owned-final-digest-recheck-v7.json
SHA f5c41e3522383be811373e615a95f12e7f73af874378ac5f0745fa59ecd7f496.
All 166960 digests freshly passed AFTER exact byte restoration.
Formal candidate roots now 25; candidate source owned-forest-v7, actual replay
owned-forest-published-replay-v7. Their acceptance SHA is
7189f3ea021ddf973d4d13027650baa547d82b1c38d7f18f8e721db659de6257.
Root1794 lower-bounded, NOT emptied;39 new leaves, all29 old paid nodes retained.
Source pending angles SHA bb6feb6f826f69d450c7320dd27c26c97bb4f6c4b1a097448701c91e17398914.
Formal conditional frontier stage17 remains7747;families306/1068/2872/3501.
Actual frontier outputs/n26-conditional-force-stage-v17/FRONTIER.json.
Historical87 full types/215 proof receipts retained.
Latest user checkpoint outputs/n26-current-checkpoint-after-owned-v7-20261011-v23.md.

## Integrity diagnosis and recovery COMPLETE

Full non-short-circuit scan outputs/n26-current-owned-v7-integrity-diagnosis-20261011-v1.json
SHA397f9718f1b6a4fb7632c31589e6be4f247d670cdeff31ffd530e29d3d6c355b.
All166960 scanned,166958 matched,2 extra damaged receipts identified:
-outputs/n26-force-stage-v12/native-02313.json:
 original f0b53cfc81474275bb1cda21c32662bb3b171a425353ef9a484fe6aa807190df,
 corrupt6845ead39a1792197801252c468e2906c3adf37f5e8bd4a3cc2632b9c1aa982f.
-outputs/n26-conditional-force-stage-v1/native-00042-launch.json:
 original548c295f202740e73a6551587c42e7ac7654d6159d5a3b9714ee068d619a06d1,
 corrupt1347c2c24e20b6410183184c1fe549e6da4e85d7a371e7e4b72851915952c1b6.
Both snapshots preserved in work/n26-integrity-snapshots-20261011-v1.
Both events regenerated to fresh work/n26-native-integrity-regeneration-20261011-v2.
For EACH event both RESULT AND historical LAUNCH bytes match original SHA exactly.
Actual new-path command/receipts explicitly distinguished from historical launch
recovery candidates; no historical execution provenance fabricated.
Recovery report outputs/n26-historical-native-byte-recovery-candidates-20261011-v3.json
SHA278ab4dcf8e202d60acd3165db13fb056f63fa678bba87f8d2b70f5f3b26c6db.
Targets were checked against saved corrupt bytes, snapshots/candidates rehashed,
exact bytes restored using guarded PowerShell Copy-Item, original hashes verified.
Operation report outputs/n26-historical-native-byte-restoration-20261011-v2.json.
Cause UNKNOWN. Earlier2312 RESULT/LAUNCH exact restorations and snapshots retained.
Failed fresh regeneration work/n26-native-integrity-regeneration-20261011-v1
retained:2313 succeeded but the next native invocation failed;v2 actual receipts
fully passed. No corrupted proof/input was relabeled as accepted.
Recovery earned ZERO new geometric payments. Complete independent final rehash
session31409 subsequently passed all166960 plus accounting, exit0.

New work/scan_current_inventory_integrity.py and
work/regenerate_diagnosed_native_receipts.py are diagnostic/recovery scripts,
not substitutes for independent mathematical or final-current gates.

## TWO confirmed live handles

1.Session56971, Windows Python PID4432, started09:04:50:
frozen outputs/n26-conditional-force-stage-v18-sparse-v1/verify_conditional_force_stage_sparse.py
--input outputs/n26-conditional-force-stage-v18-sparse-v1
--area-bundle outputs/n26-multislope-area-lower-v1
--report outputs/n26-conditional-force-stage-v18-sparse-v1/VERIFIED.json.
Exact sparse standalone retry AFTER historical recovery. No VERIFIED at launch.
Do not edit the frozen checker or restart while live.

2.Session85594, started09:08:
work/propose_owned_candidate_forests.py
--source outputs/n26-current-candidate-owned-forest-v7
--source-replay outputs/n26-current-candidate-owned-forest-published-replay-v7.json
--current-audit outputs/n26-current-candidate-owned-current-audit-v7.json
--current-digest-recheck outputs/n26-current-candidate-owned-final-digest-recheck-v7.json
--only-indices41 45 48 959 --checks-per-root127 --maximum-depth18 --try-local
--output work/n26-current-candidate-owned-forest-discovery-v8.json.
Producer must fully replay original source/history. No status-marker shortcuts.
Existing41/45/48 forests continued;1794 cannot reopen. Discovery is UNACCEPTED.

Completed this turn:79366(all-digest diagnosis exit1, expected2 corrupt results),
27907(fresh regeneration-v1 exit1),86615(fresh regeneration-v2 exit0),
31409(independent final current-v7 rehash exit0), identity-regression-v5 exit0.
No full-current join/final rehash is currently live.

## Next sparse stage chain

Preserve failed original outputs/n26-conditional-force-stage-v18.
Fresh sparse-v1 all4800 native events already passed; original exact semantic
checker848... SHA unchanged; sparse executor has its own SHA/provenance.
Fixture stage17event268/B14/3nodes/1SPLIT/2FORCE is a ZERO-payment regression.
Proposal work/n26-conditional-stage-proposals-v18.json
SHAc9bcfeab7145e5ec7b1efc0ce46fbebdbd7a24233a63ffdebd92363f12355fa5.
Proposed SPLIT3710 AREA180 EMPTY908 TERMINAL2 FORCE0 TREE0.
Proposed frontier8082, families306/1053/3184/3539.
Children5133,7747+5133-3710-180-908=8082.
Do not formally use these counts until complete chain/final rehash.

When56971 succeeds:
1.Run the ACTUAL frozen sparse checker again to fresh
 outputs/n26-conditional-force-stage-published-replay-v18-sparse-v1.json.
2.Build fresh native terminal catalogue IN LINUX via
 wsl.exe -- /usr/bin/python3 <linux work/build_terminal_catalog.py>
 --source-stage <linux sparse stage18>
 --candidate-control <linux outputs/n26-candidate-transport-control-v1>
 --output <linux outputs/n26-conditional-terminal-catalog-v18-sparse-native-v1>.
 /usr/bin/python3 version3.10.12 confirmed, no WSL restart needed.
3.Actual frozen catalogue replay to fresh
 outputs/n26-conditional-terminal-catalog-published-replay-v18-sparse-v1.json.
4.Fresh stage18 narrative with ACTUAL accepted counts/controls/catalogue, clearly
 full-current chain/final rehash still required.
5.Full work/audit_stage_catalogue_with_closed_pool.py join using NEW COMPLETE
 owned-current-v7 parent, both actual replays, fresh narrative/output. Always:
 --dependency-note outputs/n26-n8-theorem-import-source-review-20261010.md
 --family-scope outputs/n26-new-scope-v1.
 This unchanged current checker compares/replays the original exact SEMANTIC
 checker, not the old defective CLI main; sparse executor is bound separately.
6.Independent work/recheck_current_stage_catalogue_inventory.py final rehash.
Serialize all full-current joins and independent final rehashes.
Stage19 discovery can begin from ACTUALLY accepted stage18 while join pending,
but its counts remain unaccepted. Current candidate count25 must be retained.

## Owned-v8 continuation after85594

Use unchanged verify_owned_candidate_forests.py build/verify, PARTITION and
HISTORY regression receipts and original proof-time COMPLETE owned-current-v7
parent/rehash. Accepted code/checkers are immutable.
Build fresh outputs/n26-current-candidate-owned-forest-v8, standalone plus actual
published replay. Join onto the NEWEST complete enumeration parent available,
not onto an obsolete global chain. Test layer identity from that actual newest
parent before join; v5 identifies actual owned-v7 directly and passes10 controls.
If stage18 join is complete first, layer gate must follow its bound enumeration
ancestry to owned-v7, preserving every per-root history and whole-root row.
Later independent final candidate-forest rehash required before rootcount changes.

## Invariants and outstanding global obligations

Strict Rstar interval unchanged:
0.234700090400448239616790133776692127560495963654971391785924
<Rstar<
0.234700090400448239616790133776692127560495963654971391785925.
Scope at-most-same-root-Rstar-not-original-U;originalUfrontier3922.
Original92rods/62vertices/16anchors/46freevertices/52coordinates;LOCAL7/800000.
ExternalN8 imported,NOT reproved. CPPa76a8ce6... binaryb07a612b...
CAPS754112/1555305/2486507/3880649,D10^7.
Fixed original-arithmetic-resource-v1 standalone/actual SHA935d336... remain
validated earlier but are NOT current-source/history replacements or shortcuts.
No fast latest-current resource interface exists. No semantic gates skipped.
Global catalogue/lower-bound/optimality/unrestricted-joint remain FALSE.
n27 NOT started. This is substantive progress, not an external-blocked turn.

## Last live observation

2026-10-11 09:31:08 Asia/Shanghai:
The sparse stage18 standalone and actual replay both completed successfully.
The fresh native terminal catalogue and its actual replay also completed
successfully; acceptance/replay hashes differ only because they are distinct
published files, while their parsed JSON contents are equal.

Session93202/PID696 completed the serialized stage18 full-current join and its
independent final rehash. The new current audit SHA is
8cec3ea3e55a3532e3b3cbc6f572f377164c8af648bd1748039ed655610d7d06; the final
rehash checked176625 files and has SHA
843df3a585db90a5f72b593d0af632e82f8d04a33684e6d3e791663949cfd6fd. Formal
conditional frontier is now8082, with candidate roots25 unchanged. Do not
start another stage18 join or final rehash.

Session85594/PID10424 remains live in owned-v8 source/history reconstruction.
Stage19 exploratory proposal completed with verified=false, SHA
3e282a7a499affcd3fd4d908399a6b18abc39b79abbd81c2e099dc940610ccc1; its
4800 events and proposed exclusions remain unaccepted and must not alter formal
counts. Current formal source is now stage18/8082 pending and owned-v7/25 roots
until an owned-v8 acceptance and a new current join/final rehash are completed.

Stage19 was frozen at outputs/n26-conditional-force-stage-v19, but its original
native auditor failed because relative Windows output paths were passed directly
to WSL; the failed bundle is preserved. A second absolute-path run reached a
real output-exists collision after partial progress and is also preserved in
outputs/n26-conditional-force-stage-v19-native-v2. Failure snapshot:
work/n26-stage19-native-failure-20261011-v1.

The unchanged historical auditor remains untouched. A separate
work/audit_force_forest_native_retry.py now uses absolute Linux output paths and
retries only transient nonzero runs that produced no output. Fresh v3 native
bundle outputs/n26-conditional-force-stage-v19-native-v3 is live as
session74253/PID10856; it has independently matched at least700 events as of
09:41:09. This is exploratory and earns no accepted geometry until its native
report, exact verifier, actual replay, terminal catalogue and complete current
join all pass.

Superseding observation 2026-10-11 12:23:53 Asia/Shanghai:
Stage19 has now passed its complete chain. Current audit:
outputs/n26-nineteenth-conditional-current-audit-v19-native-v4-with-scope.json
SHA9d0f7f7dc318a5db1155c8db2e0cba7ccd5e7a8a43ecc2fcb3b97fe41e7992e7.
Independent final rehash checked186283 files and has SHA
4395769907a87fb4e7ade1250bb64aef2195768ea141362b4e3b735920f1c2ef.
Formal conditional frontier is now8193.

Owned-v8 discovery
work/n26-current-candidate-owned-forest-discovery-v8.json
SHA2dfaad3bde510872e9874d12d409797e9c77ebb2b15a9c66a5160fc67d24eee7
passed standalone acceptance at
outputs/n26-current-candidate-owned-forest-v8/VERIFIED.json:
roots41/45/48/959,870 SPLIT,19 ENERGY,4 exact leaves,855 OPEN, zero
whole-root payments,25 pending roots/boxes. Stage19-parent identity regression
v6 passed. Session41457/PID5152 is replaying the accepted v8 bundle to
outputs/n26-current-candidate-owned-forest-published-replay-v8.json; it remains
live and must not be restarted. Only after this actual replay can the new
owned-current join and independent final rehash run.
