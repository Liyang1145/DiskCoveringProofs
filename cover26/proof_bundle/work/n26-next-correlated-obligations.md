# Next continuation after correlated angles and global stage v9

2026-10-10. Goal active. n26 global optimality NOT proved; n27 NOT started.

Accepted immutable bundles:

- outputs/n26-correlated-candidate-angles-v1: 1,153 nodes, 576 SPLIT,
  215 FORCE, 76 SHARP_FORCE, 93 SHARP_CORRELATED_FORCE, 13 LOCAL,
  3 SHARP_EMPTY, 177 OPEN. New payments: 45 direct + 93 correlated.
  All 93 correlated leaves need their nonnegative difference dual; their
  same-flow direct-arc bound does not exceed the certified radius endpoint.
- outputs/n26-force-stage-v9: from 2,654 source subtrees, 2,400 events;
  1,870 splits, 23 force, 6 force_tree, 101 area, 400 empty, 0 terminal.
  New strict exclusions 130; pending B14/B15/B16/B17=289/661/844/1074,
  total 2,868. Known full candidate still uniquely owned by [24,40].
- Both standalone published replays actually passed and matched their
  original VERIFIED.json reports exactly.

Current full audit is audit_correlated_stage_current_bundle.py, target
outputs/n26-correlated-stage-current-bundle-audit-v1.json. It actually passed,
then all 5,469 bound files were rehashed with zero changes. No current output
status document was edited after this final rehash.
Original v8 full chain actually passed with 483 unchanged bound files, but is
historical after status changed for v9.

The v9 full chain reused the just-observed fresh v8 parent replay, bound by
SHA-256 eb05baa0b17da0c6fc307afe6d36922c44b3081e1819a563e1058ceaa2900970.
That parent really replayed the entire chain under the current v9 status bytes;
the first outer attempt then failed on Windows backslash provenance paths.
The corrected outer replay normalizes those path identifiers without altering
any accepted bytes, rechecks the complete parent inventory, replays the new
correlated tree and global v9 stage, and performs an end-of-run double check.
All proof reports and original standalone reports remain unchanged.

## Promising next task: leaf-specific pinning (NOT accepted yet)

work/n26-leaf-specific-pinning-discovery-v1.json is exploration only.
probe_leaf_specific_anchor_pinning.py independently replays the current source
and tries a root-containing hull for every narrow sharp OPEN box.
It found 100 out of 100 attempted source leaves enter the already certified
original-coordinate local allowance 7/800000 using unchanged exact refined
energy arithmetic. This has not changed any accepted tree node or pending
count; 177 OPEN remains authoritative.

For each leaf, the proposed hull is the coordinatewise union of its reconstructed
sharp box and the tiny certified exact-root angle cells from sharp cap v2.
Thus base.check_cells still certifies strict root inclusion. Unlike merely
testing containment in the one fixed rectangular pinning domain, each hull gets
its own exact anchor extrema, individual anchor errors, A, K, path errors and
center-to-root bound. The same positive rational network and root are used.

Required acceptance:

1. Gate/replay current correlated source semantically, not through the old
   standard-only or sharp-only replayers.
2. Reconstruct every incoming original U box and sharp box before any leaf
   payment; keep all old non-OPEN nodes and both closed halves intact.
3. Rebuild the proposed root hull from actual leaf endpoints and certified tiny
   root cells; never trust discovery hulls or reported error margins.
4. Bind the unchanged positive network/reference to refined pinning v2,
   same-root stress, centered local v2 and transported full candidate.
5. Re-run refined.derive on the entire hull and require strict original-coordinate
   entry <7/800000. No initial-neighbourhood assumption and no D2 competitors.
6. Add a distinct radius-conditional local leaf (or independently replayed leaf
   certificates plus a complete tree continuation), all new rejection controls,
   a frozen standalone replayer and an updated current full-chain audit.
7. Only after actual acceptance may 100 be removed from the angular OPEN ledger.

Do not silently loosen rotation allowance to delta/3. The old delta/8 allowance
and its 7/800000 original-coordinate radius remain certified.

## Source loading / execution cautions

verify_correlated_candidate_angles.source_gate currently gates its historical
sharp-v2 source, then replay_and_close establishes the correlated tree from its
sealed PROPOSAL. Do not pass the new correlated tree straight into that historical
source gate. A continuation loader must first replay the sharp-v2 basis, then
the full correlated-v1 proposal/certificate/pending/ledger with new leaf semantics.
Keep the sharp cap interface's historical standard-only certification source
unchanged, while continuing to use the same exact graph and root.

The full historical chain must run in WSL: some old manifests contain /mnt/c
paths read directly without Windows conversion. Use Ubuntu2204 explicitly.
WSL may exit 1 before starting with no text; check process and target-file
existence before retrying. Never restart a confirmed live process.

## Later improvements (unimplemented, unproved)

An endpoint-secant affine lower bound could replace the midpoint Taylor support.
If f=g.q is nonnegative over an arc, f''=-4*pi^2*f<=0, so its endpoint chord is
an affine minorant. Exact lower endpoint values give a rational secant slope
to combine with the same difference dual. If f can be negative, the proved
lower bound L for f gives f''<=4*pi_upper^2*max(0,-L); pay the full
M*(theta-lo)*(hi-theta)/2 sag, or its M*h^2/2 box bound. This needs a separate
verifier, controls and bundle before using it as proof.

The known broad candidate owner has only 2 faces, 33 immediate children and
next=17. A future targeted expansion along the exact 34-face candidate path
can expose its full transport while retaining every sibling; it is not a
subtree exclusion. A later audit must find its owner using the full transported
candidate prefix, rather than assume the current [24,40] owner stays fixed.
