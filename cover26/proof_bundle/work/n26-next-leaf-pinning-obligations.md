# Next continuation after leaf pinning and global stage v10

2026-10-10. Goal active. n26 global optimality NOT proved; n27 NOT started.
The previous goal turn made genuine progress: 100 new exact LOCAL payments,
151 new strict whole-subtree exclusions, and an explicitly exposed full candidate.

## Accepted new state

Current angle bundle: outputs/n26-leaf-pinned-candidate-angles-v2.
1,153 nodes: 576 SPLIT, 215 FORCE, 76 SHARP_FORCE,
93 SHARP_CORRELATED_FORCE, 13 LOCAL, 100 SHARP_HULL_LOCAL,
3 SHARP_EMPTY, 77 OPEN. All 100 new leaf hulls were reconstructed from actual
sharp endpoints and certified tiny root cells, then exact refined energy
pinning was rerun using the unchanged network and 7/800000 allowance.
Maximum center error <6.552e-6; minimum local entry margin >2.198e-6.
The v2 published standalone replay actually passed and matched exactly.
v1 is preserved as a historical intermediate with a missing publication
path-helper import; v2 removed that unnecessary dependency.

Current global bundle: outputs/n26-force-stage-v10.
From 2,868 source subtrees, 2,400 events: 1,917 splits, 60 force,
13 force_tree, 78 area, 322 empty, 10 unresolved terminal events.
New strict exclusions 151; pending B14/B15/B16/B17=289/751/1185/1106,
total 3,331. All 10 unresolved terminals are included in B16 pending.
The native audit and exact acceptance passed; the published replay passed and
matched the report exactly.

Candidate owner is no longer the two-face [24,40] prefix. It is uniquely the
complete 34-step prefix in outputs/n26-candidate-transport-control-v1/
CANDIDATE-PATH.json. Its current face list exactly matches that control.
Every sibling on the path was retained. Other unresolved complete graphs are
retained too; do not call the 10 paths 10 distinct canonical types.

Current full audit: work/audit_leaf_pinned_stage_current_bundle.py.
Target: outputs/n26-leaf-pinned-stage-current-bundle-audit-v1.json.
It actually passed, then every one of 10,353 bound files was rehashed with
zero changes. The exact decimal comparisons maximum error <6.552e-6 and
minimum margin >2.198e-6 also passed with Fraction arithmetic.
No output status document was edited after this final check.
It launched the entire historical chain via a fresh v9 parent, then replayed
all 100 leaf hulls and v10 native/force/area/terminal obligations.

## New exploratory diagnostics (NOT lower-bound acceptance)

work/n26-free-angle-rod-discovery-v1.json: six widest retained angle boxes.
Joint angle/free-rod SLSQP converged numerically near R*=0.234700090400448...;
no proposed improvement by more than 1e-8 and no new exact correlated-force
payment. Their angle vectors are within about 5.33e-8 turns of the original
root. This is not a global minimum proof, and it does not certify coverage
of the floating centers. It suggests near-root, second-order difficulty,
not a different labelled root orbit on these six tested boxes.

work/n26-anchor-schur-convexity-discovery-v1.json: eliminate 46 free points of
the positive 92-rod network, leaving a 16-anchor quadratic Dirichlet energy.
For E(q)=2 sum c_ij(1-cos(2*pi*(theta_j-theta_i))),
the angular Hessian is 8*pi^2 sum c_ij*cos(delta_ij)*(e_i-e_j)(e_i-e_j)^T.
Replacing each cosine by its independent full allowed-interval minimum
gives a valid-form minorant, but the NUMERICAL pilot is NOT positive definite:
global smallest eigenvalue approx -0.08629; all 77 root-containing box hulls
have negative minorants (best approx -0.04437). No exact convexity certificate
was accepted; do not claim this simple minorant pays any leaf.

A stronger quadratic/energy or correlated Hessian bound may still help.
Any future Schur proof requires exact nonnegative Kron elimination, exact
trigonometric bounds, positive-definite acceptance (not floating eigenvalues),
full reference energy/gradient/error charges, and strict entry into the
existing local box. A global PD premise cannot simply be assumed.

## Continuation cautions

To load current angles semantically:

1. verify_leaf_pinned_candidate_angles.source_gate gates correlated-v1 by
   replaying its historical sharp-v2 basis and unchanged pinning reference.
2. build_nodes uses the sealed discovery indices and requires each to be a
   distinct retained correlated source OPEN.
3. replay masks SHARP_HULL_LOCAL as OPEN for the old whole-tree semantic
   replayer, then independently reconstructs and pays all its hulls.
4. Compare full CERTIFICATE, PENDING-ANGLES and LOWER-LEDGER to the accepted
   v2 bundle before extending it. Do not feed HULL_LOCAL directly into an
   older standard/sharp/correlated-only source loader.

Old non-OPEN nodes, all closed children/shared boundaries and every unresolved
leaf must remain. SHARP_* scope is radius <=R*, not original U emptiness.
Do not loosen rotation allowance or restrict competitors to D2.

The v10 global source includes pre-existing unresolved terminals. Discovery
and acceptance currently reprocess complete source states as retained terminal
events; if changing that behaviour, explicitly carry every inherited terminal
classification and update exact counts instead of dropping unvisited terminals.
Candidate full angle closure will eventually pay a same-root lower-bound TYPE,
not declare the known feasible candidate physically empty at U. Adapt the
positive-control owner audit accordingly only when that complete type is
actually accepted.

Full historical chain must run in WSL Ubuntu2204 because some old manifests
read /mnt/c paths directly. Check process and target existence if WSL exits 1
silently; never restart a confirmed live process. The new leaf v2 provenance
uses canonical absolute /mnt/c identifiers and needs no working discovery file.
