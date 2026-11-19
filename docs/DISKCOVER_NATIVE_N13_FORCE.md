<!-- SPDX-License-Identifier: MIT -->
# n=13 native exact metric exclusions

This check starts from the native necessary-topology census at
\(U=0.346646\), with \(9,10,11\) boundary owners. It excludes **all** 610
\(B=9\) orbits, **all** 351 \(B=11\) orbits, and 717 of the 718 \(B=10\)
orbits by exact integer/rational checks at \(U\). The one exception is
the known candidate topology (canonical index 712); pruning it at \(U\)
would be incorrect, because an attaining realization exists below \(U\).

## Reproduce

Use `python tools/check_native_n13_global.py` for the complete exact replay, or run individual parts:

```sh
python tools/check_native_n13_census.py --out build/n13-census
python verification/n13/force_prototype.py --require-family --quiet \
  --census build/n13-census/n13-B9.json verification/n13/force-B9.json.gz
python verification/n13/force_prototype.py --require-family --quiet \
  --census build/n13-census/n13-B11.json verification/n13/force-B11.json.gz
python verification/n13/force_prototype.py --require-noncandidate --quiet \
  --census build/n13-census/n13-B10.json \
  verification/n13/force-B10-noncandidate.json.gz
python verification/n13/candidate_tree.py --census build/n13-census/n13-B10.json
```

Verification needs no SciPy; the optional generator uses it only as
an untrusted LP hint source. The proof streams were freshly generated for
the native canonical face lists. The verifier recomputes SHA-256 of the
census lists, matches every record to the corresponding indexed mask list,
and rejects duplicate, missing, or extra records in the stated scope.
The candidate's canonical masks were matched to the contact graph under
both dihedral root maps, including the distinct anchor label under
reflection (an anchor is attached to the boundary edge, not the vertex).

## Force certificate and angular boxes

A face contributes a fresh witness node linked to its three centers; an
anchor is linked to both incident boundary centers. The Voronoi reduction
makes every rod length less than \(U\). Pin anchor zero to \((1,0)\)
by rigid rotation, with the other turn angles in \([0,1]\).
The exact difference-constraint closure uses the two- and four-rod caps;
a six-rod path provides no restriction because \(6U>2\), the unit-circle
diameter. Any feasible angle tuple remains inside the tightened box.
A split makes two closed coordinate boxes whose union equals the parent.
Both are checked, and empty leaves require a genuinely contradictory
interval after tightening.

For each force leaf, orient a rational vector \(f_e\) along each graph
edge \(e\). It must have zero total divergence at every nonanchor node.
Write \(P_i\) for its divergence at anchor \(i\). Then
\[
 \sum_i P_i\cdot q_i
   =\sum_e f_e\cdot(z_{e,\mathrm{tail}}-z_{e,\mathrm{head}})
   \le U\sum_e\|f_e\|.
\]
For each \(i>0\) the exact trig enclosure supplies a rational support
\(a_i\cdot q_i\ge c_i\) valid over its entire angle interval.
Given a nonnegative rational multiplier \(\lambda_i\), use
\(d_i=\lambda_i a_i-P_i\). Since \(\sum_iP_i=0\) and \(q_0=(1,0)\),
\[
 \sum_iP_i\cdot q_i
 \ge\sum_{i>0}\left(\lambda_i(c_i-a_{ix})+d_{ix}-\|d_i\|\right).
\]
A strict separation between this lower bound and the rod upper bound
excludes the whole box. Both square-root norm roundings are outward and
obtained by integer square roots, and every support direction and arc
threshold is enclosed rationally. Thus the LP's convergence, objective
value, or numerical dual error is never an acceptance premise.

## Exact-target seam for candidate analysis

To exclude arbitrary covers at a radius below \(r_*\), normalize and
perturb using an intermediate \(\rho\) with \(r<\rho<r_*\). This leaves
all rods strictly below \(r_*\); it does not merely bound them by \(U\).
The \(U\)-based owner exclusions and topology screens still apply by
monotonicity. A candidate-specific force leaf is allowed to test the
separately certified rational bound \(0.346645456927389645>r_*\). A
candidate **isolation** leaf instead needs the exact-target inequality
(bound all rods by \(r_*\)), and must first verify the anchor distance
in the **original candidate gauge** at the pinned original anchor zero.
The canonical census fixes a different anchor; to compare them the
checker uses exact intervals for the relative turns
\(u_j-u_k\), where \(k\) is the canonical image of original anchor zero,
then negates on reflection. The resulting nine squared distances must
sum to at most \(1/64\), and the independent exact isolation proof must
pass. This construction prevents confusing a small canonical-gauge
distance with a justified neighborhood in the original gauge.

## Complete hybrid candidate replay and provenance

The completed candidate replay uses the original \(q_0\) gauge directly,
relabeling the graph rather than assuming that a canonical-gauge norm bound
transfers unchanged. The labeled original contact graph is independently
matched to canonical index 712, including every face and boundary edge;
a cyclic relabeling and a rigid rotation of any putative cover are harmless.
The candidate tree only needs the looser adjacent gap cap \(1127/10000\).
The replay checks that this cap is outward for its rational test radius.

The candidate tree's split positions and force hints come from the
[pinned upstream compressed data](https://github.com/VonEquinox/DiskCoveringSolve/blob/089584973f41e6374ce110f6e5b5ee456df19352/cover13/proof_bundle/core/candidate_global_certificate.json.gz),
SHA-256 `54dee4b47b3c307064c30cf2f93f5e9cc7a755b3f5fb7aeeb6ae859f7996e51a`.
No upstream Python checker, old verdict, or checked-output report is an input.
Our converter rounds the force hints to the native fixed-point scale, repairs
nonanchor divergences, and freshly checks every inequality, split, and anchor
leaf before writing the compact archive. The standalone replay of that archive
rechecks all content: 915 splits and 916 terminal leaves, of which 837 are
exact force exclusions and 79 fall in the independently proved isolation
neighborhood. A visit bitmap rejects repeated, orphan, or out-of-range
nodes and both children are required at each split. The 79 anchor leaves
verify the sum of all nine squared endpoint distance bounds is at most
\(1/64\) in the original gauge. The root of the exact algebraic system is
checked separately; no optimization result is trusted.

Together with the written twelve-owner exclusion, the normalized topology
classification, all 1,678 noncandidate force trees and the independent
attaining construction, this rules out *every* cover of a strictly smaller
radius. It establishes \(r_D(13)=\sqrt{t_*}\) in the stated rational isolating
interval. This is a computer-assisted proof with written geometric steps,
not a Lean formalization.
