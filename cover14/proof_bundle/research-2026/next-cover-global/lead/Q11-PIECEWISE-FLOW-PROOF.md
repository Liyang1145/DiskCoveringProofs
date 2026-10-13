# Piecewise balanced-flow exclusion on the q11 deficit polytopes

## Scope and interface
Unit disk, U=.33173203427623414, L=2asin(U), B=2asin(2U). The necessary boundary-owner representation is C1171/C1172. For a retained q11 graph use production anchors A_j incident to sites j,j+1; deficits d_j=L−(angle(A_(j+1))−angle(A_j)) are nonnegative, at most L, and sum to11L−2pi. Set angle(A_0)=0 by rotation. A second-neighbor chord with middle owner i adds d_(i−2)+d_(i−1)+d_i >=3L−B. This necessary polytope is closed and contains all limiting degeneracies. No symmetry assumption on sites or gaps.

## Exact subdivision
Every coordinate is a Q-linear combination of L,B,2pi. Cuts have rational normal and a Q³ right side. Each internal node has exactly two closed children P∩{n·d>=c}, P∩{n·d<=c}. They cover P including the interface. There is no volume/sampling coverage argument.

The child vertices are precisely retained parent vertices and intersections of straddling parent edges with the cut. With ambient dimension11 and the sum equality included, distinct vertices share an edge iff the rank of their common active normals plus the equality is10. The crossing is solved from these10 independent rows plus the cut, not by an unjustified rational interpolation parameter. A true crossing may not be silently discarded. Every sign of a Q³ expression is either identically zero or strictly resolved with directed bounds for the constants; unresolved signs fail the audit.

Production member code was repaired before acceptance for an equality-rank double count. Its tests independently derive the D11 edge set (110 vertices,550 edges). Lead q11_split_basis_audit.py uses complete active-basis enumeration as a different representation: at most one d_j=L because sumd<2L; k active nonbox cuts leave k+1 free coordinates. It matches all child vertex sets on510,75,311,434. The scalable lead q11_split_inductive_audit.py separately reconstructs crossing edges and solutions from serialized inequalities; it does not import the producer module. Its reconstruction agrees with those complete basis sets. Completeness for the root follows the earlier independent q11 vertex audit; completeness thereafter is inductive clipping, not agreement alone.

## Leaf inequality
For every feasible site–witness/anchor incidence system, choose an exactly force-balanced rational vector flow z. Then r sum||z_e|| >= L_z(A)=Σg_j·A_j. The leaf proof reconstructs incidence from the source catalogue, checks every balance equation exactly, and bounds all flow norms upwards. Anchor angles are affine in d.

For each anchor coordinate let f_j(t)=g_j·(cos t,sin t). If f_j is nonnegative at both endpoints of an interval of length<pi, it is nonnegative throughout (the nonnegative half-circle is a closed interval on this branch); hence f_j is concave there. Otherwise choose eta_j=||g_j||, so f_j(t)−eta_j(t−t0_j)^2/2 is concave since its second derivative is −f_j−eta_j<=0. Summing gives a concave function on the whole leaf polytope, everywhere <=L_z. Its minimum is at a vertex. Directed vertex evaluations divided by an upper bound for sum||z_e|| yield a lower bound on r. Accepted leaves require this lower bound strictly above U.

The Fraction replay independently computes pi/asin/sin/cos/norm bounds, reconstructs the graph incidence and checks exact balance. A second arithmetic implementation is not an independent proof of the geometric cover interface; that interface is stated above. Optimizer exit status and numerical residuals are irrelevant after rational repair and certificate verification.

## Global tree and source binding
q11_partition_coverage_audit.py binds graph index and every leaf face set to q11-pocket-catalogue.json; validates the root box/equality/chord rows; verifies the independent complete vertex sets; checks each child appends precisely one opposite cut and retains the same equality; traverses the full tree with no repeated/unreachable nodes or unfinished leaves; then replays each leaf bound. Its outputs are only per-graph exclusions. A catalogue union must separately check exactly which retained graph indices have these outputs. A partial batch never implies exclusion of all q11 graphs.

## Reproduction
For an existing complete saved tree of index INDEX:
```
py -3 -B research-2026/next-cover-global/lead/q11_split_inductive_audit.py INDEX
py -3 -B research-2026/next-cover-global/lead/q11_partition_coverage_audit.py INDEX
```
The producer is q11_polytope_partition_probe.py, bounded to31 additional nodes per invocation. Production trees are not themselves accepted evidence until the above audits finish. Batch state: q11-partition-catalogue-batch.json. Original target remains the unrestricted exact n14 optimum; q10/879 is not settled by these exclusions.
