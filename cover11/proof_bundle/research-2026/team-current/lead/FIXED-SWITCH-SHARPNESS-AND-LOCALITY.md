# Exact sharpness and local transfer for the fixed-switch oracle

## Scope and dependencies
Unit disk, graph and V(U) of FIXED-SWITCH-SOC-REDUCTION.md. R* is the exact C891 root coordinate, C* the C892 center configuration. This note proves sharpness at U* and a qualitative angular neighborhood lower bound, NOT a global bound on P. Inputs: exact physical stationarity C897, strict local optimality C902, strict triangulation C892, and the audited interval acuteness/slopes kernel below.

The root construction has ring indices k=0..8, hubs9,10, central faces (2,9,10),(6,9,10), and fan hub9 on edges2..5. To put it in canonical graph coordinates relabel new ring i = old ring (i+2) mod9; hub a=old9 and b=old10. This takes the central faces to (0,a,b),(4,a,b). All switches relabel by the same cyclic shift. No geometry changes and no assumed symmetry of competitors.

## 1. Checked signs at the exact root
The source fresh_acute_slopes_interval.py reconstructs the same root box as C891/C892 with mpmath.iv at 50 digits. All 11 face triangles have every vertex-angle dot product >7/100. For all nine boundary ties, sc=((U-c)/R)·JU and sd=((U-d)/R)·JU have opposite signs and |sc|,|sd|>51/100. Endpoint sign tests are two-sided; rounded nstr outputs are diagnostic, not certified endpoints. Lead replay: acute_slopes_audit.txt.
Acuteness implies the circumcenter barycentrics beta_s are all positive. The site coordinates are strictly inside the unit disk by C892's construction.

## 2. Exact vector-force certificate
Let mu_i>0 be the nine tie weights and nu_f>0 the nine active-face weights from C897; their sum is EXACTLY1.
For a face with circumcenter z=sum beta_s c_s, differentiation of |z-c_s|=R and barycentric cancellation gives
 dR=sum_s beta_s (c_s-z)·dc_s/R.
Put force magnitudes alpha_fs=nu_f beta_s>0 along the three site-to-z unit vectors. The auxiliary balance follows from z=sum beta_s c_s.
At a tie, differentiating the two equal distances and eliminating the tangent velocity gives the split eta=sd/(sd-sc), 1-eta=-sc/(sd-sc), both positive. Assign magnitudes mu_i eta and mu_i(1-eta) to its two site-to-anchor edges. The free-site balances are exactly C897. The slack triangles carry zero force. The sum of force magnitudes is1, and all45 carrying edges have length R*.
Therefore the dual work is R*, and the feasible candidate has t=R*: V(U*)=R* exactly.
At anchor i the load l_i has zero tangent component by construction. Its radial component is strictly positive because each incident force has radial component alpha(1-c·U)/R*>0. This assertion concerns this particular physical lift, not every optimal dual.

## 3. Uniqueness of all site coordinates at fixed U*
Take any oracle-feasible X' at t<=R*. The sharp dual gives
 R*=sum_e p_e·(X'_v-X'_w)<=sum_e |p_e||X'_v-X'_w|<=R*sum_e|p_e|=R*.
Every summand gap is nonnegative. Hence on each positive edge both inequalities are equalities: its displacement has length R* and is parallel with the same orientation to p_e. Its vector therefore equals the candidate displacement exactly.
All nine ring sites are attached to anchors by positive endpoint edges. Both hubs are attached through either positive central-face auxiliary to a pinned ring site. Thus all11 site coordinates are uniquely pinned. The nine active auxiliaries are pinned too. The two slack auxiliaries need not be unique; this is immaterial.
This proves global fixed-anchor uniqueness of SITES without claiming uniqueness of every auxiliary or of the dual.

## 4. Compactness controls near-anchor low-radius solutions
For U near U*, any feasible solution with t<=R* has all free coordinates bounded by graph paths to anchors using the FULL51-edge graph (zero dual weights do not delete primal distance constraints). Thus these solutions lie in one bounded set. If U_n→U*, t_n<=R*, any convergent subsequence has a feasible limit at U*. Section2 forces t_limit=R*, and Section3 forces its sites=C*. A contradiction/subsequence argument shows: for every site neighborhood O of C*, there exists an anchor neighborhood N of U* such that ALL oracle-feasible solutions at U∈N and t<=R* have sites in O. This is stronger than continuity of a chosen solver output.

## 5. Local primal feasibility implies a true cover
Choose O small enough that the C892 strict empty-circle triangulation remains complete, every one of its11 triangles remains acute, its circumcenters remain inside D, and C902 local optimality applies. These are open conditions: C892 gives strict orientation/empty-circle/hull/interior margins and Section1 gives strict acuteness.
Choose N within the same cyclic angular chart with all nine owned anchor intervals shorter than pi. If both endpoints of one such interval belong to a radius-t disk with t<1, its whole short circular arc is covered: that disk meets the unit circle in a single arc shorter than pi, and this arc must contain the unique short path between the endpoints. Thus all boundary arcs are covered by the ring disks from the18 endpoint constraints. The anchors need not be the NEW Voronoi switches; this argument uses only their cyclic ordering and endpoints.
For each acute triangle, its minimum enclosing radius is its circumradius. The three constraints involving the free z_f imply that minimum enclosing radius<=t, so the actual circumradius<=t. Completeness of the stable Delaunay triangulation then covers every internal Voronoi critical point. Boundary coverage plus those critical-point bounds implies coverage of the entire unit disk: squared distance to the nearest site on a clipped Voronoi cell has its maximum at a cell vertex or on the unit-circle boundary. Equivalently an uncovered internal global maximum cannot lie in a cell interior or in the interior of an edge, since the distance restricted to a line is strictly convex there.
Consequently any nearby oracle-feasible solution with t<=R* gives a genuine11-disk cover of radius<=t.

## 6. Qualitative local angular theorem
Suppose no anchor neighborhood satisfies V(U)>=R*. Then choose U_n→U* with attained oracle optima t_n=V(U_n)<R*. Section4 places their sites in O for large n; Section5 turns them into genuine covers; C902 forbids a smaller radius in O. Contradiction.
Hence V(U)>=R* in SOME neighborhood of U* (and of its rotational/relabeling orbit).
No quantitative neighborhood radius has been produced. No lower bound on P outside this neighborhood is proved. Completing the main goal still requires that global complement, or a different unconditional exclusion.
