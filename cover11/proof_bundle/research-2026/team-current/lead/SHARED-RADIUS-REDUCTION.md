# Shared-radius graph: exactly two nonlinear cycle obligations

Object: established nearest-site 9+2 disk-covering representative, q=0 or1; full compact hub cells and nine single-arc ring cells; locality-preserving Delaunay refinement. All angles/lengths in this note are exact geometric quantities, not rounded optimizer values.

## 1. Endpoint-radius graph H

Make one vertex of H for every refined Delaunay triangular face, and one leaf for every boundary switch (nine leaves). Join face vertices across every internal dual edge; attach each switch leaf to the face incident to its boundary dual edge. If a polygonal cocircular face was triangulated, the triangles remain distinct graph vertices even though their primal Voronoi points coincide. Each has the same positive nearest-site radius; no zero-radius point is introduced.

For boundary cycle length9 and two interior hubs, a triangulated disk has 11 triangular faces and 21 edges. Hence H has 20 vertices,21 edges and is connected. Its cycle rank is 2. This holds for both q0 and q1; an ear triangle gives a pendant part and does not change the count.

Associate a positive radius rho_v to each vertex, the common distance from that primal vertex/switch to its incident sites. For an edge e=vw of H, let a_e,b_e be opposite triangle angles (at a boundary switch use b=pi/2−gamma as in C814). The shared side length identity is
 rho_v sin a_e = rho_w sin b_e = d_e/2.
All relevant angles are strictly between 0 and pi for genuine configurations with distinct sites. Artificial zero-length primal edges still have nonzero site-site distance; their opposite angles sum to pi and their radii are equal. Thus no logarithmic singularity occurs on an actual legal configuration; a limiting collision would require separate closed-domain treatment for a certificate.

## 2. Spanning-tree elimination, necessary and sufficient for edge-length matching

Fix any spanning tree T, root v0. Recursively define positive k_v by k_v0=1 and k_w/k_v=sin a_e/sin b_e along each oriented tree edge. Every positive radius assignment satisfying tree identities is uniquely rho_v=s*k_v, s>0. For each of the TWO non-tree edges, matching is one scalar product identity, equivalently the sum of oriented log-sine ratios around its fundamental cycle is zero.

These two conditions are necessary AND sufficient for existence of positive radii satisfying ALL shared-edge identities. They are independent as graph equations in formal edge ratios. No claim is made that they are functionally independent after further angle constraints, or that edge matching alone constructs a planar unit-disk covering.

Normalize k by max_v k_v=1. Then all endpoint radii<=R is exactly 0<s<=R. This eliminates 19 radius-ratio parameters and all 21 matching equations in favor of TWO cycle obligations and one scale. Tree choice does not alter existence or normalized radii.

## 3. Exact area and chord expressions

Write boundary-switch factors k_i and owned ring-sector angles alpha_i∈[0,pi]. Consecutive switch distance for ring i is
 s*L_i, L_i²=k_{i-1}²+k_i²−2k_{i-1}k_i cos alpha_i.
For a genuine inward-root representative its owned arc is minor, hence w_i(s)=2asin(s L_i/2). Because k_i<=1 and s<=R<1/2, arguments are <=R and no inverse-trig branch ambiguity exists.

The area partition is EXACT:
 A(s)=s² sum_{e=vw} k_v k_w sin(a_e+b_e)
      + (s²/2)sum_i k_{i-1}k_i sin alpha_i
      + (1/2)sum_i(w_i(s)−sin w_i(s)).
For a covering A(s)=pi and sum_i w_i(s)=2pi. The q1 outside-six sum is >=2pi−2asin(2R). This uses actual nearest-owned arcs, not original overlapping arcs.

Each term is nonnegative and nondecreasing in s, since a_e+b_e<=pi and alpha_i<=pi. Therefore every genuine configuration yields necessary inequalities at maximal allowed scale R:
 A(R)>=pi, sum_i w_i(R)>=2pi,
 plus q1 outside-six capacity. Maximal scaling is used only in an algebraic relaxation; it is NOT a WLOG transformation of a real unit-disk covering (the switches need not remain on the unit circle).

The width equation sum_i w_i(s)=2pi has at most one positive solution when at least one L_i>0, and has a solution s<=R iff the total at R is >=2pi. Thus one may also solve for scale uniquely instead of saturating it. Full planar/cyclic closure remains an additional obligation; do not infer sufficiency for disk coverage.

## 4. Numerical mechanism test only

`area_shared_radius.py` retains all20 log radii, face/hub angle sums, actual chord-width sectors and21 shared-edge equations. Positive angles and finite log boxes make it a diagnostic, not domain-covering computation. Six single-start local maxima at R=.38 are approximately 3.04814,3.12769,2.95174,2.95123,3.13522,2.89767, all below pi; these do not upper-bound the global relaxation. The two balanced (6,6) classes now also have local optima below pi, unlike independent-edge models. The exact tree reduction provides a way to inspect whether this comes from genuine metric constraints rather than solver failure.

Remaining implication: prove a global upper bound for the angle-dependent normalized expression, or find a more efficient certified relaxation. No new graph exclusion follows from the local maxima.
