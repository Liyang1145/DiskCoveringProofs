# Independent geometric interface review for Voronoi area route

This note does not itself certify the new radius bound; it records the mathematical checks and the remaining review boundary for the area construction in the sibling `area`, `audit`, and `coupling` directories.

1. **Reflection.** For U<1, d=|c|>R=sqrt(1−U²), and λ=(1−U²)/d², the reflected center c'=λc satisfies exactly

       |x−c'|²−U² = λ(|x−c|²−U²) + (1−λ)(|x|²−1).

   Thus its U-disk contains the original U-disk intersected with D; equality holds on the unit circle. Since λ>0, an original cover at a strictly smaller radius is pointwise strict after reflection. Compactness then gives a uniform margin before perturbation and genericity. Do not claim that distances decrease at every x∈D.

2. **Single boundary ownership arc.** When all perturbed center norms are strictly <R, every pair of distinct centers has bisector distance from the origin at most (|c_i|+|c_j|)/2<R. Its circle-intersection chord is consequently >2U. In a cover, every point owned by center i is in disk i; its disk covers on the unit circle a single arc of total width at most 2asin U<π. If a Voronoi owner i had two separate boundary arcs, select two strictly owned points inside those arcs and a point between them where another fixed owner j is strictly nearer. By continuity, the pairwise bisector of i,j crosses the covered arc at two points, which are at distance at most 2U because both belong to disk i. This contradicts the >2U bisector chord. Genericity must separately exclude multiple ties on ∂D, isolated owner arcs and four-way interior Voronoi vertices.

3. **Restricted dual and face count.** Distinct centers in D belong to their own Voronoi cells, whose intersections with D are convex. A suitably embedded topological dual with one boundary interval per boundary owner has a triangulated disk and b boundary owners. Euler then gives `T=2n−b−2≤50−b`. The construction must explicitly justify the topological dual, including the boundary cycle and no crossing of dual arcs; it is not enough to assume an arbitrary contact graph. A Voronoi triple point p corresponding to an interior face lies in D. Since the p-nearest center is at distance ≤U and all three are tied, all three vertices lie in the same radius-U disk centered at p. This common witness, not merely pairwise center distances, justifies area ≤3sqrt(3)U²/4.

4. **Signed fan area.** Let q_{i−1},q_i be consecutive circle-boundary ownership switches, with angular gap 2δ_i and midpoint unit direction u_i. The oriented area of the fan bounded by the two segments to c_i and the unit circle arc is

       δ_i − sin(δ_i) (c_i·u_i).

   Both anchors lie within U of c_i; the endpoint lens yields c_i·u_i≥cosδ_i−sqrt(U²−sin²δ_i), and hence the oriented fan is ≤g(δ_i). This remains true if c_i is on the outer side of the anchor chord. In that case adding the two **unsigned** triangle and circle-segment areas is not the same quantity; the proof should use the oriented 2-chain and cancellation. Each switch triangle has |area|≤U²/2 since its two center-to-anchor sides are ≤U. Summing oriented chain boundaries leaves the unit circle, so inner triangle and switch absolute upper bounds plus fan signed upper bounds yield the area inequality even when the affine images overlap.

5. **Concavity.** For s=sinδ, c=cosδ and h=sqrt(U²−s²)>0, direct differentiation gives

       g''(δ)=s(4c−h−(3c²−s²)/h−s²c²/h³).

   Since U<1/2, h≤U and 3c²−s²=3−4s²≥3−4U², the bracket is at most `4−(3−4U²)/U<0`. Hence g is concave on the open interval and extends continuously to endpoints, so Jensen applies. The final strict numerical comparison is a separate exact-arithmetic obligation, not a consequence of the topology alone.

The independent numerical scripts and final topological writeup must still be rechecked before promoting any suggested stronger global bound. In particular, none of these arguments pays an original n26 finite-prefix/OPEN count by itself.
