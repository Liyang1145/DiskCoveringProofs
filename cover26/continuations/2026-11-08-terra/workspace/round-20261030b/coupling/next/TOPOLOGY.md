# Edge-face coupling and a proposed lower bound for 26-disk covering

All formulas below are independent of the numerical proposal for an optimal covering. Put `r0=1139/5000` and `U=22781/100000`. The exact arithmetic premises of the inequality for this U are checked by `verify_joint_area.py`. The geometric and topological argument below is the corresponding proof interface.

## Reducing to a generic cover

Suppose at most 26 closed disks of radius r0 cover the unit disk D. Regard them as U-disks and set H=sqrt(1−U²). For each center c with norm d>H replace c by c'=(H²/d²)c. With λ=H²/d²,

    |x-c'|²-U² = λ(|x-c|²-U²)+(1-λ)(|x|²-1).

Every x in D originally covered by the r0-disk is therefore strictly inside the replacement U-disk. Unchanged disks also cover the same points strictly. The nearest-center distance is continuous on compact D, so the U-cover has a uniform positive margin. Move all centers slightly toward the origin, then perturb them slightly and independently, retaining the cover and ensuring distinct centers, all norms <H, no four cocircular centers and no boundary triple ties. These generic restrictions avoid only a finite union of algebraic exceptional sets.

For two distinct centers with norms <H, their perpendicular bisector has distance strictly less than H from the origin: in its normal direction their signed coordinates differ by their distance and have average the bisector coordinate. Consequently the two intersections of their bisector with the unit circle are more than 2U apart.

Each center's disk covers at most one short circular boundary arc of half-angle asin U. Since D is covered, every point where that center is nearest is in its disk. If its boundary Voronoi cell had two points in this short arc with another center strictly nearer at an intermediate point, the distance-difference function would have two distinct zeros on that arc. Their chord length would be at most 2U, contradicting the preceding bisector fact. Thus each boundary Voronoi cell is one arc or empty. Boundary switch points are generic and finite. Let b be the number of positive-length owner arcs. Their half-angles δ_i sum to π and each is at most asin U. The exact certificate verifies 13 asin U<π, so 14≤b≤n≤26. This b is the transformed cover's number of owner arcs, not the number of all disks that meet the unit boundary.

## Abstract dual and oriented area

Each restricted Voronoi cell is convex, contains its own distinct center in its interior, and meets the unit boundary in at most one arc. Its planar dual inside D is an abstract triangulated disk: centers are the n interior vertices; the b consecutive boundary switches q_i are boundary vertices; a generic interior Voronoi vertex gives one center-only triangle; each switch q_i gives triangle (q_i,c_i,c_{i+1}); each owner arc gives triangle (q_{i-1},q_i,c_i). Dual edges can be embedded as paths through their shared Voronoi edges. We do not require the actual straight segment between two centers to stay in these cells or avoid other edges.

The dual has V=n+b, b boundary edges, and F triangles. Euler plus 3F=2E−b gives F=2n+b−2. Subtracting the 2b boundary triangles leaves

    T=2n-b-2 ≤ 50-b

center-only triangles. Each such triangle has a common U-disk witness: its corresponding interior Voronoi vertex p lies in D, is covered by at least one disk, and has those three centers as nearest sites. Each switch triangle has q_i in both adjacent center disks.

Map each abstract vertex to its actual point in the plane and map each triangle affinely. Orient the abstract triangles consistently. The signed area of an affine triangle is half its oriented boundary cross-product sum. On summing, all interior edges cancel exactly; the remainder is the signed area of the q_i polygon. Adding the b nonnegative areas of the circular segments between that polygon and the unit circle gives exactly π. Hence π is at most the sum of the absolute areas of all triangular images and the circular segments. This signed-chain identity does not assume the straight images form an embedding; folding and overlap are harmless. The q_i occur in circular order, so the circular segments are the usual disjoint segments.

Every center-only triangle lies in a U-disk and has area at most A=3sqrt(3)U²/4. Every switch triangle has area at most U²/2. For one owner arc of half-angle δ, the adjacent anchor/center triangle and circular segment have total area at most

    g_U(δ)=δ-sinδ cosδ+sinδ sqrt(U²-sin²δ).

For s=sinδ, c=cosδ, z=sqrt(U²-s²), one has

    z³ g_U''(δ)/s = 4c z³ - U⁴ - 3U² + 6U²s² + 2s² - 4s⁴
                    ≤ U²(5U²−1) < 0.

Here cz≤U, 6U²+2−4U>0, and s²≤U². Endpoints follow by continuity. Hence g_U is concave and Jensen bounds the sum by b g_U(π/b).

## Sharing each boundary edge forces a definite area defect

The center-center edge c_i c_{i+1} on the dual boundary is incident to exactly one center-only triangle. Let L be its length. The triangle's common U-disk witness is within U of both endpoints, so its distance to their line is at most sqrt(U²−L²/4); its third center is at most U farther from that witness. Therefore its area A_i is at most

    (L/2)(U+sqrt(U²−L²/4)).

Likewise q_i is within U of both endpoints, so the switch triangle area C_i is at most

    (L/2)sqrt(U²−L²/4).

Set x=L/U in [0,2] and y=sqrt(1−x²/4). Young's inequality with w=37/100 gives

    x/2+xy ≤ x/2 + (w x²+y²/w)/2
            ≤ 1/(2w)+1/[8(1/(4w)−w)] = 147325/83694.

The old separate bound was (3sqrt(3)/4+1/2)U². Since sqrt(3)>433/250, the difference exceeds (19/500)U²; the script verifies the exact rational comparison. Thus each paired boundary edge has

    (A−A_i)+(U²/2−C_i) > (19/500)U².

A center-only abstract triangle can contain at most two edges of the b-edge boundary-center cycle because b≥14; three would close a 3-edge cycle component. Each switch occurs once and each center triangle occurs at most twice in the b paired inequalities. All deficits are nonnegative, so their actual aggregate is greater than (19/1000)b U². Subtracting that amount from the former independent area bound yields

    π <or≤ (50−b)(3sqrt(3)/4)U² + b U²/2
           + b g_U(π/b) − (19/1000)b U².

More precisely the left inequality is ≤ before applying the strict defect; the displayed right side is a strict upper bound on the summed areas. `verify_joint_area.py` checks that, for every b=14,...,26, this right side is less than 31415/10000<π. Therefore the assumed r0-cover is impossible, conditional only on the explicit generic dual construction above. Compactness of center configurations after projection onto D gives attainment of the minimum covering radius and makes the exclusion strict: r_D(26)>1139/5000.

The numerical verification does not prove an exact optimum, identify the archived candidate root, or establish r_D(26)>.23. The r=.23 improvement remains insufficient under this particular defect bound.
