# Joint edge–face area defect for the 26-disk lower bound

## Statement and checked consequence

Let U>0. In a generic single-arc restricted Voronoi dual, suppose the b≥14 distinct boundary owners are c_0,...,c_{b-1}, and q_i is the boundary switch between owners c_i and c_{i+1}. Each switch triangle has both centers within U of q_i. Each center-only dual triangle has a common point within U of all three of its centers.

The center-only part of the abstract dual is a triangulated disk whose boundary is the simple b-edge cycle c_0 c_1 ... c_{b-1}. This follows by deleting the 2b boundary-band faces (q_{i-1},q_i,c_i) and (q_i,c_i,c_{i+1}) from the full abstract disk. Consequently each center-cycle edge is incident to exactly one center-only triangle; because b≥14, such a triangle has at most two center-cycle edges. These statements concern abstract incidences, not whether the straight edges form a geometric embedding.

For every center-cycle edge e, write C_e for the absolute area of its switch triangle and A_e for that of its incident center-only triangle. Define

    Amax = (3sqrt(3)/4) U²,
    D_e = U²/2 - C_e,
    D_T = Amax - area(T).

Each deficit is nonnegative. The coupling proved below is

    D_T + D_e > (19/500) U²

for the triangle T incident to e. Summing the b inequalities counts a center triangle's D_T at most twice and each D_e once. Since all deficits are nonnegative, the actual total area deficit satisfies

    sum_T D_T + sum_e D_e > (19/1000) b U².

This is a rigorous, topology-aware improvement over independently bounding every interior and switch triangle. It does not involve the old rectangle/lens monotonicity conditions or claim the separate b pairs are geometrically independent.

Combining it with the single-arc signed area chain and concavity of the fan term gives the strict upper bound

    π < (50-b)(3sqrt(3)/4)U² + b U²/2
        + b g_U(π/b) - (19/1000)b U²,
    g_U(t)=t-sin(t)cos(t)+sin(t)sqrt(U²-sin²(t)),

for any generic cover by at most 26 U-disks. `verify_joint_area.py` checks with pure rational arithmetic that, when U=22781/100000, the right side is less than 31415/10000<π for all b=14,...,26. A cover with radius at most 1139/5000 can be reflected and perturbed to a generic U-cover with uniform positive margin as in `TOPOLOGY.md`. Therefore such a cover is impossible; compactness gives

    r_D(26) > 1139/5000 = 0.2278.

This result remains subject to independent audit of the stated dual triangulation interface. It neither identifies the known numerical candidate nor proves the global optimum, and this defect alone does not reach 0.23.

## Proof of the pairwise inequality

Let L=|c_i-c_{i+1}|. Since q_i is within U of both endpoints, 0≤L≤2U. The distance of q_i from the line through the endpoints is at most sqrt(U²−L²/4); hence

    C_e ≤ (L/2)sqrt(U²−L²/4).

The incident center triangle has a common U-disk witness p. Its distance from the same endpoint line is at most sqrt(U²−L²/4). The triangle's third vertex is within U of p, so its distance from that line is at most U+sqrt(U²−L²/4). Hence

    A_e ≤ (L/2)(U+sqrt(U²−L²/4)).

Put x=L/U, y=sqrt(1−x²/4) and w=37/100. The elementary square (sqrt(w)x−y/sqrt(w))²≥0 gives 2xy≤w x²+y²/w. Consequently, setting a=1/(4w)−w>0,

    (A_e+C_e)/U² ≤ x/2+xy
       ≤ 1/(2w) + x/2 − a x²/2
       ≤ 1/(2w)+1/(8a) = 147325/83694.

The final maximum follows from the square −a(x−1/(2a))²/2≤0; it holds on all real x, in particular [0,2]. The exact inequalities (433/250)²<3 and

    (3/4)(433/250)+1/2−147325/83694 > 19/500

establish the desired per-edge strict defect. All these constants are rational and are rechecked by `verify_joint_area.py`; no floating point is used for acceptance. See `TOPOLOGY.md` for the independent general-position, signed-chain and limiting details.
