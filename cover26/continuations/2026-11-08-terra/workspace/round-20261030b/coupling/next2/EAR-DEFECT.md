# Two-edge ear improvement for the disk-covering area bound

## Statement

Let U=228081/1000000. Assume the generic restricted Voronoi dual described in `../next/TOPOLOGY.md`: n<=26 distinct center vertices, b boundary-owner arcs, 14<=b<=26, and a center-only triangulated disk bounded by the simple b-edge center cycle. Each center-only triangle has one common witness within U of its three centers. The switch triangle associated with each boundary edge has a common witness within U of its two endpoints.

Put Amax=(3sqrt(3)/4)U^2. A center-only triangle T with k boundary-cycle edges has k=0,1, or 2 because b>=14. Let C_e be the switch-triangle area at edge e, and set

    D_T = Amax - area(T) >= 0,
    D_e = U^2/2 - C_e >= 0.

For k=1, the previously verified shared-edge argument gives

    D_T + D_e > (19/500) U^2.

For k=2, the new argument below gives

    D_T + D_e1 + D_e2 > (54/1000) U^2.

The triangles with k=0 contribute nonnegative D_T. If there are E ears with k=2, then b-2E triangles have k=1, so the total deficit is strictly greater than

    (19/500)(b-2E)U^2 + (54/1000)E U^2
    >= (27/1000)b U^2,

where E<=b/2. This treats each triangle deficit and each switch deficit exactly once. It does not use a symmetry assumption or count independent realizations of adjacent edges.

## Bound for a two-edge ear

Let x_i=L_i/U in [0,2], where L_1,L_2 are the lengths of the two boundary edges of T, and let y_i=sqrt(1-x_i^2/4). The shared witness and switch geometry of `../next/JOINT-DEFECT.md` give, separately for i=1,2,

    (area(T)+C_i)/U^2 <= f(x_i) = x_i/2 + x_i y_i,
    C_i/U^2 <= g(x_i) = x_i y_i/2.

Adding the two first inequalities and the two second inequalities, then dividing by 2, gives

    (area(T)+C_1+C_2)/U^2
      <= (f(x_1)+g(x_1)+f(x_2)+g(x_2))/2
      <= max_{0<=x<=2} [x/2 + (3/2)x sqrt(1-x^2/4)].

The last line is the maximum of the arithmetic average of two numbers. It holds for unequal x_1 and x_2 and does not assert the individual bounds are simultaneously attainable.

Let w=101/250 and a=1/(4w)-w>0. Young's inequality follows from a square and gives, for y=sqrt(1-x^2/4),

    2xy <= w x^2 + y^2/w.

Completing the square then yields, for all x in [0,2],

    x/2 + (3/2)xy
      <= 3/(4w) + x/2 - (3a/4)x^2
      <= 3/(4w) + 1/(12a)
      < 22444/10000.

Moreover sqrt(3)>433/250, so

    Amax/U^2 + 1 - 22444/10000
      > (3/4)(433/250)+1-22444/10000
      > 54/1000.

The script verifies these rational inequalities, with no floating point acceptance.

## Exact numerical consequence and scope

The signed area identity, the boundary fan concavity, and the generic reduction are unchanged from `../next/TOPOLOGY.md`. Substituting the total deficit gives, for every feasible b,

    pi < (50-b)(3sqrt(3)/4)U^2 + b U^2/2
         + b g_U(pi/b) - (27/1000)b U^2.

`verify_ear_area.py` checks using rational interval arithmetic and integer square roots that this expression is strictly below 31415/10000<pi for every b=14,...,26. If a cover of radius at most r0=2851/12500=0.22808 existed, reflect and generically perturb its centers after enlarging to U>r0 while retaining positive cover margin. That cover would contradict the inequality. Compactness ensures the covering radius infimum is attained, so the conclusion is

    r_D(26) > 2851/12500 = 0.22808.

This is a lower bound, not an optimality proof, and is conditional on independent audit of the generic dual topology and its simple center-cycle boundary. The exact numerical script uses only Python's standard library and rejects optimized mode. Run `python verify_ear_area.py` from this directory.
