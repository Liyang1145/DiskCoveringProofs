# A two-edge ear bound using both sides of one triangle

## Result

Under the generic single-arc restricted Voronoi dual and signed area chain described in `../next/TOPOLOGY.md`, the area deficit of a two-boundary-edge center triangle together with its two switch triangles is strictly greater than (59/1000) U^2. A one-boundary-edge triangle and its switch retain the previous strict defect (19/500) U^2. The center-only dual is an abstract triangulated disk with simple boundary cycle of b>=14 distinct owners, so each center triangle has k=0,1,2 boundary edges. If E triangles have k=2, the total deficit is strictly greater than

    (19/500)(b-2E)U^2 + (59/1000)E U^2
      >= (59/2000)b U^2,

using E<=b/2. Different ear triangles cannot share a boundary edge, and all nonincident triangle deficits are nonnegative. No equal-side or symmetry assumption is used.

The pure rational certificate `verify_coupled_ear.py` combines this defect with the area chain for U=228151/1000000, checking all b=14,...,26. It proves the numerical right-hand side is <31415/10000<pi. Assuming the generic dual topology is independently accepted, it excludes a cover at r0=4563/20000=0.22815 after the small-radius enlargement, reflection and generic perturbation, and compactness gives

    r_D(26) > 4563/20000 = 0.22815.

This is still a lower bound, not an optimality proof or a proof of r_D(26)>0.23.

## Simultaneous two-side geometry

Let the two boundary sides of an ear have lengths xU and yU, with 0<=x,y<=2. Write s=(x+y)/2, h=sqrt(1-s^2/4), and let A,C1,C2 be the ear triangle's area and its two switch areas. Set

    f(t)=t(1+sqrt(1-t^2/4))/2,
    g(t)=t sqrt(1-t^2/4)/2.

The common U-disk witness for the three ear centers and the two common switch points give

    A/U^2 <= f(x), A/U^2 <= f(y),
    C1/U^2 <= g(x), C2/U^2 <= g(y).

Additionally, since the xU and yU sides share a vertex, the elementary side-angle area bound gives A/U^2<=xy/2. This is valid for acute, right, obtuse and degenerate triangles, without requiring their circumradius to be <=U.

The function t sqrt(1-t^2/4) is concave on [0,2]: its second derivative on (0,2) is

    -t(3-t^2/2)/(4(1-t^2/4)^(3/2)) <= 0,

and endpoints follow by continuity. Hence f and g are concave, and xy<=s^2 implies

    A/U^2 <= min(s^2/2, f(s)),
    (C1+C2)/U^2 <= 2g(s)=s h.

Consequently

    (A+C1+C2)/U^2 <= min(s^2/2, s(1+h)/2) + s h.

The two terms inside min switch at s=8/5. For 0<=s<=8/5, the first applies; for 8/5<=s<=2, the second applies. This follows by comparing s and 1+h, with both sides nonnegative.

Use Young's inequality 2sh<=w s^2+h^2/w with w=3/8. On the first interval,

    s^2/2+s h <= 4/3 + (17/48)s^2 <= 56/25.

On the second interval,

    s/2+(3/2)s h <= 2+s/2-(7/32)s^2 <= 56/25,

because the quadratic is decreasing for s>=8/5. Both inequalities agree at the switch point. Therefore A+C1+C2<=56U^2/25.

As (433/250)^2<3,

    3sqrt(3)/4 + 1 - 56/25
       > (3/4)(433/250)+1-56/25 = 59/1000.

This establishes the strict two-edge deficit. Each numerical constant, including the Young evaluations and the 13 area cases, is checked using `Fraction` and integer square roots. Float output, if any, has no acceptance role. Run `python verify_coupled_ear.py` without `-O`.
