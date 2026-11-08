# Independent review: two-edge face deficit

The independent `check_stronger_independent.py` verifies the frozen 13-family arithmetic at U=228251/1000000. Its smallest conservative rational gap is at b=17, greater than approximately 0.0005994021. The 23/100 negative control refuses to certify b=15,...,19. This file and checker supplement `AREA-REVIEW.md`: the geometry, abstract dual and one-edge deficit reviewed there remain necessary; only the estimate for an interior face adjacent to two boundary-cycle edges is replaced below.

## Two-edge geometric inequality

Scale U to 1 and choose an interior triangle with sites u,v,w in a common unit disk. Translate the disk center to the origin; no circumcircle assumption is made. Let z=|u-v|, let x=|w-u| and y=|w-v|, and write s=x²+y². Set m=(u+v)/2 and h=(u-v)/2. Since |u|,|v|,|w|≤1,

    |m|²+|h|²=(|u|²+|v|²)/2≤1,
    s=2|w-m|²+2|h|²≤4+4√(1−z²/4).

For s≥4 both sides of `(s−4)/4≤√(1−z²/4)` are nonnegative, hence squaring gives z²≤2s−s²/4. The side lengths are at most2 and 0≤s≤8. In the s≤4 case, triangle area A≤xy/2≤s/4≤1. In the s≥4 case, Weitzenbock's inequality gives

    A≤(√3/12)(s+z²)≤(√3/12)(3s−s²/4).

The cited inequality follows directly from Heron's identity: if a,b,c are side lengths and A is area, then `(a²+b²+c²)²−48A²=2[(a²−b²)²+(b²−c²)²+(c²−a²)²]≥0`. It holds for every triangle, including degenerate and obtuse triangles, and does not require its circumcenter to be in the unit disk.

For the two associated switching faces, their third vertices are within distance1 of both endpoints of the corresponding edges. Their total area is at most

    (x/2)√(1−x²/4)+(y/2)√(1−y²/4)
      ≤√(s(8−s))/4≤1−(s−4)²/32.

The first inequality is Cauchy-Schwarz. The second follows from √(1−v)≤1−v/2, with v=(s−4)²/16∈[0,1]. Thus A plus the two switching areas is at most2 for s≤4. For 4≤s≤8 it is at most the concave quadratic

    1−(s−4)²/32+(√3/12)(3s−s²/4).

The factor multiplying √3 is positive over this interval, so replacing √3 by a rational upper bound preserves the direction. The source checker uses 1733/1000 and obtains the global quadratic upper bound K=28873867/12932000<2.233; the independent checker uses 1732051/1000000 and recomputes the vertex and maximum exactly. Since √3>433/250, the independent old bound `(3√3/4+1)` exceeds the source K by more than 33/500; its excess beyond 33/500 is exactly 3289/12932000. The independent tighter rational bound also passes this comparison.

## No double counting

As reviewed in `AREA-REVIEW.md`, the b distinct boundary-owner centers form an abstract cycle, every cycle edge has one associated switching triangle and one adjacent interior site triangle, and an interior triangle meets at most two cycle edges because b≥14. Assign each switching triangle to that unique interior triangle. If N1 faces have one assigned switching triangle and N2 have two, then b=N1+2N2. The separately checked one-edge deficit exceeds 19/500 per edge and the new two-edge deficit exceeds 33/500 per two-edge face. Therefore the aggregate is at least

    (19/500) N1+(33/500) N2 ≥ (33/1000) b

in units of U². Each actual face occurs in only one assigned group; this is not a repeated subtraction. Subtracting the non-strict lower bound from the former total area upper bound is safe.

The original checker's 13-family result at U=228251/1000000 and the independently reproduced scalar bounds support the target `r_D(26)>913/4000=0.22825`, once the geometric proof in `AREA-REVIEW.md` is used. The arithmetic at U is strict; by continuity of the finite family and strict domain conditions it also holds at some slightly larger radius, so the same argument plus compactness supports `r_D(26)>228251/1000000`. Neither assertion identifies the exact optimum or pays the archived 16/4957/344 candidate obligations.
