# Sharp shared-disk ear bound and its n=26 consequence

All quantities in this note are exact. The numerical verifier is
`final_heron.py` (SHA256
`307ed8e3d974b72901423004cf814c20605c9d2c5e257d5ff1c08839ba6d3464`).
It uses only the Python standard library, refuses disabled assertions,
and verifies the constants and all 13 area comparisons. The geometric
interfaces are stated explicitly below rather than attributed to the
numerical script.

## Local joint inequality

Let a triangle have vertices a,b,c in a common closed disk of radius U.
Let edges ab and ac each have a switch point q within U of both its
endpoints. Write A for the absolute area of triangle abc, and C1,C2 for
the absolute areas of switch triangles qab and q'ac, respectively.
Then

    A + C1 + C2 < (3 sqrt(3)/4 + 1 - 97/1000) U^2.

Normalize U=1. Let x=|a-b|, y=|a-c|, z=|b-c|, and s=x^2+y^2.
The unit common disk may be centered at the origin. If m=(b+c)/2 and
h=(b-c)/2, then |m|^2+|h|^2 <= 1 and

    s = 2|a-m|^2 + 2|h|^2 <= 4+4 sqrt(1-z^2/4).

For 4<=s<=8, both sides are nonnegative and this implies

    z^2 <= 2s-s^2/4 <= s.

Heron's identity and 4 x^2 y^2 <= (x^2+y^2)^2 give

    16 A^2 = 4 x^2 y^2 - (s-z^2)^2
           <= z^2 (2s-z^2).

The right side is increasing in z^2 on [0,s]. Therefore

    A <= s sqrt(s(8-s))/16.                         (1)

Each switch point belongs to the lens of the two unit disks at its
endpoint centers. Hence

    C1 <= (x/2) sqrt(1-x^2/4),
    C2 <= (y/2) sqrt(1-y^2/4).

Cauchy's inequality and x^4+y^4 >= s^2/2 yield

    C1+C2 <= sqrt(s(8-s))/4.                         (2)

Combining (1)-(2), for 4<=s<=8,

    A+C1+C2 <= (s+4) sqrt(s(8-s))/16.

Its square is `(s+4)^2 s(8-s)/256`; its derivative has the sign of
`-(s^2-4s-8)`. Its maximum on [4,8] is at s=2+2 sqrt(3), with maximum
squared `9/4+3 sqrt(3)/2`. Rational comparison using
`sqrt(3)<17321/10000` shows that maximum is strictly <1101/500=2.202.
For s<=4, the independent bounds A<=xy/2<=s/4<=1 and C1,C2<=1/2
show A+C1+C2<=2<2.202. Also `sqrt(3)>433/250` implies

    3 sqrt(3)/4+1 > 2299/1000 = 2.299.

The joint deficit is therefore strictly greater than 97/1000. The
local inequality needs no acute-triangle assumption and does not
assume that the three vertices lie on the witness circle.

For a face with only one boundary edge, write x for that edge length
and y=sqrt(1-x^2/4). Its triangle and associated switch satisfy

    (A+C)/U^2 <= x/2 + x y.

With w=37/100 and a=1/(4w)-w>0, Young's inequality gives

    x/2+xy <= 1/(2w) + x/2 - a x^2/2
             <= 1/(2w)+1/(8a) = 147325/83694.

The exact verifier checks this is more than 19/500 below
`3 sqrt(3)/4+1/2`, using `sqrt(3)>433/250`.

## Summing over boundary incidences

Use the generic single-arc restricted Voronoi dual with n<=26 distinct
centers and b>=14 boundary owners. Its center-only subcomplex is an
abstract triangulated disk with boundary cycle consisting of the b
owner-center edges. Every boundary edge is incident to precisely one
center-only triangle and to its own switch triangle. For b>=14, a
center-only triangle has at most two boundary-cycle edges. Every
center-only triangle has a common U-disk witness at the corresponding
restricted Voronoi triple point; every switch point is within U of its
two centers. These are geometric premises of the local inequalities,
not consequences of pairwise center distances alone.

Partition the center-only triangles by whether they contain 0, 1, or 2
boundary edges. A zero-edge face has nonnegative deficit from
`3 sqrt(3) U^2/4`. A one-edge face and its switch have deficit
>19 U^2/500. A two-edge face and its two switches have joint deficit
>97 U^2/1000 > 2*(19 U^2/500). Since switch edges are unique and each
face is charged once, the total deficit is strictly greater than

    (19/500) b U^2.

This grouping avoids double-counting a two-edge face. The area bound is

    pi < (50-b)*(3 sqrt(3)/4)*U^2 + b*U^2/2
         + b*g_U(pi/b) - (19/500)*b*U^2,

where

    g_U(t)=t-sin(t)cos(t)+sin(t)sqrt(U^2-sin(t)^2).

Here 2n-b-2<=50-b bounds the number of center-only faces. The original
area identity is an oriented 2-chain: the boundary fans are signed,
not a sum of unsigned circular segments and triangles. The switch and
center triangles are bounded by absolute area; Jensen applies because
`g_U` is concave on `[0,asin U]` for U<1/2.

## Exact comparison and scope

For target r0=571/2500=0.2284, choose the strictly larger generic
radius U=228401/1000000=0.228401. The verifier checks `U<sin(pi/13)`,
so 14<=b<=26, proves rational enclosures for pi, sin, cos and square
roots, and checks every b=14,...,26 satisfies

    right hand side < 314159/100000 < pi.

Thus the inequality above contradicts a generic U-cover. The global
conclusion `r_D(26)>0.2284` additionally uses the separately established
reflection/perturbation, single-arc boundary, restricted-dual disk, and
oriented-area interfaces, as well as compactness of the covering-radius
minimization. This note supplies the new local bound and finite exact
arithmetic; it does not prove an exact optimum or discharge the original
16/4957/344 frontier obligations.

Run:

    python round-20261030b/lower/next/final_heron.py
