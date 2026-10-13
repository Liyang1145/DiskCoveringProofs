# Sharp-arc shifted-core strengthening of the new 8/7/6 argument

This NEW manuscript strengthens, rather than edits, the bound first scan.
Read it together with n26-shifted-core-eight-seven-six-filled-patch-proof.md.
All of that document's continuous core-coverage, embedded-filled-patch,
seven-disk impossibility and whole-prefix counting arguments apply.
No old frozen code, queued process or report is modified.

## Keep the actual radius-dependent arc bound

Put u=234701/1000000, R=1-2u and alpha=asin(u). A radius-rho boundary
owner has unit-circle footprint at most 2asin(rho)<=2alpha. Thus the
midarc frame of a filled k-consecutive-owner patch gives every patch
center projection at least

    cos((k-2)alpha)-u.

This is stronger than replacing each arc by pi/6. Since
u<1/4<sin(pi/12), even 6alpha<pi/2, so cos is decreasing over all
half-spans in k=3..8. Coincident anchors do not weaken the inequality.

Write q=u^2 and A=1-q. Repeated cosine addition gives

    cos(alpha)  = sqrt(A)
    cos(2alpha) = 1-2q
    cos(3alpha) = sqrt(A)*(1-4q)
    cos(4alpha) = 1-8q+8q^2
    cos(5alpha) = sqrt(A)*(1-12q+16q^2)
    cos(6alpha) = 1-18q+48q^2-32q^3.

At this EXACT rational u these have the following strict rational lower
bounds, respectively:

    c_3=24/25, c_4=22/25, c_5=3/4,
    c_6=29/50, c_7=3/8, c_8=37/250.

For the odd expressions the polynomial factor is positive, and squaring
compares A*factor^2 to c_k^2. Even expressions are rational comparisons.
The accompanying code recomputes every rational margin; no rounded
trigonometric approximation defines or proves these inequalities.

## Three and FOUR owners both require EIGHT outsiders

For k=3 retain the full target disk of radius 1/2 and center (-1/40,0)
from the preceding manuscript.

For k=4 use the full target disk of radius s=47/100, centered at
(-3/50,0). Its farthest norm is s+3/50=53/100, its rightmost x is
41/100. Each of the following exact strict margins is 299/500000:

    R-53/100 > 0,
    s-2u > 0,
    22/25-2u-41/100 > 0.

Consequently the whole disk is inside the core and inaccessible to
boundary owners and every patch center. Seven radius-u disks cannot cover
it, by the self-contained circle-arc argument in the preceding manuscript.
Thus EIGHT distinct original outside nonowners are necessary, not seven.

For clarity, the universal circle-footprint inequality used there can be
written without an optimization assumption. If a disk of radius t<s/2
whose center is at distance d>0 meets a target circle of radius s, its
half-angle beta satisfies

    cos(beta)=(s^2+d^2-t^2)/(2sd)>0,
    (s^2+d^2-t^2)^2-4d^2(s^2-t^2)
        =(d^2-(s^2-t^2))^2 >= 0.

Hence beta<=asin(t/s)<pi/6. A disk covering the target center has
d<=t and misses that circle because s-d>=s-t>t. Six remaining
footprints therefore cannot cover the target circle. This proves the
continuous seven-disk obstruction for arbitrary plane centers.

## Five and six owners

Retain the six and five strictly interior rational targets, respectively,
from the preceding manuscript. The increased c_5 and c_6 only increase
their horizontal separation. Thus SIX and FIVE outsiders are necessary.

## Seven and eight owners: one more target each

For k=7 take FOUR points:

    (-1/10,+/-13/25), (-19/40,+/-47/200).

Their maximum squared norm is 5617/20000; their minimum squared pair
distance is 2209/10000. They are strictly inside the core and separated
by more than 2u. The largest x is -1/10 and

    3/8-2u+1/10=2799/500000>0.

For k=8 take THREE points:

    (-161/500,+/-421/1000), (-53/100,0).

Their maximum squared norm is 280925/1000000 and minimum squared pair
distance is 44101/200000. The largest x is -161/500, with

    37/250-2u+161/500=299/500000>0.

Again all inequalities are exact and strict. The small last separation
margin must not be accepted using rounded decimals.

## Result and scope

The necessary outside-original counts for filled cycles of lengths
3,4,5,6,7,8 are now 8,8,6,5,4,3. If the exact full outside-label budget
26-B-|S| is smaller, the whole prefix is impossible in the inherited
conditional radius scope. The rule is a strict strengthening of the
first shifted-core scan and all queued old-midarc obstructions.

The finite scan and independent source reconstruction test applicability,
ownership, topology, arithmetic and all original/shadow placements. They
do not replace the written continuous proof, actual geometry/current
admission, unresolved candidate-angle analysis or global acceptance.
All raw complete terminals, old payments, partial histories and LOCAL
remain unchanged. n26 is pending; no n27 work is claimed.
