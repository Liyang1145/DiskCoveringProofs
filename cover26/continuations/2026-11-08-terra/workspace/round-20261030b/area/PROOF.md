# A strict lower bound for covering a disk with 26 congruent disks

Date: 2026-10-30, Asia/Shanghai.

Let D be the closed unit disk. Let r_D(26) be the minimum radius for a
cover of D by 26 closed congruent disks with arbitrary centers in the plane.
Repeated centers, redundant disks and all boundary degeneracies are allowed.

The result proved here is

    r_D(26) > 11421/50000 = 0.22842.

Together with the previously checked MinMax Arena construction this gives

    0.22842 < r_D(26) <= 0.234700091.

This is a partial lower bound, not an exact optimum, a new identification of
the archived candidate root, or a formal proof in a proof assistant. The
argument below supplies the geometric proof; two separate rational programs
check its finite scalar inequalities. Their execution cannot replace review
of the geometric argument. No claim of priority or external review is made.

## 1. Strict normalization and general position

Suppose that at most 26 disks of radius r0=11421/50000 cover D. Set

    U = 228421/1000000 > r0,       H = sqrt(1-U^2).

Regard the original disks as U-disks. If a center c has norm d>H, replace
it by c'=(H^2/d^2)c. For lambda=H^2/d^2 in (0,1), direct expansion gives

    |x-c'|^2-U^2
      = lambda (|x-c|^2-U^2) + (1-lambda)(|x|^2-1).

For every x in D originally covered by that r0-disk, the right side is
strictly negative. Unchanged centers also cover their old points strictly.
The continuous nearest-center distance on compact D consequently has a
uniform positive margin below U. Move all centers slightly inward and
perturb them independently, preserving this margin, to obtain distinct
centers of norms strictly less than H in general position. We avoid three
collinear centers, four cocircular centers and triple nearest-site ties on
the unit circle, as well as boundary tangencies of Voronoi edges. Each is
an algebraic exceptional condition with empty interior; finitely many such
conditions can be avoided by arbitrarily small perturbations.

Write m<=26 for the resulting number of sites. Each site is in the interior
of D and in the strict interior of its own restricted Voronoi cell.

## 2. Every boundary ownership cell is a single short arc

For two distinct sites c_i,c_j, their perpendicular bisector has distance
h<H from the origin. Indeed their projections onto its normal differ by
L=|c_i-c_j| and have average equal to its signed offset; the larger absolute
projection is h+L/2. Both site norms are <H. Thus the bisector's two
intersections with the unit circle are at chord distance

    2 sqrt(1-h^2) > 2U.

The boundary footprint of any U-disk is empty, a point, or one circular
arc of half-angle at most asin(U)<pi/2. Every point where its site is nearest
belongs to that footprint, because D is covered. Suppose two such ownership
points a,b have a point between them on that short footprint arc where some
other site is strictly nearer. The squared distance difference for these
two sites is nonnegative at a,b and negative in between. It has two distinct
zeros in the same footprint arc. Those zeros are bisector-circle crossings
at chord distance <=2U, a contradiction.

Thus each restricted cell meets the unit circle in one arc or is disjoint
from it. General position excludes isolated ownership points. Let b denote
the number of positive-length owner arcs, let q_0,...,q_(b-1) be their
switching points in counterclockwise order, and let their half-angles be
delta_i. Then

    sum delta_i = pi,     0<delta_i<=asin(U),     b<=m<=26.

The rational check sin(pi/13)>U gives b>=14. This b counts transformed
Voronoi owners. It is not assumed equal to the original or transformed
number of disks intersecting the unit circle. No classification by that
different count is used in this proof.

## 3. The abstract dual and its signed area identity

Restricted Voronoi cells are convex and contain their own sites. Within
each cell connect its site to chosen interior points of its shared cell
edges, and to its boundary switches. These paths give an embedded abstract
dual. Each generic interior Voronoi vertex yields a three-site triangular
face; every switch q_i yields a face (c_i,q_i,c_(i+1)); and every owner arc
yields a face (q_(i-1),q_i,c_i). The last face has the circular arc as its
outer edge. Equivalently replace this arc by an abstract edge for the
combinatorial count. Convexity permits the paths in their cyclic order
without crossings. They decompose D into these faces.

The resulting abstract triangulated disk has m interior site vertices and
b boundary vertices q_i. If F and E denote its face and edge counts, then

    (m+b)-E+F=1,       3F=2E-b,       F=2m+b-2.

Exactly 2b faces are the two boundary types. There are therefore

    T=2m-b-2 <= 50-b

center-only faces. Each has a common U-disk witness: its corresponding
interior Voronoi vertex is in D and has distance <=U to its three nearest
sites. Each switch is within U of both adjacent owner sites.

Orient all abstract faces consistently and map their vertices to their
actual sites and switches. The sum of their signed straight triangle areas
equals the signed area of the q_i polygon, because each interior oriented
edge cancels. Add the circular segment areas between consecutive q_i. The
result equals pi. We may upper-bound every signed triangle by its absolute
area. The straight images may overlap, cross or reverse orientation; none
of those phenomena affects this algebraic identity.

For a triangle whose three vertices lie in a U-disk, its absolute area is
at most A=(3 sqrt(3)/4)U^2. For example, maximize area over the three points
in that disk; each maximizing vertex can be moved to its boundary, and the
maximum inscribed triangle is equilateral. A switch triangle has absolute
area <=C=U^2/2.

For an owner arc with half-angle delta, put s=sin(delta). Its endpoints
are at chord distance 2s. Their common U-disk center is within perpendicular
distance sqrt(U^2-s^2) of their chord line, so the owner triangle has absolute
area <=s sqrt(U^2-s^2). The circular segment has area delta-s cos(delta).
Their sum is bounded by

    G_U(delta) = delta - sin(delta)cos(delta)
                   + sin(delta)sqrt(U^2-sin(delta)^2).

This is an upper bound even if the triangle and circular segment overlap;
we never assert an unsigned partition by these straight images.

## 4. Concavity of the boundary contribution

For 0<delta<asin(U), set s=sin(delta), c=cos(delta) and
z=sqrt(U^2-s^2). Differentiation gives

    G_U' = 2s^2 + c(U^2-2s^2)/z,
    z^3 G_U''/s = 4cz^3-U^4-3U^2+6U^2s^2+2s^2-4s^4.

Use cz^3<=U(U^2-s^2), -4s^4<=0, s^2<=U^2, and
6U^2+2-4U>0. The last display is at most

    4U^3-U^4-3U^2+(6U^2+2-4U)s^2
      <= U^2(5U^2-1) < 0.

The domain inequality is checked exactly. Continuity at the endpoints
extends concavity to [0,asin(U)]. Hence Jensen's inequality gives

    sum G_U(delta_i) <= b G_U(pi/b).

## 5. Shared edges force a definite area loss

Deleting the 2b boundary faces of the abstract dual leaves a triangulated
center disk with the simple boundary cycle c_0,...,c_(b-1). Each cycle edge
is adjacent to exactly one center-only triangle and one switch triangle.
A center-only triangle has at most two cycle edges: three would make the
whole boundary cycle have three vertices, whereas b>=14.

For a cycle edge of length L, write h=sqrt(U^2-L^2/4). Its switch triangle
has absolute area <=Lh/2. The common U-disk witness of its adjacent internal
triangle is within distance h of the edge line; the third site is at most
U farther from that line. Thus the internal triangle has area <=L(U+h)/2.
With x=L/U in [0,2], define

    f(x)=x/2+x sqrt(1-x^2/4),
    j(x)=x sqrt(1-x^2/4)/2.

The sum of one internal triangle and its switch is <=U^2 f(x), while a
switch alone is <=U^2 j(x).

For w>0, y=sqrt(1-x^2/4), and a=1/(4w)-w>0, Young's inequality gives

    2xy <= w x^2+y^2/w,
    x/2+t xy <= t/(2w)+x/2-(ta/2)x^2
               <= t/(2w)+1/(8ta),       t>0.

Using t=1,w=37/100 yields f(x)<=147325/83694. Since sqrt(3)>433/250,
the independent bound A+C exceeds this joint bound by more than
(19/500)U^2. This is the loss for a center triangle with one cycle edge.

For a center triangle with two cycle edges we use the fact that its three
vertices share the same U-disk, instead of treating the edges independently.
Scale to U=1. Write its vertices as u,v,w in the unit disk, its two cycle
edge lengths as x=|u-v|, y=|u-w|, and its third edge length as z=|v-w|.
Set s=x^2+y^2. If M=(v+w)/2 and h=(v-w)/2, then

    |M|^2+|h|^2 <= 1,     |h|=z/2,
    s = 2|u-M|^2+2|h|^2
      <= 4+4|M| <= 4+4 sqrt(1-z^2/4).

For 4<=s<=8 this implies z^2<=Z=2s-s^2/4<=s. Heron's identity and
4x^2y^2<=s^2 imply

    16 area(T)^2 = 4x^2y^2-(s-z^2)^2 <= z^2(2s-z^2).

The last expression increases as a function of z^2 on [0,s]. Consequently

    area(T) <= sqrt(Z(2s-Z))/4 = s sqrt(s(8-s))/16.

The two switches together have area at most sqrt(s(8-s))/4. This follows
by applying concavity of sqrt(t(4-t)) on [0,4] to t=x^2,y^2 and their
individual lens bounds j(x),j(y). Thus the three-face group has area at most

    F(s)=(s+4)sqrt(s(8-s))/16,        4<=s<=8.

The maximum occurs at s=2+2 sqrt(3), with

    max F(s)^2 = 9/4+(3/2)sqrt(3).

For 0<=s<=4, use area(T)<=xy/2<=s/4<=1 and the switch sum <=1;
the group is then bounded by 2. The estimates for s>=4 are never applied
in this second range. Since sqrt(3)<17321/10000, both cases give a group
area strictly less than 1101/500=2.202. Its independent bound is
3 sqrt(3)/4+1, whose excess is strictly greater than 97/1000. Scaling back
restores a factor U^2. These arguments include obtuse and degenerate
triangles; the common disk is an enclosing disk, not an assumption that
the three vertices lie on a circle of radius U.

Assign every switch triangle to its unique neighboring center-only
triangle. If N1,N2 internal triangles receive one and two switches, then
b=N1+2N2. These groups have no face in common. The total loss compared
with bounding every face independently is greater than

    [(19/500)N1+(97/1000)N2]U^2 >= (19/500)b U^2.

There is no double subtraction; the two-edge estimate concerns an entire
three-face group.

## 6. The finite exact contradiction

Combining the signed area bound, concavity, and shared-face loss gives

    pi < (50-b)(3 sqrt(3)/4)U^2 + (b/2)U^2
           + b G_U(pi/b) - (19/500)b U^2,
                  14<=b<=26.

The strict sign can safely be weakened to <=. The primary rational checker
proves that the right side is <314159/100000<pi for every one of these
thirteen integer values, with U=228421/1000000. It encloses pi using
Machin's identity, sin and cos by alternating Taylor series, and positive
square roots by integer square root bounds. The independent implementation
uses different, shorter Taylor enclosures and a coarser rational sqrt(3)
bound. All thirteen positive gaps are recorded by the independent checker.
Floating-point displays are not used in either program's acceptance.

Thus the original r0-cover cannot exist. Projecting any centers into D
cannot increase any distance to a point of D. The covering-radius function
is continuous on compact D^26, so its minimum is attained. Exclusion of
radius r0 therefore proves the strict bound r_D(26)>11421/50000.

## Remaining scope

This proof excludes radius 9/40 as a consequence of the stronger global
bound; the old two actual-boundary-count cases are no longer needed for
that radius. It does not settle the candidate radius near 0.2347000904.
It does not pay any original 16-root, 4957-prefix or 344-domain obligation,
establish completeness of the original catalogue, or restore missing native
inputs. The known upper construction is credited to MinMax Arena's source
and is reproduced in the earlier supplement. The next target is a stronger
bound using boundary positions together with shared internal faces.
