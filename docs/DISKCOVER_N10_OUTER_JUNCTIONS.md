<!-- SPDX-License-Identifier: MIT -->
# Native geometry for the n=10 outer-junction exclusion

This note reconstructs the geometric inputs to the two area tests in
[Fejes Tóth, §3](https://library.slmath.org/books/Book52/files/18fejes.pdf).
It does not replay the eight-owner exclusion or the directed numerical
inequalities. Use the paper's target radius $R=1+2\cos(2\pi/9)$ and
unit covering disks. For the global lower bound it suffices to refute
covers at (R) that have a strict distance margin below 1.

## Normalization and the dual

An outer center at radial distance $d>\sqrt{R^2-1}$ can be moved
radially to $d'=(R^2-1)/d$. In coordinates along its ray, for
$x\le(d+d')/2$ this only reduces distances. At a point of the target
disk with $x>(d+d')/2$, the new squared distance is bounded by
$R^2-2d'x+d'^2<1$. Consequently a finite cover with a strict margin
continues to have a strict margin, by compactness. A disk disjoint from
the target can instead be moved into the interior arbitrarily.
Perturb the centers slightly and generically with all norms strictly
below the radial threshold, keeping the strict cover. Centers are then
distinct and strictly in the target. The perturbation can avoid
four-way Voronoi vertices, any Voronoi vertex on the circle, or an edge
tangent to the circle. The disk covering the origin cannot reach the
target boundary because (R>2). In the branch here, the already
established exclusion of an eight-disk boundary cover means the other
nine sites each own positive-length portions.

A unit disk cuts one short covering arc on the target circle. The
part owned by its nearest-center cell is connected: if a competitor
were strictly nearer between two owned points in that arc, the two
bisector crossings would both lie in the unit disk. Their distance
would be at most 2, contradicting the bisector chord's length, which
exceeds 2 because both sites are strictly inside the radial threshold.
The same chord observation shows that each switch starts a Voronoi
edge that reaches an interior triple vertex rather than another
boundary point.

For the planar dual, no claim that the outer sites are vertices of
the Euclidean convex hull is needed. The clipped cells are convex
topological disks. Place a dual vertex at each site. Across each
interior Voronoi edge join the two sites by two straight segments
through an interior point of the edge. These spokes in each cell are
disjoint away from the site. At every three-way interior Voronoi
vertex the dual has a triangular face: its six spokes bound three
cell wedges around that vertex. Along the boundary, the sectors in
each owner cell between the spokes to its two switch edges are a
single exterior collar, because each owner has one boundary arc and
the switches occur in a simple cycle. They form the exterior face,
whose inner boundary is the dual cycle of the nine owners, in cyclic
order. This is a triangulated topological disk with the origin-owning
site as its only interior vertex, regardless of the convex hull
of the coordinates of the dual vertices.

## Why the two cases exhaust the outer junctions

Write $\theta=\arcsin(1/R)$ and $\psi=\arcsin(2/R)$. Sites
that both cover a common point have separation at most 2, so two
boundary endpoints assigned to those sites have distance at most 4.
For a span of at most five owner arcs the angle is at most
$10\theta<2\pi-2\psi$, so an endpoint distance at most 4 forces
the span to have angle at most $2\psi$, the minor-arc bound.
This excludes an edge between sites separated by three or four
slots around the cycle, since then the rest of the circle has at
most five owner arcs and $2\psi+10\theta<2\pi$. Thus every
outer triangular face is three consecutive sites. Two disjoint
outer triangles are impossible, because their two spans and the
remaining three arcs cover at most $4\psi+6\theta<2\pi$.
Two consecutive triples shifted one slot are also impossible:
their two end-to-end edge chords interleave, so must cross in a
topological disk. It follows that there is at most one consecutive
triple, or exactly two that share an endpoint, represented as
(123) and (345) up to rotation or reflection.

Every nonboundary outer edge cuts off a short side of three boundary
sites. The interior dual vertex is not on that side: otherwise the
long side is an outer-only octagon, requiring six all-outer triangular
faces, already ruled out. Hence every nonboundary outer edge cuts off
an ear with no interior vertex; the middle owner of the ear has no
central contact. After deleting the ear middle sites, the remaining
triangulation is a star about the interior site, since it has no
remaining outer diagonals. One or two ears therefore leave eight or
seven sides on the interior clipped cell, respectively.

## Area decomposition without the figure

Cone every clipped Voronoi cell to its site. This partitions each
convex cell into fan triangles for its straight edges and one curved
fan for its boundary arc, if present. Junctions and switch points
have distance at most 1 from every incident site.

For each side of the interior cell, the triangle with apex its site
is congruent by reflection in the side to the fan triangle across
that side, because the side is on the two-site bisector. Hence these
pieces contribute twice the interior area, at most
$k\sin(2\pi/k)$ for (k=8,7): the (k) triangles about its
interior site have both radial lengths at most 1, and their vertex
angles in $[0,\pi]$ sum to $2\pi$.

Each ordinary boundary switch edge contributes the two triangles
coned to the two adjacent sites, of area at most $1/2$ each.
There are (9-2e) such edges, where (e=1,2) is the ear count.
At an ear of middle site (i), let (p) be the outer triple vertex
and (q_i,q_{i+1}) its two exterior switches. Sum the entire middle
cell with the fan triangles $[q_i,p,o_{i-1}]$ and
$[p,q_{i+1},o_{i+1}]$ of the two neighboring sites. Cancelling
oriented boundary segments gives the polygon with boundary vertices
(q_i,o_{i-1},p,o_{i+1},q_{i+1}), plus the target circular segment
between the switches. The four consecutive side lengths are at most
1, and the closing chord is at most 2 because the two switches lie
in the middle owner's disk. This signed-area identity holds
independently of convexity of the pentagon. The remaining pieces
are the (9-e) curved fans of nonmiddle owners. Thus these are
exhaustive area decompositions directly from the cell fans.

## The pentagon bound

Take a cyclic reference pentagon with side lengths (1,1,1,1,2)
and all central angles $a_j$ in $(0,\pi)$. Its radius (T>1)
uniquely satisfies $4\arcsin(1/(2T))+\arcsin(1/T)=\pi$,
because the left hand side strictly decreases to 0 and exceeds
$\pi$ at 1.

For any oriented pentagon with respective side bounds as above,
replace each edge of actual length $\ell_j$ by a minor circular
arc bulging to the right, prescribing its central angle $a_j$
and its radius $\rho_j=\ell_j/(2\sin(a_j/2))$. Traverse each on
time interval $a_j$, at speed $\rho_j$; a zero edge contributes
a constant path. The added signed area over the straight edge is
$\rho_j^2(a_j-\sin a_j)/2$. The result is a closed piecewise
smooth curve of period $2\pi$. Translate its mean to zero.
Cauchy–Schwarz and the periodic Wirtinger inequality bound its
signed area by half its kinetic energy integral
$\tfrac12\int|\gamma'|^2=\sum_j\rho_j^2 a_j/2$.
Subtract the arc additions. The original signed area is at most
$\tfrac12\sum_j\rho_j^2\sin a_j\le\tfrac12 T^2\sum_j\sin a_j$,
the claimed cyclic reference area. This proof does not assume
that area for fixed side lengths increases with every side.

## Bounding the remaining curved fans

For a remaining fan, write $y$ for its target-centered arc angle,
$s=R\sin(y/2)$ for half the chord, and $z=\sqrt{1-s^2}$. Its site
is within 1 of both endpoints, so its distance from the chord is at
most $z$ (average the squared distances to the endpoints). Its area
is therefore at most the cap plus a triangle of area $sz$:
$$K(y)=R^2(y-\sin y)/2+sz.$$

Write $A=\sqrt{R^2-s^2}$. On the interior,
$K'=s^2+(1-2s^2)A/(2z)$, whose derivative in $s$ is
$$s\left(2-2A/z+\frac{(1-2s^2)(R^2-1)}{2Az^3}\right).$$
If $s^2\ge1/2$, the last term is nonpositive; otherwise use
$1-2s^2\le z^2$ and $R^2-1\le A^2$ to bound the bracket above by
$2-3A/(2z)<0$, since $A/z\ge R>2$. Thus $K$ is concave in $y$
including the endpoints, by continuity.

With $e$ ears, the $m=9-e$ remaining angles sum to at least
$2\pi-2e\theta$. Let $y_0=(2\pi-2e\theta)/m$. To check that
$K$ is decreasing from $y_0$ on, set
$f_R(a)=2\arcsin(\sin(a/2)/R)$ and $F_R=K\circ f_R$.
The directed check establishes $F_R'(1.9)<0$ and
$R\sin(y_0/2)>\sin(.95)$, so $y_0>f_R(1.9)$ and
$K'(f_R(1.9))<0$. Concavity now gives the residual-area bound
$mK(y_0)$ by Jensen. This avoids any unproved relation between the
boundary endpoints and the actual angle at the site.

To compute the pentagon's area, let $x=\arcsin(1/(2T))$ and
$c=\cos x$. The closing equation gives
$\sin(4x)=2\sin x$, or $4c^3-2c-1=0$. Conversely, the isolated root
has $1/2<c^2<4/5$, so $\pi/8<x<\pi/4$ and the equation gives the
required closing relation on the minor arcs. The cyclic triangles
give the exact area $2\sqrt{T^2-1/4}+\sqrt{T^2-1}$, with
$T^2=1/(4(1-c^2))$.

Putting the fan pieces together gives the two bounds replayed by
[the interval checker](../tools/diskcover_n10_area.py). In target
units the total would be less than 20.142129866916335 with one ear,
or 19.927708248544316 with two ears. Both contradict the verified
target area above 20.142240018608209.

Two apparent printed arithmetical errors can be avoided by evaluating
the scope-correct formulas: the two-segment estimate is twice the
one-segment estimate (not the displayed primed decimal), and an
individual certified pentagon bound is simply counted twice in Case
2. Use 7, not the printed 8, in the Case 2 Jensen sum, and use
$2\pi-x$ for its residual total.
