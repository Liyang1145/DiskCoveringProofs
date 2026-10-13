# From a strict cover to an embedded center disk, including corner shadows

This supplies the missing written geometric bridge for the closed-ear rule.
It is not the final unrestricted current/source joint acceptance, a complete
catalogue, or a proof-assistant formalization. Existing frozen flags and
payments are unchanged. The companion program checks universal polynomial
identities and scope controls, not the entire continuous/topological theorem
by finite sampling.

## 1. Precise input and radius scope

Start with a cover at radius r strictly below the radius being excluded.
Choose r<rho below that same excluded radius and below U=234701/1000000.
The separately bound strict-slack/generic-position argument permits projection,
inward motion and finite generic perturbation without losing ANY point of D.
Remove redundant disks, leaving m<=26 distinct centers strictly inside D.
All seven listed general-position exclusions remain valid. The cover is
strict at radius rho: each nearest-center distance is uniformly below rho.

Use the already written irredundant clipped-Voronoi no-return argument.
Its conclusion is that each boundary-owning cell has one connected positive
unit-circle arc. B refers to these ORIGINAL owners, not every disk touching
the circle and not a new nearest-site diagram of 26 shadow labels.
The independently bound four-family count gives B in14,15,16,17 and
m-B>=9. No new external radius theorem is imported here.

The strict-competitor quantifier matters. Inflating a cover past the radius
scope of an earlier conditional lower certificate is NOT allowed. Degenerate
limiting configurations can be considered subsequently through the closed
necessary inequalities; an inflated radius is never relabeled as the original.

## 2. The clipped cell decomposition and its abstract simple disk dual

Let C_i be the full nearest-site Voronoi cell intersected with D. It is convex,
contains its distinct center in its interior, and is contained in the closed
rho-disk of that center. A shared interface of two cells is a connected
interval on their bisector; it cannot give two distinct dual edges.

General position makes each interior diagram vertex an intersection of exactly
three cells. Each unit-circle transition has exactly two interior cells and
the outside cell. There are no tangencies or triple ties on the circle.
Add the outside of D as one cell on the sphere. No-return makes its interface
with every boundary owner one connected arc, so the dual has no parallel edge
to the outside vertex. Distinct positive-area cells cannot create a self-loop.

For completeness, a clipped internal interface with BOTH endpoints on the
circle would make the same pair consecutive twice in the boundary-owner word.
Each owner appears once; for B>=3 this is impossible. Our B>=14 scope excludes
the exceptional two-owner situation. Thus each boundary dual edge has one
incident interior triangle; every other dual edge has two.

The dual can be drawn without crossings by connecting each center to an
interior point of each shared cell side, inside its own convex cell. Choose
the side points generically so spokes only meet at their own centers.
Interior diagram vertices give triangular dual faces. Each internal cell's
link is a circle; each boundary cell's link, after deleting the outside
vertex and its open star, is a path. The boundary is the simple B-owner cycle.
This is the dual of a regular disk cell decomposition, hence a connected
triangulated disk, not merely an Euler-number guess.

Its counts are V=m, E=3m-B-3, F=2m-B-2. Equivalently they follow from disk
Euler V-E+F=1 and 3F=2E-B. This paragraph is a topological argument about the
actual convex-cell decomposition; code checking these counts alone is not
claimed to prove it.

## 3. Why the same dual embeds with straight actual-center edges

At any relative-interior point q of a shared clipped side for centers a,b,
the circle centered at q through a,b contains every other center strictly
outside. This is immediate from the nearest-site definition at a side point
away from all diagram vertices.

Here is a self-contained noncrossing argument. Suppose two center edges ab
and cd properly cross at
p=(1-t)a+t b=(1-s)c+s d, with0<t,s<1. Put

A=t(1-t)|a-b|^2, C=s(1-s)|c-d|^2.

For an empty circle of edge ab, write f(x)=|x|^2-2q.x+k, so
f(a)=f(b)=0 and f(c),f(d)>0. The exact interpolation identity gives

(1-s)f(c)+s f(d)=C-A,

because both affine interpolants meet at p. Hence C>A. Repeating with the
strictly empty circle of cd gives A>C, contradiction. No assertion about
arbitrary intersecting rods is used. The symbolic program verifies the
interpolation/weighted-circle identities universally, not at sample edges.
Coincident centers and three-collinear centers were excluded before this step.

The rotation system also agrees. An internal side of C_i has outward normal
c_j-c_i, since its half-plane is
2(c_j-c_i).x <= |c_j|^2-|c_i|^2.
Around a convex cell containing c_i, its visible sides and their outward
normals have the same cyclic order. Its center-to-side spokes therefore have
the same neighbor order as the straight center edges c_i c_j.
For a boundary cell, the single circle arc supplies the one exterior gap;
the remaining neighbor list is the same path, not a different cyclic cut.

The straight noncrossing drawing has the same rotation system as the disk
dual. Its bounded faces are exactly the stated center triangles; its outer
boundary is the same simple owner cycle. Every nonowner center is an interior
vertex of that drawing. In particular a closed subdisk whose boundary is a
three-cycle fills that geometric triangle, so every vertex in it lies in
the convex hull of its three boundary centers. A finite compact planar patch
cannot instead fill the unbounded exterior of that Jordan triangle.

## 4. Anchors and common face witnesses

At a circle transition between owners i and i+1, the circle point A_i is in
both original disks, giving the two boundary rods of length<rho.
At an interior Voronoi vertex v, the three tied centers have distance<rho
from v. This v is the common face witness and belongs to D.
It need NOT belong to the center triangle: no acute-triangle or circumcenter-
inside-triangle assumption is made. The witness is used for rod inequalities,
not as the position of an abstract new center.

## 5. Padding m<26: retain the historical CORNER-COPY model

Choose any center face(a,b,c), add a NEW ABSTRACT label s, and replace it by
faces(a,b,s),(b,c,s),(c,a,s). Retain every original edge and set the limiting
geometric position c_s=c_a. Reuse the old common witness v in all three new
faces. It remains within rho of every incident center, including the copy.
The original physical disks and their coverage are unchanged. The new label
is a shadow, not a claim of a new positive-area nearest-center cell.

Repeat until exactly26 abstract labels are present. Boundary labels/anchors
are unchanged. Assign each original clipped cell to its original label and
assign zero cell area to each shadow. The new labels are interior ABSTRACT
vertices even when their limiting positions coincide with a boundary center.
This is the historical duplicate/zero-area interface; do NOT silently claim
26 distinct original Voronoi cells.

The star graph nevertheless has a genuine EMBEDDED-LIMIT realization.
For0<epsilon<1/2 replace each copied corner insertion by

c_s(epsilon)=(1-2epsilon)c_a(epsilon)
              +epsilon c_b(epsilon)+epsilon c_c(epsilon),

performing the finitely many insertions in their original order, with original
physical centers fixed. Every insertion is strictly inside its current
nondegenerate triangle. The three child triangle orientations are
epsilon,1-2epsilon,epsilon times its positive orientation. Thus the entire
26-label disk is a noncrossing straight triangulation for everyepsilon>0.
Every position stays in D by convexity, and the configurations converge
recursively to the prescribed corner-copy positions as epsilon tends to zero.

All face-witness inequalities can even be retained along this family:
if v is within rho of three corners, it is within rho of their convex
combination. The exact variance identity proves this. Reusing the common
parent witness at every insertion is therefore safe; no new circumcircle
or new Voronoi-diagram assertion is made.

Each closed ear patch of the abstract 26-label disk consequently has its
vertices inside its boundary triangle at everyepsilon>0 and also at the
corner-copy limit. This is the geometric inclusion needed by the new ear
rule; an arbitrary weak rod realization does not acquire this property.

## 6. Degree-area interface: vertex budgets, not fictional new cells

Each insertion keeps old edges and adds one neighbor to each old corner.
An old label's degree can only increase. An original interior clipped cell
has a polygon with at most its ORIGINAL degree many vertices. A boundary
cell has its circle arc plus a polygon with at most ORIGINAL degree+1
vertices, including the two fixed transition anchors.

The geometric polygon-capacity lemmas must be stated for AT MOST this many
vertices, allowing repeated vertices or zero sides. Raising the budget to
the starred degree is a relaxation: pad the original polygon by repeated
vertices. The same anchored capacity lemma then applies at the larger budget.
No comparison between rounded coefficient-table entries is used as a proof
of this set inclusion. Interior capacity is nonnegative for every degree>=3,
so each shadow's zero cell area safely satisfies its own interior bound.
The original cell areas still sum to area(D), and the original boundary arcs
still sum to one full turn.

This explains how a degree-area argument can be compatible with shadows.
It does NOT by itself reprove every frozen area formula/table/partial-state
payment or certify that all those implementations use exactly this at-most-
vertex-budget statement. Their actual source/semantic interface must still
be checked before a full unrestricted joint acceptance.

## 7. Transfer to the closed-ear contradiction and exact remaining budget

Every original nonowner disk occurs as a distinct original label>=B in the
padded disk. A shadow may copy any old center but never deletes an original
label. The original B owners miss the open core radius1-2U, so the ORIGINAL
nonowners cover its closed core. Shadow copies may be included in the union
without weakening that statement.

If a closed ear contains every introduced label>=B, convex-hull inclusion
places all introduced ORIGINAL nonowner centers in the forbidden half-plane.
The four separated core points in the ear proof then require four distinct
ORIGINAL nonowner disks outside the ear. Each has a different retained
original label, and all those labels must be unintroduced. If26-next<=3,
there are at most three such labels, contradiction. Counting shadows as
potential remaining labels only enlarges this upper bound, so it is safe.

Thus the written embedded/limit premise of the 643 actual ear tests is
geometrically justified for the generic-cover/corner-starred reduction.
This is a continuous mathematical argument with an explicit radius and
label scope. It is not inferred from the 643 finite checks or their hashes.
The actual current28 source receipt, all older exclusion interfaces and a
distinct geometry/current/final supplemental admission remain required before
formal frontier removal. Global lower bound/optimality remain UNPROVED.
