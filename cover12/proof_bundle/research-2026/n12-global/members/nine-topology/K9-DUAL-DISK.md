# n12 / k9 branch: from an arbitrary cover to an abstract triangulated dual disk

Companion to `K9-TYPE-LIST.md` (finite type list) and `INTERFACE.md`.
Level: analytic proof of the dual-disk reduction, conditional only on inputs (I1)-(I5) of `K9-TYPE-LIST.md`
§0 and the k=9 branch hypothesis (12 congruent radius-r disks cover D, exactly nine boundary-active, r <= U).
Independent re-derivation; no n11 classification or constants. Not proved and not claimed: any metric exclusion,
any lower bound for r_D(12), anything about k=10/11, any enumeration of untriangulated degenerate faces.

## 1. Cells, spokes, switches

D = closed unit disk. After (I1) and merging coincident hub centers, the distinct sites are nine ring sites
`c_1..c_9` with `1-r <= |c_i| <= sqrt(1-r^2)` and `m <= 3` hub sites with `|h| < 1-r`; all sites are points of
int D. Coincident *ring* centers are impossible in this branch, because two of the nine boundary-active disks
would then have the same actual arc, so the nine arcs could not be essential / cover S^1. No hub is assumed
non-removable: `m` is simply the number of distinct non-boundary site positions after merging (a redundant hub
still has a nonempty cell, so it still contributes a dual vertex). Clipped cells
`V_s = {x in D : |x-s| <= |x-t| for all sites t}`.

Lemma 1.1. `V_s subset B(s,r)`; each `V_s` is closed convex with `s in int V_s`; interiors tile int D; the
facet-adjacency graph (edges = positive-length common facets) is connected; non-adjacent ring cells are disjoint.
Proof: coverage (I5) and minimality give `|x-s| <= r`; convexity is standard; `|s-s| = 0 < |s-t|` for all other
sites gives interior. The primal vertex set is finite. Join interior points of two cells by a polygonal path in
int D avoiding that finite set (possible, as a finite set does not disconnect int D); each time the path changes
cell it passes through a point lying in exactly two cells, i.e. through the relative interior of a positive-length
facet. Hence the facet-adjacency graph — not merely the point-intersection graph — is connected. Two rings with
label distance `>= 2`: `V_{c_i} cap V_{c_j} subset B(c_i,r) cap B(c_j,r) = emptyset` by (I4). QED

Lemma 1.2 (hubs are interior, core). For `u in S^1`: `|u-h| >= 1-|h| > r` while some site is within r of u, so
`u notin V_h`; convexity gives `V_h subset int D`, and `V_h subset B(h,r)`. The open core `B(0,1-2r)` (nonempty,
as `r <= U < 1/2`) contains no point of any ring disk (`|x-c_i| >= |c_i|-|x| > (1-r)-(1-2r) = r`), hence is
covered by hub cells; so `m >= 1`. QED

Lemma 1.3 (switches). The boundary vertices of the cellulation are exactly the nine switches `w_i`; each has
exactly three incident cellulation edges (the two boundary arcs and one interior edge, the **spoke** `s_i`
shared by `V_{c_i}, V_{c_{i+1}}`), and the spoke has positive length.
Proof: at `u = w_i`, by (I2)/(I3) exactly `c_i,c_{i+1}` are nearest, with the same distance
`rho = |u-c_i| = |u-c_{i+1}| <= r`, while every other site `s` satisfies `|u-s| > r >= rho`; by finiteness the
gap is strict and uniform: `|u-s| - rho >= delta > 0`. The bisector `L` is secant,
`dist(0,L) = ||c_i|^2-|c_{i+1}|^2|/(2|c_i-c_{i+1}|) <= (|c_i|+|c_{i+1}|)/2 <= sqrt(1-r^2) < 1`, so `L cap D` is
a chord with `u` as one endpoint: exactly one of the two directions of `L` at `u` runs into int D. Let `w` be
that inward unit direction and `z(t) = u + t w`, `0 < t < t_0`, the corresponding segment in int D. For every
site `s` the map `z |-> |z-s|` is 1-Lipschitz, so the strict inequalities at `u` persist: for small `t > 0`,
`|z(t)-s| > |z(t)-c_i| = |z(t)-c_{i+1}|` for every `s != c_i,c_{i+1}` (the two are equal because `z(t) in L`).
Hence an interval of positive length of the bisector lies in `V_{c_i} cap V_{c_{i+1}}`: the spoke has positive
length. (No estimate of the distance to `r` is needed: `z(t) in D` and nearest-ness of `c_i,c_{i+1}` at `z(t)`
mean that their common distance is the minimum over sites, and coverage (I5) supplies some site at distance
`<= r`.) This covers both the case where the owned arcs overlap in positive length and the case where they meet
in the single point `u`. QED

Lemma 1.4 (the only ring-ring facets are the spokes; the only 2-ring faces are the spoke faces). If an interior
primal vertex `x` lies in `V_{c_i} cap V_{c_j}`, `i != j`, then `i,j` are adjacent labels, `x` is the inner
endpoint `x_i` of the spoke `s_i`, `V_{c_i}, V_{c_j}` are consecutive at `x`, and the face at `x` is the spoke
face containing the spoke edge (whose other side is the outer face).
Proof: `V_{c_i} cap V_{c_j}` is closed convex and lies on the bisector `L`; as a subset of the chord `L cap D`
it is an interval whose endpoint `w_i` is the switch (the endpoint of the chord). Its other endpoint `y` lies in
int D: the other S^1 point of `L` is outside both owned arcs by (I3), so it is outside `V_{c_i} cap V_{c_j}`.
Let `x in V_{c_i} cap V_{c_j}` be an interior primal vertex. Suppose `x != y`. Fix a third cell `V_t` incident
at `x` (there is one, as `x` is a vertex). The function `z |-> |z-t|^2 - |z-c_i|^2` restricted to the line `L`
is affine, vanishes at `x` (both `c_i` and `t` attain the minimal distance at `x`), and is not identically zero
(otherwise the bisectors of `{t,c_i}` and `{c_j,c_i}` would coincide, forcing `t = c_j`). Hence it is strictly
negative on one of the two sides of `x` in `L`: points of `L` on that side near `x` satisfy `|z-t| < |z-c_i|`,
so they are not in `V_{c_i}`. Therefore `V_{c_i} cap V_{c_j}` has no points of `L` on that side of `x`, so `x`
is an endpoint of `V_{c_i} cap V_{c_j}`; as `w_i` is the other endpoint and `x in int D`, `x = y`. At `y` the
bisector ray towards `w_i` (whose points just off `y` lie in `V_{c_i} cap V_{c_j}`) is a common boundary
direction of the two cells, and since they lie on opposite sides of `L`, their sectors are consecutive. The
spoke edge is that primal edge; its two incident dual faces are the outer face and the face at `y`. QED

Lemma 1.5 (ring incidence is small). At an interior primal vertex at most two ring cells meet and they are
adjacent labels; hence every interior primal vertex is incident to at least one hub, every face of the dual disk
contains at least one hub, and no face contains two rings unless it is a spoke face.
Proof: incident ring cells contain x, so their disks contain x (Lemma 1.1) and by (I4) their labels are
adjacent; pairwise adjacent labels in `C_9` number at most two. If no hub were incident, the vertex would have
at most two incident cells, i.e. not be a vertex. Lemma 1.4 identifies the 2-ring case. QED

## 2. The dual disk G

Definition: `G` has one node per cell, one edge per positive-length facet (two cells share at most one facet by
convexity). Draw nodes inside cells and edges through facet points; the drawing is planar. Standard duality:

* bounded faces of `G` `<->` interior primal vertices, each with boundary cycle = the incident cells in their
  cyclic order (each convex cell has exactly one sector at the vertex, so the cycle is simple);
* outer face = simple cycle `R_1...R_9` (dualise the cellulation compactified by the exterior face: the exterior
  vertex is adjacent to the nine ring cells in cyclic order, and deleting it merges the nine switch-faces, each a
  triangle `(R_i,R_{i+1},exterior)` by Lemma 1.3, into one face with boundary walk `R_1...R_9`).

Counting. With `E_RH`, `E_HH` the ring-hub and hub-hub facets, `v` the number of interior primal vertices:
`V(G) = 9+m`, `E(G) = 9+E_RH+E_HH`, and Euler gives `v = 1 + E_RH + E_HH - m`. There are exactly nine
2-ring faces (the spoke faces, Lemma 1.4) and every other face with a ring (a "1-ring face") has `>= 2` hubs
(a 1-ring 1-hub face would have only two vertices), so for `m <= 3` the 1-ring faces are exactly the
`n1 = n12+n13` ones. Counting ring-face incidences in two ways:
`sum over bounded faces of r(f) = 18 + n1` (nine spoke faces contribute 2 each) and
`sum over bounded faces of r(f) = sum over rings of (#inner faces at R_i) = sum_i (1 + d_i) = 9 + E_RH`
(`deg_G(R_i) = 2 + d_i` comprises the two spokes and the `d_i` hub facets, and a boundary vertex of a plane
graph is incident to `deg - 1` bounded faces). Hence `E_RH = 9 + n1` and, substituting into Euler,

    v = E_RH + n03 ,   E_HH = m - 1 + n03 >= m - 1 ,      (n03 = number of 0-ring faces)

which for `m <= 3` gives: `m=1`: `E_HH >= 0`; `m=2`: at least one hub edge; `m=3`: at least two hub edges.
(Moreover a 0-ring face needs `>= 3` hubs, so `n03 = 0` for `m <= 2` and `n03 <= 1` for `m = 3`.)

Corollary 2.1 (hub connectivity, m <= 3). The only simple graphs on 3 vertices with `>= 2` edges are `P_3` and
`K_3`; on 2 vertices `>= 1` edge is `K_2`. Hence `H in {K_1, K_2, P_3, K_3}`.
(Independent cross-check, all steps elementary: label every bounded face by the H-component of its hubs — the
hubs of a face are consecutive on its boundary cycle, hence pairwise joined by hub edges, so the label is well
defined; two bounded faces sharing an edge share the label, since a ring-ring edge is a spoke and always has the
outer face on one side, while ring-hub and hub-hub edges are incident with hubs; at each node of G all incident
faces share a label (around a hub node all faces contain that hub; around a ring node consecutive inner faces
share hub facets); the bounded faces tile the closed disk bounded by the outer cycle, and two label classes
could only meet at a node, where all incident faces are chained. So one class, H connected.)

## 3. Reduction to an abstract triangulated disk (covers all degeneracies)

Theorem A. Let a k=9 cover be given. Then there is an abstract triangulated disk `T` with

    vertices 9 boundary rings R_1..R_9 (in arc-midpoint cyclic order) and m interior hubs,
    faces all triangles (F = 7+2m), edges 15+3m of which 9 are the boundary spokes,
    and a witness map: each triangle tau receives a point x_tau in D with |x_tau - s| <= r for all three
    site-vertices s of tau.

Construction: start from `G` of §2. Every bounded face `f` is a convex polygon whose vertices are the cells
incident to its primal vertex `x_f`, and every such cell satisfies `|x_f - s| <= r` (Lemma 1.1). Choose any
triangulation of `f` (e.g. a fan from one vertex) and declare `x_f` the witness of every triangle created inside
`f`; real triangular faces keep their own primal witness. No new vertex is created, so the result is a
triangulated disk with the same boundary cycle. Euler with all faces triangles: `3F + 9 = 2(9+m+F-1)` gives
`F = 7+2m`, `E = 15+3m`. QED

Theorem B (no ring chords; hubs in every triangle). In `T`, the only ring-ring edge is a boundary spoke, no
triangle has three ring vertices, and every triangle has at least one hub.
Proof: every edge of `T` is a facet of the cellulation or an artificial diagonal inside a face; in both cases it
is contained in a triangle whose witness satisfies `|x-s| <= r` at both endpoint sites. If both endpoints were
rings, the two radius-r disks would intersect at x; by (I4) the labels are adjacent, and by Lemma 1.4 the pair's
only facet is its spoke, which already is an edge, so no artificial diagonal can join them. A triangle with
three rings would have the three disks pairwise intersecting at its witness, contradicting (I4); a triangle with
two rings has them adjacent, and then by Lemma 1.4 it is the spoke face of that spoke. QED

Corollary C (rigid shape of `T`). The nine boundary spokes each lie in exactly one triangle (their outer
triangle), these nine are distinct and of type (2 rings + 1 hub), and the remaining `F-9 = 2m-2` triangles are
(1 ring + 2 hubs) or (0 rings + 3 hubs) — for `m=1` there are none, for `m=2` two, for `m=3` four. Each
interior edge lies in exactly two triangles; `deg_T(R_i) = t_i + 2` where `t_i` = number of hub neighbours of
`R_i`, and the hub neighbours in cyclic order form a simple path `q_i` in `H` from the hub of the outer triangle
of spoke `i-1` to that of spoke `i`.

## 4. Classification (proof of the list)

Let `l_i` be the hub of the outer triangle of spoke `i`. Reading the chains `q_1,...,q_9` in order gives a
closed walk in `H` (it starts at `l_0` and ends at `l_9 = l_0`); it traverses a hub edge once for every inner
(1-ring) triangle containing that edge. Each hub edge lies in exactly two triangles of `T`; both are inner
triangles of type (1 ring + 2 hubs), except that in the `K_3` case one of the two may be the (0-ring) triangle
`A B C` (which contains all three hub edges). Since `t_i <= 3`, each `q_i` has at most 2 steps, and the possible
step data are:

* `H = P_3 = L-M-L'`: `sum_i (t_i-1) = 4`, so the multiset of step counts is `{1,1,1,1}` (P4), `{2,1,1}` (P3)
  or `{2,2}` (P2); the runs of equal labels are the blocks listed in `K9-TYPE-LIST.md` §2;
* `H = K_3`: the `(0,3)` triangle exists and consumes 3 edge incidences, so `sum_i (t_i-1) = 3`: step counts
  `{1,1,1}` (T3) or `{2,1}` (T2);
* `H = K_2`: `sum_i (t_i-1) = 2 = 2` edge incidences from two (1-ring) triangles: two transitions (M2);
* `H = K_1`: no inner triangle: wheel W_9 (M1).
Each chain is a simple path in `H`, so a 2-step chain uses the two different edges of `H` and visits all three
hubs; in `K_3` a 2-step chain is `A-C-B`-type and the third edge is consumed by the remaining 1-step chain.
This yields exactly the families of `K9-TYPE-LIST.md` §2 and proves that no further combinatorial type exists.
QED

## 5. Degeneracies (untriangulated dual; handled, not excluded)

(a) *Cocircularity / higher-order vertices.* Bounded faces may be polygons with `k >= 4` vertices (k cells
meeting at one primal vertex). They are triangulated in Theorem A; the witness copy makes every artificial
triangle satisfy "all its site-vertices within r of a common point of D", so all downstream statements that need
locality (no ring chords, hub connectivity, degree/face counts) hold on `T`. Artificial diagonals have **zero
primal edge length** but non-zero site distance; they are never treated as cell adjacencies of `G`.
(b) *Collinear sites.* For distinct sites the bisectors of `{a,b}` and `{b,c}` are distinct parallel lines when
a,b,c are collinear, and two different pairs may even have coincident bisectors; this is harmless: a pair's
common facet is `V_a cap V_b`, convex and inside one line, hence one interval (or a point = no edge). At a
primal vertex no three incident sites are collinear (a line meets the circle of radius rho around x in at most
two points), so every face of the straight drawing is a non-degenerate convex polygon.
(c) *Boundary degeneracies.* Singleton arc overlap handled in Lemma 1.3; tangential ring disks are allowed by
(I1); no triple tie on S^1 by (I2); hubs stay at distance `> r` from S^1 (Lemma 1.2), so no hub touches the outer
structure; the secant bisector (Lemma 1.3) makes every switch a degree-3 boundary vertex with exactly one
interior edge; `r <= U < 1/2` keeps the core nonempty.
(d) *Zero-length primal edges* are not edges of `G` but their pairs still occur together in a face's vertex set,
i.e. in artificial diagonals as in (a).

## 6. Straight-site realization (confirmed)

Lift `s |-> s^ = (s,|s|^2)` in R^3 and set `pi_s(y) = 2y.s - |s|^2`; then `|y-s| <= |y-t| <=> pi_s(y) >=
pi_t(y)`, so the nearest-site diagram is dual to the lower convex hull of the lifted points. If `x` is an
interior primal vertex with `rho = |x-c| <= r`, all incident sites are at distance exactly `rho` from `x` and all
other sites strictly farther; hence the lifted points of the incident sites are the vertices of a face of the
lower hull, lying in the plane `z = 2y.x - (|x|^2-rho^2)`, and that plane is a graph over R^2, so the face
**projects injectively** (affinely, not isometrically; lengths are scaled by the plane's slope) onto the convex
polygon `conv(incident sites)` in the cyclic order of cells. The projected lower-hull faces have pairwise
disjoint interiors and their union is `conv(sites)`, the projection of the convex hull of the lifted points —
**not** all of R^2 (a vertical line over a point outside `conv(sites)` misses that hull). Therefore
nodes-at-sites with straight edges for the facet-sharing pairs gives a non-crossing straight drawing realizing
the incidence of all bounded faces of `G` (= the Delaunay cells whose Voronoi vertex lies in int D); an
artificial triangulation of a face is realized inside its convex polygon, without crossings, and faces with
`>= 4` cells are strictly convex polygons (no three sites collinear, §5(b)). Finally, `|c_i| >= 1-r` and the arcs cover S^1 give `u.c_i >= 1-r` for every unit
direction (some arc covers u), hence `B(0,1-r) subset conv{c_1..c_9}`; as `|h| < 1-r`, every hub site lies
strictly inside `conv(ring sites)`. The nine straight spoke-dual edges `c_i c_{i+1}` are Delaunay edges (their
cells share the spoke) and do not cross, so they form a simple closed polygonal curve.

## 7. Scope ledger

Proved (conditional on (I1)-(I5) + k=9 branch):
1. Lemmas 1.1-1.5 (honest cells, interior hubs, degree-3 switches with positive spokes, ring-ring facets are the
   9 spokes, `<= 2` rings and `>= 1` hub per primal vertex);
2. Theorem A: every such cover yields an abstract triangulated disk with witness copy, `F = 7+2m`,
   `E = 15+3m`, 9 spokes;
3. Theorem B / Corollary C: no ring chord, every triangle has a hub, rigid shape;
4. §4: the classification is exactly the families of `K9-TYPE-LIST.md` §2 (m=3: P4, P3, P2, T3, T2; m=2: M2;
   m=1: M1), with `H` connected and `H in {K_1,K_2,P_3,K_3}`;
5. §6: straight-site realization exists.

Missing: no metric exclusion of any family; no lower bound for r_D(12); k=10/11 untouched; no claim that the
original candidate's switches are preserved by (I1).
