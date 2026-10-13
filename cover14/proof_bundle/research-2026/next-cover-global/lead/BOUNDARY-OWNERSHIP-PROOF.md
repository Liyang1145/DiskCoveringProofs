# Connected boundary ownership: direct bisector argument

**Scope.** Any n14 cover at0<r≤U=.33173203427623414 with exactly10 actual boundary-active disks. Apply the count-independent same-arc inner-root replacement proved in n12 `lead/INNER-ROOT-REDUCTION.md` (input/output: D∩old disk⊆D∩new disk; same actual S1 arc), so each active center norm≤s=sqrt(1−r²)<1. Keep inactive centers unchanged. This note does not import n12 graph enumeration or stress bounds.

**Inputs.** Every actual active arc A_i is essential since nine radius-r disks cannot cover S1 (C1142 sine estimate). In particular each A_i has a private relatively open subinterval covered by no other disk. This follows because the other nine closed arcs have closed union, and any point outside that union has an open neighborhood still outside it; total coverage puts that neighborhood in A_i. Active centers are distinct; duplicate arcs would contradict essentiality. No-chord measure argument gives nonadjacent active disks disjoint, although the connectedness proof below only needs the norm bound and private interval.

## Pairwise bisector separation
For distinct active c_i,c_j, their equidistance line has distance

    d = ||c_j|²−|c_i|²| / (2|c_j−c_i|)
      ≤ (|c_i|+|c_j|)/2 ≤ s < 1.

Its two S1 intersections are separated by a smaller angular gap2acos(d)≥2acos(s)=2asin(r). Every actual arc A_i has length≤2asin(r). Consequently no two distinct bisector crossings can both lie in the relative interior of A_i; if two lie in A_i at all, they must be its two endpoints and its length must equal2asin(r).

The continuous distance-difference function g_ij(x)=|x−c_i|²−|x−c_j|² is affine in x. It vanishes at those two circle points and nowhere else. Parametrize A_i as a real closed interval. The subset where g_ij≤0 is therefore an interval, all of A_i, empty, or only its two endpoints (the last possibility requires both endpoint zeros and g_ij>0 inside). But a private interior point of A_i has |x−c_i|≤r<|x−c_j|, hence g_ij<0. It excludes both empty and two-endpoint alternatives. Thus each active competitor's non-strict nearest constraint cuts A_i to a single interval containing the private interval.

Inactive hubs have distance>r at every S1 point, so cannot beat c_i anywhere on A_i. Intersecting the finitely many intervals yields a nonempty connected closed interval J_i=A_i∩V_i on S1, with nonempty relative interior. Every boundary point is owned by at least one active site because the nearest distance≤r and all hubs have distance>r. Thus these ten J_i partition S1 into a circular sequence of nondegenerate arcs with disjoint interiors. The interior-disjoint assertion holds because any tie of two distinct sites is on a line and hence has at most two circle points. No argument equating a convex cell with its radial cone is used.

## Switches and positive inward facets
Any boundary switch is owned by at least two active sites. Three owners would contain a nonadjacent pair in the10-cycle, violating the disjoint-disk theorem, since all nearest distances≤r. Thus exactly two sites own a switch; the pair is adjacent in the actual-arc order. At the switch all other finitely many site distances are strictly greater. By continuity this strict margin persists in a neighborhood. Their bisector line crosses S1 transversely since d<1. Its inward segment therefore is a positive-length Voronoi facet owned exactly by the pair. There are exactly10 boundary switches.

## Remaining graph implication
The clipped cell complex is a disk cellulation with exactly10 nearest-owned boundary arcs and10 inward facets at their endpoints; the common-point condition excludes nonadjacent ring-cell intersections because each clipped cell lies inside its disk. Existence of a straight-line embedded Delaunay dual and triangulating its higher faces with copied witnesses is a separate standard geometric/topological step. This note does NOT infer Euler counts before that step. Merging duplicate hubs gives m∈{3,4}; C1142 core argument eliminates m≤2 even when k10 originally has four labelled hubs.
