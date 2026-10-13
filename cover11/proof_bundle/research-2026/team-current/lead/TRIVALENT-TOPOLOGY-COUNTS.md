# Conditional trivalent topology counts (not a WLOG assertion)

Assume the inward-root covering representative in VORONOI-BOUNDARY-REDUCTION.md has only trivalent interior Voronoi vertices and no zero-length edges. The dual is a triangulated topological disk with 9 boundary vertices (ring labels), 2 interior vertices (hub labels), 21 total edges and 11 triangular faces. The boundary 9-cycle follows actual boundary nearest-center order, not necessarily an independently presumed Euclidean convex-hull order.

Let d=1 if the two hub cells share an edge and d=0 otherwise. They can share at most one because convex cells meet in a convex segment. Let K=k1+k2 be the sum of hub-cell edge counts. Then:

- hub-hub edges = d;
- hub-ring edges = K-2d;
- ring-ring edges = 21-K+d;
- ring-only triangles (= ring-only trivalent Voronoi vertices) = q=11-K+2d;
- hub-ring-ring triangles = K-4d;
- hub-hub-ring triangles = 2d.

Proof: around each interior hub vertex its k_j incident triangles form a cycle. A hub-hub interior edge is incident to precisely two triangles, both containing both hubs. Therefore total faces containing at least one hub is K-2d, leaving q. Other counts follow from incidence and Euler. In particular 6<=K<=11+2d. Absence of ring-only triangles would force K=11+2d but does not itself force d=1: d=0 gives two triangulated hub fans glued along a ring-ring chord. Thus even eliminating triple-ring intersections would leave a hub-disconnected topology to exclude.

Structural use: a triple-ring exclusion would reduce trivalent topology to the q=0 cases. Current rigorous no-four-ring-common-point result does NOT imply q=0. Nontrivalent mixed hub/ring nodes need either separate analysis or a proved perturbation passage; none is asserted here.

Unconditional graph counts v<=11 and e<=21 remain as in the source lemma. This file is only a conditional combinatorial calculation and does not sharpen the covering-radius bound.
