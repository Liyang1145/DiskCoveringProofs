# Ear decomposition once the hubs are adjacent

Status: analytic combinatorial argument; geometric dual-interface check pending. Input is a triangulated topological disk with boundary cycle (0,...,8), exactly two interior vertices h1,h2 joined by an edge, and no edge between ring vertices at cyclic distance >=3. Every ring-only triangular face is a consecutive triple, as follows directly from the permitted edges.

## Pure combinatorial lemma

Every ring chord (i,i+2) cuts off the boundary triangle with ring vertices i,i+1,i+2 on its short side, and this short side contains neither hub. Indeed the hub edge keeps both hubs on the same side of the chord. If both were on the short side, the long side would be an eight-gon with no interior vertices, triangulated using only ring edges. Every triangular face in that eight-gon would have to be a consecutive original triple. Such a triangle has at least two ORIGINAL nine-cycle boundary edges. These original boundary edges are never shared by two faces. The eight-gon has only seven original boundary edges (the eighth edge is the new chord), yet any triangulation has six faces and would need at least twelve such edges. Contradiction. Hence the long side contains the hubs and the short side is one empty triangular face.

It follows that every ring chord cuts an empty ear. Its skipped middle vertex has degree two and no hub neighbor. Two such ears cannot have adjacent skipped vertices: the respective chords would cross. Thus the skipped set is an independent subset of C9; its size q is at most four. Ears may share a corner vertex, not a whole original boundary edge. Removing them yields a (9-q)-sided core with two adjacent interior hubs and no ring-ring diagonals; every face of the core involves at least one hub.

In this core exactly two faces contain both hubs (the two sides of their edge). Write u,v for their distinct ring vertices. The two paths u..v along the core boundary are triangulated by fans from h1 and h2 respectively. Thus, after choosing the independent skipped set and the two transition ring vertices, the entire triangulation is fixed (up to swapping hub labels). Each hub has at least two ring neighbors and its hub-hub neighbor; either path can consist of just a single ring edge, giving one hub degree three. No claim of angle symmetry is made.

Counts for the refined triangulation: q in {0,1,2,3,4}, K=k1+k2=13-q, so K>=9. Ring-ring edges are 9+q, hub-ring edges 11-q, hub-hub edge one. These extend the earlier formal equations only after the adjacency and locality premises have been established.

## Geometric interface still requiring explicit proof

For a trivalent clipped Voronoi cellulation of the inward-root 9+2 covering representative, the assumed topological triangulation is exactly its dual. In a degenerate cellulation, triangulate each higher-order dual face without deleting the actual hub-hub edge. The sites of each such face have a common nearest point x in D with common distance <=r; therefore every added ring-ring edge obeys the same locality restriction. Added edges represent zero-length primal edges, so their combinatorial degrees cannot silently be inserted into strict positive-edge estimates. The existence of a globally embedded simple refinement and the preservation of the boundary cycle must be checked before treating the q<=4 fan classification as an unconditional geometric reduction.

Payoff: finite cyclic choices instead of arbitrary planar topology, valid with arbitrary arc overlaps if the geometric interface is completed. Does not establish any sharp radius bound, remove q>0, or reduce metric parameters to a symmetric family.
