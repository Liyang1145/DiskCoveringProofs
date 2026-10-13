# Removing cocircularity without perturbing a covering

Conditional on the geometric clipped Voronoi dual being a regular embedded disk with9-cycle boundary and hub interior vertices (the geometric interface is assigned to nine-topology), cocircularity does NOT require a generic-position assumption or a separate metric class.

For each bounded dual polygonal face P, its primal Voronoi vertex x lies inD and is equidistant to all sites on P; coverage implies this common distance≤r. Choose any combinatorial triangulation of P using only existing vertices. Give EVERY resulting triangle the SAME witness x. All vertex-to-witness constraints≤r are therefore valid, including for triangles sharing newly introduced artificial diagonals. No statement that the new triangulation is the actual positive-facet dual is made.

By C933, two nonneighbor ring sites cannot have any radius-r common witness inR². Thus a bounded dual polygon cannot contain such a pair in its vertex set. In particular, a new diagonal cannot be a nonneighbor ring-ring chord. The only possible ring-ring pair in a bounded face is a consecutive pair on the9-cycle, whose edge is already a boundary edge. Therefore all artificial diagonals have at least one hub endpoint, and every resulting triangle has a hub.

The filled abstract disk has the same9+m vertices, with all bounded faces triangular, so F=9+2m−2 and E_int=9+3m−3. Its hub subgraph is connected by the face-adjacency argument: every face has connected hub set; every shared inner edge has a hub; paths in the face adjacency graph connect these sets. Thus for m=3 it is P3 orK3, for m=2 an edge, for m=1 a singleton. Combinatorial fan classification may now be applied to this FILLED graph.

This is a direct exact implication to a weak witness network, not a limit or density argument. The relaxed network must permit equal witness positions, zero geometric lengths of artificial primal facets and all other degeneracies. It must NOT impose a positive area, strict circumcenter location, or unique geometric triangulation. Bounds proved for the complete closed network domain then cover the original degenerate configuration.

Caution: equations counting the ORIGINAL positive-facet dual need not be maximal. For example m=2 can have a4-cell cocircular vertex (a quadrilateral bounded face), and its actual F may be10 rather than11. This is not an exclusion; its polygon can be split using the same witness to obtain the11-face metric network. Do not claim trivalence of the original diagram from hub degree alone.
