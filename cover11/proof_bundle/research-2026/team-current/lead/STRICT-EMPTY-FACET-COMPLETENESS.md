# Eleven strict empty-circle faces suffice: lifted-hull completeness

## General planar lemma
Let S be n distinct planar sites, with h sites the vertices of a strictly convex hull and all remaining sites strictly interior. Suppose we exhibit N=2n-h-2 distinct noncollinear triples of S, each having a circumcircle strictly excluding every other site. Then these triples are exactly all Delaunay faces; in particular all finite Voronoi vertices are their circumcenters. No global 'no four cocircular' hypothesis is required.

Proof. Lift p to (p,|p|²) in R3. The plane through a noncollinear triple with circumcenter u and squared radius t is z=2u·p+(t−|u|²). Strict exclusion of every other site means every other lifted site is strictly above this plane. Consequently each exhibited triple is a distinct triangular lower convex-hull facet, not merely a sample triangle with a useful radius.
Every lifted site is an exposed lower vertex (the tangent plane z=2p0·p−|p0|² has equality only at p0, since its gap is |p−p0|²). Projected lower facets therefore form the Delaunay subdivision of the planar convex hull, using every site. Triangulate any nontriangular lower facets without introducing vertices. Every exhibited strict triangular facet remains a face. Euler and edge incidence give exactly 2n-h-2 triangular bounded faces for the completed subdivision. Already that many distinct triangular facets were exhibited, so no additional lower facet, triangular or otherwise, can remain. Delaunay/Voronoi duality identifies all finite Voronoi vertices. QED.

This is not counting arbitrary valid-looking faces: strict empty circles first prove they are facets of ONE convex polytope. Compatibility and coverage follow from convex-hull structure. It also allows cocircular quadruples whose circles are nonempty, such as reflected pairs at this candidate.

## Application to repaired TC root
n=11,h=9,N=11. Ring points form the strict convex hull by interval cross-product inequalities >.05; both hubs are strictly interior to every hull edge. The two hubs are distinct because y0−y1>.4 (read from the isolating box). All11 listed triples have determinant magnitude>.14. At the exact root, nine active circumcenters/radii follow analytically from res5 and reflection; the two slack ones follow by the rational circumcenter formula. Every listed circle has squared-distance exclusion margin>.15 for all other sites. These are direct interval assertions in lead/check_tc_root_geometry.py on the root box.

Hence all11 finite Voronoi vertices are accounted for WITHOUT needing a separate 330-quadruple determinant audit or numerical Delaunay selection. Independent r20-rigidity/r20_tc_delaunay_completeness.py provides an alternative straight-line embedding check, but is not a bearing dependency of this shorter inference.

Boundary arcs tile exactly via sum a=pi. All finite vertices lie inside D and have radius<=R, with nine radius exactlyR; the two slack radius²−R²<−.0008. A positive maximum of nearest-site distance in int D cannot lie inside a one-site Voronoi cell (strict convexity of squared distance) or in the relative interior of a two-site edge (strict convexity along the line); it must be a Voronoi vertex. Therefore the exact root configuration covers D at R, and the active interior vertices give covering radius EXACTLY R.

Conditional only on the existence of the exact isolated root and the displayed interval geometry. This proves an upper-cover object, not a lower bound for arbitrary11center configurations.
