# k9 branch: essential actual arcs and nearest-owned arc connectedness

Proof draft, scope: a radius-r cover of D with exactly nine boundary-active disks, 0<r≤U, after same-arc inner-root replacement. No D3 assumption. This does NOT address k10/11 or imply the candidate contact graph.

## Essential arcs and circular order
Let A_i=B(c_i,r)∩S1. Every arc has angular length≤2asin r<π/4 (since r≤U<sin(π/8)). Eight arcs cannot cover S1, so each of the nine is essential in the nine-arc boundary cover: A_i is not contained in the union of the other eight. In particular all nine arcs have positive length, are distinct and none contains another.

Their midpoints have a strict cyclic order. Indeed coincident midpoints would give nested arcs, contrary to essentiality. For nonnested short arcs, left endpoints and right endpoints have the same cyclic order as midpoints (choose a lift locally where the relevant arcs meet).

At most two arcs can meet at any point. If three arcs meet, unwrap around that point; because each has length<π/4, all three lie in an interval shorter thanπ/2. Sort their left endpoints. No nesting implies the same order of right endpoints. The middle interval is contained in the union of the first and third, since these overlap at the common point. It would be redundant in the full cover, a contradiction. The argument includes a common endpoint.

Furthermore only cyclic neighbors overlap. For a rigorous way to see this, traverse S1 and its essential exclusive pieces: each A_i has a nonempty relatively open piece uncovered by the others, because the others form a closed set and do not contain A_i. Any overlap can involve only two arcs by the preceding argument. Moving through the covered circle therefore encounters exclusive pieces in the same endpoint/midpoint order, with overlap transitions only between consecutive pieces. Nonneighbor overlap would pass an intervening endpoint/exclusive piece and cause either containment or a triple point. This final order step is stated explicitly here but should receive an independent combinatorial check before use in a global topology proof.

## A same-radius inner-root pair has at most one tie in any actual arc
All inner-root centers satisfy |c_i|≤s=sqrt(1-r²). For distinct c_i,c_j their midpoint m lies strictly inside B(0,s), by strict convexity. Their perpendicular bisector L passes through m, so dist(0,L)<s. Its two S1 intersections have smaller angular separation
2acos(dist(0,L))>2acos(s)=2asin r.
Consequently no arc of length≤2asin r contains both tie points. This is a strict statement even when either original disk used a double radial root. Duplicate centers are excluded here by essentiality, not by a generic-position assumption.

## Nearest ownership
Each A_i contains an exclusive open subarc where c_i is the unique nearest center among ALL12 disks: nonboundary disks have distance>r on S1, and other boundary disks have distance>r there, while c_i has distance≤r. Only immediate boundary neighbors can compete on the overlap intervals at the two ends of A_i. The squared-distance difference against either neighbor is continuous and has at most one zero anywhere in A_i by the previous paragraph. Thus it cannot cut a middle hole and return; starting from the exclusive piece, the set where i wins against the left neighbor extends to one endpoint/switch on the left, and similarly on the right. Hence the nearest-owned subset on S1 is one closed nonzero arc containing its exclusive piece, with one switch between each consecutive pair. Triple ties on S1 are excluded by no triple actual-arc overlap.

This yields exactly nine connected nearest-owned boundary arcs and nine two-site switches after the replacement. It does NOT yet prove an embedded triangulated Delaunay disk with exactly three interior vertices: some nonboundary sites may be duplicate/redundant, and their cells, interior edge topology and triangle realizability remain to be analyzed. Nor does nearest ownership preserve the old candidate's switch locations.
