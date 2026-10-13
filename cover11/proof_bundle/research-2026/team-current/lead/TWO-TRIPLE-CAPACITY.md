# Two disjoint triple clusters cannot occur; refined ear count improves to q<=2

Object: nine congruent radius-r disks cover S(0,1), 0<r<=19/50, with the essential cyclic arc ledger. Write A=asin(r), B=asin(2r). If a triple of disks has a common point p, all three actual boundary arcs are contained in J_p=S(0,1) intersect B(p,2r), of length <=2B. This uses the triangle inequality, independent of any Voronoi structure.

## Disjoint-label triples excluded

Suppose two triples have disjoint label sets, with common points p and q (not necessarily the same point). Their six actual arcs cover total circle length at most 4B; the three remaining arcs contribute at most 6A. Hence 2pi<=4B+6A, i.e. pi<=2B+3A. But at r<=.38, A<.4 and B<.9, so 2B+3A<3<pi. Contradiction. The strict easy bounds follow from sin(.4)>.38 and sin(.9)>.76 (alternating Taylor, e.g. x-x^3/6 lower bound gives .38933 and .7785 respectively).

This proof uses union measure, so overlaps between J_p and J_q only strengthen it. It applies to all closed triple intersections, not only ring-only Voronoi vertices, and needs no independent-hub input.

## Consequence for the refined ear classification

In any dual triangulation supplied by LOCALITY-TOPOLOGICAL-EARS.md / C801, each ear has labels {i-1,i,i+1}, where i belongs to an independent skipped subset S of C9. An artificial ear from subdividing a degenerate Voronoi face also has a true common point (the original higher-order Voronoi vertex), so the preceding capacity statement applies to it as well.

Two skipped labels i,j cannot be at cyclic distance 1 (independence), and cannot be at distance 3 or 4 (their triples would be disjoint). Therefore any two distinct skipped labels must be at cyclic distance exactly 2. There is no three-element subset of C9 whose pairwise cyclic distances are all 2: rotate first to 0; the other two would have to be 2 and 7, at cyclic distance 4 from each other. Thus |S|=q<=2. If q=2, the skipped labels are i and i+2, and their two ear triangles share the corner ring i+1.

Consequently the refined hub-degree sum K=13-q is at least 11. The q=3 and q=4 classes are globally excluded (conditional only on the established 9+2/locality/adjacency topological reduction, not on any metric symmetry). q=0, q=1, and the adjacent-shared-corner q=2 classes remain. This is not a sharp radius bound.

Next possible strengthening: for the q=2 case, union(J_p,J_q) half-measure <=2B-t_shared because both windows contain the shared ring's actual arc. Together with four other rings, pi<=2B+4A-t_shared. Hence t_shared<=2B+4A-pi (about .144219), a necessary severe small-arc condition; this may interact with the two triple common-point geometries. No contradiction or sharp lower bound is yet asserted from it.
