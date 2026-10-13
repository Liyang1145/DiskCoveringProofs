# Nine boundary cells plus two bounded interior cells: exact interface

Object: D is the unit closed Euclidean disk; eleven distinct centers with congruent closed covering disks of radius 0<r<=19/50 cover D. Assume the established C450/C451 reduction (nine boundary disks and two strictly interior disks), and the independently proved arc-ledger property: the nine actual boundary arcs are essential, cyclically ordered, only neighboring arcs overlap, and no triple overlap occurs. No zero-overlap or symmetry assumption.

Status: analytic derivation, independent review requested; no optimality conclusion.

## 1. Each boundary disk owns exactly one connected nearest-center boundary arc

Write I_i for its actual covered arc on the unit circle. A point outside I_i cannot be in its restricted nearest-center cell: some covering center is at distance <=r, whereas center i is farther than r. In the private open part of I_i only disk i covers, so its distance is strictly smaller than all other centers'. In an overlap I_i intersect I_{i+1}, only these two disks can win the nearest-center comparison. The difference of their squared distances is the restriction of a nonconstant affine function to the unit circle.

For a positive-length overlap, at its first endpoint disk i is strictly closer (the other distance equals r); at its last endpoint disk i+1 is strictly closer. The endpoint inequalities are strict because each disk's actual arc has length less than pi and the endpoints in this cyclic overlap are distinct. An affine line intersects a circle in at most two points, and opposite endpoint signs force an odd number of transverse intersections; hence exactly one intersection in the overlap. A tangent zero would not change sign and cannot coexist with a transverse zero for a line-circle intersection. If the overlap has zero length, that common endpoint is the unique tie. Thus each I_i contains exactly one connected closed nearest-center boundary arc, of positive length. There are exactly nine distinct nearest-center boundary switches.

The two interior disks cannot be closest anywhere on the boundary: |h|+r<1 implies |u-h|>=1-|h|>r, while some ring disk covers u.

## 2. Both complete hub Voronoi cells are bounded inside D

Let V_h={x: |x-h|<=|x-c| for every other center c}. It is convex and contains a neighborhood of h, since all centers are distinct. h is in int D. No boundary point of D belongs to V_h by the strict inequality above. If V_h contained a point outside int D, its segment to h would meet the boundary and remain in V_h, contradiction. Therefore V_h subset int D; being closed and bounded it is compact. Since the eleven disks cover D and h is a nearest center throughout V_h, V_h subset B(h,r).

This statement concerns the full, not merely clipped, hub cell. It bypasses the unsafe inference from original ring adjacency to active Voronoi adjacency.

## 3. Combinatorial count, with explicit regularity condition

Intersect all Voronoi cells with D. All eleven faces have nonempty interiors (each distinct center is in D after inward-root replacement; alternatively this condition must be imposed here). The nine boundary switch points have graph degree three: two circle edges and one Voronoi edge entering D. Indeed at a switch only its two ring sites have equal distance <=r, and all others have distance >r; this strict separation persists locally. Their bisector is secant, not tangent, since its distance from the origin is ||c_i|²-|c_j|²|/(2|c_i-c_j|) <= (|c_i|+|c_j|)/2 <= sqrt(1-r²)<1. Exactly one ray of this local bisector enters D. This supplies the explicit transversality argument requested by the independent review. In the open disk every graph vertex has degree >=3. Suppress artificial degree-two subdivisions. Each cell is convex and hence a disk; the whole cellulation is connected.

Let v be the number of interior vertices and e the number of nonboundary edges. Euler for a disk gives (v+9)-(e+9)+11=1, hence e=v+10. Degree counting gives 2(e+9)>=3v+27, hence v<=11 and e<=21. If all interior vertices are trivalent, v=11 and e=21. High-order cocircular coincidences decrease the counts, not increase them. Degenerate zero-length edges are not counted.

Inward-root replacement (C464) ensures all nine ring centers have norm <=sqrt(1-r^2)<1 and preserves coverage and their actual boundary arcs; the two hubs were already interior. Distinctness: ring centers are distinct because their boundary arcs are essential and distinct; hubs cannot equal each other because one would be deletable, nor equal a ring center because only ring disks meet the boundary. Thus the all-eleven-nonempty-cell premise holds for an inward-root representative.

## Payoff and unresolved implication

This replaces arbitrary boundary Voronoi topology with a disk cellulation having exactly nine ordered boundary faces, two compact interior polygon faces, at most eleven interior vertices and at most twenty-one interior edges. It does NOT show that the two hub cells share an edge, that ring-ring chords are absent, or that every vertex is trivalent. Those are explicit next obligations, not hidden assumptions. The original success criterion is still the unrestricted optimum r_D(11)=r_ideal; this lemma alone gives no matching lower bound.

Evidence sources: solo-20260922/N11-LOW-RADIUS-REDUCTION.md; solo-20260922/INNER-ROOT-DOMINANCE.md; team-max-20260922/n11-structure/ARC-COORD.md. Literature context: lit2/fejes-toth-2005-lemmas.md (Dirichlet-cell method for n=8,9,10; no novelty claim).
