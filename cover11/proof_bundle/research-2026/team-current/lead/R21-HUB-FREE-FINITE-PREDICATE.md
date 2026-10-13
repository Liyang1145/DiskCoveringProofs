# Hub-free finite covering predicate

Combine C877 (split residual vertex theorem) with exact closure membership R21-RESIDUAL-MEMBERSHIP.md. For fixed boundary-covering inward ring centers, r and separating line, form finite vertex lists V-,V+. Actual hubs are unnecessary to decide feasibility.

For each side V define a finite family of CLOSED disks F={B(0,1-r)} union {B(v,r):v in V}. A hub covers that entire split residual iff intersection(F) is nonempty. If V is empty, the side is empty by C877 and any hub in B(0,1-r) suffices.

## Finite feasibility test (all radii positive)
Intersection(F) is nonempty iff either
(a) one of the disk centers belongs to all disks, OR
(b) a boundary intersection point of two distinct noncoincident disks belongs to all disks.
Coincident identical circles can be deduplicated. Containment/tangencies must be handled exactly; no division by center distance in coincident cases.

Proof: sufficiency immediate. For necessity choose any boundary point x of nonempty compact intersection (there is one because bounded). At least one constraint circle passes through x; if two distinct circles do, (b). Otherwise there is a unique circle through x. The portion of that circle satisfying all constraints contains an arc around x unless another boundary is at x. Continue along its circle in each direction: if feasible arc ends, an endpoint belongs to another circle, giving (b). If it never ends, the whole circle is in every convex disk, hence so is its closed disk, in particular its center, giving (a). If the total intersection has no interior and x belongs to a unique circle, the strict other constraints make a small inward neighborhood feasible, a contradiction; thus lower-dimensional intersections are also covered by (b).

For two circles centers p,q radii a,b, let d=|q-p|>0. Boundary intersections exist iff |a-b|<=d<=a+b. Set u=(q-p)/d, A=(a²-b²+d²)/(2d), B=sqrt(a²-A²). Points p+A u +/- B Ju give all intersections, tangent B=0 once. Candidate containment is squared-distance <= radius². Thus exact algebraic feasibility can replace every hub solve; in numerical use directed intervals/branch isolation needed at equalities.

## Outer quantifiers remain
For all ring placements with boundary coverage and inward bounds, the n11 existence question becomes: exists line (unit normal n, offset t in [-1,1]) for which both finite predicates hold. Outer ring/r/line variables are still continuous. Disjunctions of circle arrangement, semicircle membership and active feasibility witnesses introduce branches but no unexplained continuum over target points remains. This may permit low-dimensional line search or symbolic witness-type inequalities; it does NOT yet prove global lower bound.

Independent representation: R20 minimax dual gives M_H(V)=max probability measures [E|v|²-|Ev|²+dist(Ev,H)²], supported on <=3 points. The current test is primal intersection geometry, not shared optimization software. For a rigorous lower bound one can give an empty three-disk Helly witness; for an upper/feasibility result give one center satisfying all vertex disks.
