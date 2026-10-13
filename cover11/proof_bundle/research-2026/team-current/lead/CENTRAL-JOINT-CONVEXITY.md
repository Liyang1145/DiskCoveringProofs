# Uniform acuteness gives joint convexity of the TWO-hub fiber

## Domain
Use the C904 rational nominal nine-ring centers ordered [5,7,1,8,6,4,9,10,3], each Cartesian coordinate halfwidth1/1000; r centered at3799838531198387090485182/10^25 with halfwidth1/10000. Fix any legal ring tuple and r in this box. K_A is the intersection of the closed pin disks on ring edges4..8 and the closed strict-hub-ball relaxation B(0,1−r). K_B uses edges0..3. Actual strict hub restrictions may be added without losing convexity. A is the lower hub in this labeling, B the upper hub (opposite the lettering in C906).

## Certified geometric premise
`check_central_acuteness.py` independently reconstructs all pins and the two variance-localization balls using exact rational interval arithmetic, not rounded JSON enclosures or mpmath endpoint arithmetic. Uses the inspected Fraction primitives from r20-gluing/r23_central_screen_audit.py, with all scale multipliers nonnegative. Pin squared separations and radicands strictly positive; smaller-norm branches are separated; every box intersection is checked nonempty. Variance weights positive summing1 imply the localization ball, hence the constructed rectangles contain every A∈K_A and B∈K_B.

For each c=c0,c4, all three dot products (B−A)·(c−A), (A−B)·(c−B), (A−c)·(B−c) have exact interval lower bounds >1/50. Diagnostic lower endpoints:
- c0: .08268398920675417, .04492778122575558, .3850648305020801;
- c4: .08261673485896413, .04499486253402343, .38510503807330304.
Thus BOTH triangles are strictly acute for the ENTIRE rectangular product, uniformly over ring/radius box. Strict acuteness automatically excludes coincident and collinear site triples.

## Convexity proof
For three acute sites p1,p2,p3, the circumcenter z lies in their convex hull: z=Σλ_i p_i, λ_i>0, Σλ_i=1. Their common circumradius is R. For any point q,
Σλ_i |p_i−q|² = R²+|q−z|²≥R².
Thus no enclosing disk has radius<R, and the circumdisk is the minimum enclosing disk (MEC). Consequently Rc(A,B,c)≤r iff there exists z with |z−A|,|z−B|,|z−c|≤r.

For FIXED rings and r, the set
{(A,B,z0,z4): A∈K_A, B∈K_B, |zi−A|≤r, |zi−B|≤r, |zi−ci|≤r for i=0,4}
is convex: every constraint is an affine preimage of a Euclidean ball, including the pin constraints. Projection onto(A,B) is convex. Uniform acuteness makes this projection exactly the two-central-circumradius feasible set, not a relaxation. Intersecting with open strict-hub balls also preserves convexity.

This upgrades conditional fiberwise biconvexity to full JOINT convexity in four hub coordinates, on the stated ring box. The projection onto either hub is therefore convex as well. It does NOT imply joint convexity in moving ring coordinates (pins move nonlinearly), a global acute theorem, a one-dimensional scan, or full covering sufficiency without the existing graph/geometry conditions. No exact-C891-root inclusion in the nominal ring box is claimed here.

Evidence: independent member mpmath proposal `r20-alternative/central_acuteness_interval.py/.json` (initial endpoint-arithmetic caveat noted); bearing Fraction replay `lead/check_central_acuteness.py/.json`. Repro: `py -3 -B -X utf8 research-2026/team-current/lead/check_central_acuteness.py`.
