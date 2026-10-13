# Repaired symmetric TC root and geometric interface

## Scope
The target remains global n=11 optimality. This note only defines an exact local candidate by an isolated 12D equation system, then describes the still-audited link to its exact covering radius. A stationary candidate, even a genuine local minimum, is not the global lower bound.

## Historical correction
C408 was withdrawn: old Krawczyk used positive point radii instead of symmetric displacements and floated the center residual before wrapping as a zero-width interval. No registered downstream claim depended on C408. Historical output itself called the instrument noncertifying. Do not reinstate C408 or silently reuse its PASS.

## New kernel
`repair_tc_krawczyk.py`, `repaired_tc_krawczyk.json`.
Unknown z=(a0,a1,a2,a3,y0,y1,R), multipliers lambda in R5. F=(f5, e_R-J_f5^T lambda). The residuals are precisely tc_s32_kraw.res5 (see geometry below). Interval nested automatic differentiation implements derivatives of sin, cos, reciprocal, product and positive sqrt. Center and preconditioner entries are exact binary floating-point rationals; F(center) is evaluated in interval arithmetic, not rounded mpf/float evaluation. The displacement box is exactly [-rad,rad]^12. Outward interval row sums bound ||I-YJ(X)||_infty. At rad=1e-9 inclusion holds and contraction upper is about .004371972. The wrong-lambda center (+.01) fails inclusion. Independent explicit symbolic-to-interval derivative construction is assigned; provisional status is an audited-kernel candidate, not a newly registered proof yet.

Contraction establishes Y nonsingular: ||I-YJ||<1 implies YJ invertible at every point, hence Y invertible. The map x-YF(x) maps X into int X and is contracting, so there is exactly one zero in X. This is a claim about the 12D symmetric equations only.

The root R numerically equals .3799838531198386897222616061360932143087189561522153. This decimal is not the exact root. The output interval encloses it, currently about ±2.2e-15 from the final K image. Exact root definition is the system plus the rational isolating box, never the displayed decimal.

## Geometry of the symmetric equations
Set a4=pi-2(a0+a1+a2+a3), a=(a0,a1,a2,a3,a4,a3,a2,a1,a0). Thus sum a=pi exactly. Set theta4=0 and theta[k+1]-theta[k]=a[k]+a[k+1] cyclically. rho[k]=cos(a[k])-sqrt(R^2-sin(a[k])^2); Ck=rho[k](cos theta[k],sin theta[k]); hubs H0=(y0,0),H1=(y1,0).
The unit-circle tie Bk at angle theta[k]+a[k] is exactly R from Ck and C[k+1]. Pins Uk=Ck+C[k+1]-Bk are the other equal-R circle intersection. Reflection across the x-axis maps Ck to C[8-k] and Uk to U[7-k mod9].
The first four equations are |U1-H1|=R, |U2-H0|=R, |U3-H0|=R, |U8-H1|=R. Reflection supplies U6,H1 and U5,H0 and U4,H0: exactly seven active fan triangles. The remaining two fan triangles (U0,H1 and U7,H1) are strictly slack, not assumed saturated.
Let m=(y0+y1)/2, d=(y1-y0)/2, h=sqrt(R^2-d^2). The fifth equation is |(m,h)-C6|=R. The two hubs have distance R from (m,h) identically. Reflection supplies central face through C2 with center (m,-h). These are two active central triangles. Total active circumcenters: nine of eleven; plus nine covered boundary ties = eighteen active branches.

## Interval geometric margins (separate from exact equalities)
`check_tc_root_geometry.py`, `tc_root_geometry.json` operate on the full rational root box, using the root equations analytically only to select the exact active circumcenters. They do NOT prove equality by finding an interval containing zero.
They check positive sqrt branch margins, positive arc widths, strict hub norms, nine-ring convex hull orientation (all other sites strictly left of each hull edge), all eleven fixed combinatorially assembled faces with strictly empty circumcircles and interior circumcenters (fixed list plus edge incidence, no triangulation algorithm dependency), and strict slack for the two remaining circumradii. The selected faces are explicitly listed in the JSON and must be interpreted combinatorially (not 'SciPy said so'). Their number is 2*11-9-2=11. Strict empty-circle margins are >.1504 throughout the box; hub norm-squared margin >.3099. This also identifies the active centers as genuine Voronoi vertices, giving R_D>=R.

To conclude R_D<=R, use boundary coverage plus all interior Voronoi vertices. Boundary arcs exactly tile because sum a=pi. A positive maximum of nearest-site distance on the disk occurs on the boundary or at a Voronoi vertex: on a single site's cell interior squared distance has no positive local maximum; on a two-site Voronoi edge its restriction is a strictly convex quadratic, so no relative-interior local maximum. Higher ties are vertices. Hence complete Delaunay/Voronoi incidence and all listed radii <=R suffice. This requires checking the selected face list is the entire triangulation, using strict hull and empty-circle margins, rather than merely counting samples.

## Remaining implications
1. Finish independent interval kernel audit; then register a NEW exact-root claim, not an upgrade by retract.
2. Finish geometric face-list assembly and branch coverage to identify the root radius as an actual covering radius.
3. Link the symmetric stationary system to full tied KKT, respecting all other nonsymmetric/mixed directions and boundary saturation constraints.
4. Prove global exclusion below this root across the remaining q0(6,7) ring family. This is the original and still open main obligation.
