# All q1 degree-(5,7) positions excluded at r<=19/50

## Statement and scope

In the globally reduced inward-root nearest-site 9-ring+2-hub covering problem, q=1 cannot have refined hub degrees(5,7). This includes all overlap patterns, metric asymmetries and cocircular refinements within the established dual class. Together with C813 and degree-sum reduction C809, every remaining q1 cover has refined hub degrees(6,6). This does NOT exclude q1 or prove the sharp radius.

## Graph coverage

Fix the ear (0,1,2) and core [0,2,3,4,5,6,7,8]. A degree-five hub follows a three-edge path of this eight-cycle. Starts0..7 partition under relabeling reflection i->(2−i) mod9 and hub exchange into {0,6},{1,5},{2,4},{3},{7}. Reflection is a graph isomorphism, not a geometric-symmetry assumption. Exact set enumeration is in `check_shared_dual_symbolic.py`. C815 excludes start7; new shared-radius factors certify starts0,1,2,3.

## Proof

Use the exact area/side-matching representation in SHARED-FACTOR-DUAL.md, derived from C816. Every legal cover supplies angle/radius values in its full closed factor domains. Site equations, shared squared-side lengths, and endpoint radius copies cancel with exact multipliers. The two width inequalities have nonnegative multipliers. Thus total area<=constant+29 factor suprema. Face and switch squared radii are analytically maximized at endpoints0 or1; ring factors retain both endpoint distances. The full continuous suprema are bounded by directed interval subdivisions, not finite grids or local optimization.

Certified bounds, each less than3.14159<pi:
 * start0: <3.135372;
 * start1: <3.116720;
 * start2: <3.090707;
 * start3: <3.089278.

All boxes including limiting zero radii/angles are enclosed. Boundary-switch b domain is[0,pi/2]; the proof of this restriction is in the factor note. The optional stronger cap sigma<=cos b was used only in numeric proposals, NOT by the certificate, which safely enlarges switch radii back to[0,R].

## Evidence and audits

- `shared_factor_certificate_{0,1,2,3}_3.json`: full factor upper bounds, exact9-place decimal coefficients, directed total intervals.
- `certify_shared_factors.py`: reconstructs graph independently; analytic elimination of squared radii; interval direct and mean-value enclosure; all pruned-box upper bounds retained.
- `check_shared_dual_symbolic.py`: separate exact Fraction coefficient cancellation for all formal angle,side²,radius²,width atoms in all four graphs; exact reflection orbit enumeration.
- `check_shared_dual_identity.py`: separate scalar-loop evaluation on six numeric radius-compatible states, max cancellation residual about1.2e-12 (calibration only).
- `check_radius_tree.py`: saved certified optimum candidate and20 perturbed Euclidean diagrams; exact-expression area agrees numerically with direct cell areas and pi, tree radius ratios and boundary widths agree. Explicitly checks the crucial1/2 switch-area coefficient.
- The interval supremum arithmetic is one implementation, not two independent arithmetic kernels; the symbolic and geometric checks audit different bearing interfaces.

Reproduce:
 `py -3 -B research-2026/team-current/lead/run_shared_certificates.py`
 `py -3 -B research-2026/team-current/lead/check_shared_dual_symbolic.py`
 `py -3 -B research-2026/team-current/lead/check_shared_dual_identity.py`
 `py -3 -B research-2026/team-current/lead/check_radius_tree.py`

Remaining obligation: globally exclude or bound q1(6,6), where the current finite-factor dual proposals stay above pi (~3.162,3.166), and prove the unrestricted q0 sharp bound. Local shared-radius maxima below pi are not certificates for those balanced classes.
