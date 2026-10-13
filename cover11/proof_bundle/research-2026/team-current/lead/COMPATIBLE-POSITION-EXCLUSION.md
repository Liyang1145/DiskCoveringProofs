# One q1 degree-(5,7) position excluded

Under the previously proved inward-root/global-dual reductions and C813's outside-six capacity, the q=1 graph whose ear is (0,1,2) and whose degree-five hub has ring path [8,0,2,3] is impossible at r<=19/50. The degree-seven hub follows the complementary path [3,4,5,6,7,8]. Hub interchange and cyclic relabeling are allowed; no metric reflection symmetry is assumed.

This is start7/span3 of core [0,2,3,4,5,6,7,8]. The path straddles the ear chord and has one additional core edge at each end. The ring reflection i->(2−i) mod9 preserves this graph up to reversing the path.

Proof: the exact compatible-edge support theorem in COMPATIBLE-EDGE-SUPPORT.md supplies a global dual area bound. `certify_compatible_position.py` verifies the graph face and edge lists, rational-decimal coefficients, nonnegative coverage multipliers, all exact bivariate edge supports, and the nine full univariate ring suprema by directed interval arithmetic with rigorous Lipschitz error. Continuous area upper endpoint is <3.139628, strictly below pi>3.1415926. No finite-grid optimization premise is used; `edge_compatible_dual.json` only supplies proposed coefficients.

Repro: py -3 -B research-2026/team-current/lead/certify_compatible_position.py
Evidence: compatible_position_certificate.json; COMPATIBLE-EDGE-SUPPORT.md.
Coordinate calibration (not proof): `check_edge_interface.py` reconstructs areas, signed edge offsets and site-angle equations from independent Euclidean Delaunay coordinates on 20 perturbed two-hub/nine-ring diagrams; maximum discrepancy 1.34e-15. The analytic proof is what covers the continuum and degeneracies.

Remaining q1 topology after this result:
 * degree (5,7): start representatives 0,1,2,3; their reflection mates are 6,5,4, respectively for 0,1,2, while start3 is fixed; start7 excluded.
 * degree (6,6): two representatives, starts0 and2 under reflection and hub exchange.
The exact class enumeration is to be checked with explicit set maps before further certificate expansion; this statement does not exclude those remaining graphs or assert their realizability.

The interval endpoint excludes only one graph class, not q1 globally and not sharp n11 optimality. Main objective remains active.

Independent arithmetic control completed: `check_compatible_fraction.py` gives exact upward bound 785349/250000=3.141396<3.14159<pi, N=16384. Sine/cosine Taylor bounds, asin positive-series tails, and a concavity tangent with rigorously bounded slope replace the interval trigonometric stationary-point evaluation. Numerical acos proposes a tangent point only; its accuracy is not assumed. Coordinate calibration output is `edge_interface_calibration.json`. Reflection classes checked explicitly: (5,7) {0,6},{1,5},{2,4},{3},{7}; (6,6) {0,1,4,5},{2,3,6,7}.
