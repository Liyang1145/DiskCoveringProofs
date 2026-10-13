# Exact fan-deficit coordinates (metric route after theta-grid diagnosis)

Fix actual covering radius allowance R>0, a hub H and consecutive neighboring sites U,V in one oriented refined triangle, nondegenerate at H. Put |HU|=2R cos s, |HV|=2R cos t with s,t∈[0,pi/2], and hub angle theta∈(0,pi). All dual face sides<=2R. By sine law, circumradius<=R iff
 cos²s+cos²t−2cos s cos t cos theta <= sin²theta.
Completing square gives
 (cos theta−cos s cos t)² <= sin²s sin²t.
Since cos is decreasing[0,pi], this is EXACTLY
 **|s−t| <= theta <= s+t**.
The triangle area is2R²cos s cos t sin theta. Ring edge length is2R sqrt(cos²s+cos²t−2cos s cos t cos theta). Thus each fan triangle radius inequality becomes LINEAR in deficit angles and hub increments. No saturation. Closed extension includes zero spoke limits, but a=0 leads theta-label ambiguity at coincident sites; for actual indispensable sites a>0 and coordinate is unambiguous, closure can enlarge domain safely.

For a complete hub star with d neighbor sites, deficits s_i=acos(|H−c_i|/(2R)) and positive consecutive increments theta_i summing2pi, face conditions are |s_i−s_(i+1)|<=theta_i<=s_i+s_(i+1). Hence Σs_i>=pi, equivalently Σacos(d_i/(2R))>=pi. This is the known hub-circle service capacity, here strengthened by every lower/upper pair bound and exact per-face area.

q0(6,7) theta network has two hubs A,B, common AB deficit z. HubA chain ring0..4 has5spoke deficits s0..s4; hubB chain ring4..8,0 has6deficits t4..t8,t0. Endpoint triangles (A,B,0),(A,B,4) share three sides and so impose actual triangle cosine-law relation, not merely separate fan constraints. Interior fan angular resources: sum4 incrementsA=2pi−angleA(X)−angleA(Y); sum5 incrementsB=2pi−angleB(X)−angleB(Y). These resource equalities are crucial correlation discarded by independent-angle duals.

Structural payoff: exact endpoint-conditioned fan optimization is a one-dimensional chain in spoke deficit s with one additive angular resource; joint two-hub structure is two such chains glued by endpoint triangle variables. Interval dynamic-programming bins in(s, accumulated theta) can enforce angular sums without global highdim box enumeration. No polynomial moment or symmetry premise needed. Face-only theta-grid LP (m13,25) shows severe grid optimism, so no nearpi number should be certified by blind refinement.

Next proof obligation: establish an analytic concave envelope of fan area/ring-edge dual as function(spoke endpoints,total angle) or certify it by resource DP. Need retain ring constraints to get sharp unit-circle bound; standalone star capacity already known insufficient. This identity is analytic exact; not yet a sharp inequality or optimality result.
