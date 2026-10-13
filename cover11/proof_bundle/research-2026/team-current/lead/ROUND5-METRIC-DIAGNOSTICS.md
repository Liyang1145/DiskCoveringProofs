# Round5 metric representation diagnostics (not optimality proof)

## 1. Candidate-native exact closure relaxation
`q0_exact_closure_radius.py` maps saved certified coordinate candidate onto q0 k4 graph, independently computes face angles/circumradii and switch halfangles/distances. Variables63:33 face angles9 switch b20 log normalized radii and1 log covering radius. Equations43:11 triangle sums2 hub sums21 side matching9 local cyclic closure. All candidate residuals<1e-15 and decomposed area equals pi to floating precision. Numerical Jacobian rank41, not a certified rank assertion. Three local constrained solves return R≈.379983853119839 with18/20 radius constraints active. Local minima only; neither global nor exact candidate-optimality proof.

`q0_closure_tangent.py` uses independently assembled centered scalar Lagrangian Hessian. Active equalities numeric rank59, tangent dimension4; active radius KKT multipliers all positive (~.00989 through.127); tangent Hessian eigenvalues~.04003,.04968,.05661,.05820. These are diagnostics, not remainder bounds. Two nonactive face radii normalized≈.9969665, so global all-radii-saturated WLOG would exclude the saved candidate and is invalid as a route to that candidate.

## 2. Exact sum identity, no fake extra constraint
Let S be sum of face angles at ring vertices, B=sum switch b, A=sum sector alpha.11 triangle angle sums minus2 hub sums imply S=7pi. Ring winding equations alpha_i+sum faceangles_at_i−b_(i−1)−b_i=pi imply A=2pi+2B. Local cyclic equations sum to9pi−A+2B+sum w−9pi=0, hence sum w=2pi. Thus total owned boundary width is already an exact consequence on the full matching+closure manifold. This proves one linear dependence after inclusion of total width; it does NOT explain numerical rank deficiency of the43 equations, which do not include total width. Metric integrability may explain those two dependencies; teammate investigates.

## 3. Necessary sector norm filter (derivation, proposed)
For an actual inward-root cover of radius r<=R, sector endpoint distances Ru,Rv, angle a, let q=u²+v²−2uv cos a>0. The chord line is at distance sqrt(1−R²q/4) from target origin. Inward triangle height H=Ruv sin a/sqrt q; center norm squared is exactly
  |c|²=1+R²uv cos a−2sqrt(1−R²q/4)H.
Inward-root gives |c|²<=1−r² and actual r²>=R² max(u²,v²), therefore NECESSARILY
 R²[max(u²,v²)+uv cos a]<=2sqrt(1−R²q/4)H.
This avoids the invalid substitution |c|²<=1−R² when r<R. Domain: correctly inward-oriented sector triangle inside switch polygon, angles[0,pi], endpoint distances<=r, q>0. Local-circle-geometry audit pending; no exclusion claimed from this filter.

## 4. Bounded dual experiments
Switch inward cap Ry<=cos b (already derived in C817 discussion) did not visibly close k4 gap: N48/NR16/NA144 sampled bound3.1783825 (different grid from baseline, not a rigorous monotonic comparison). Sector norm filter at same grid gives3.1693154, still>pi. No method-impossibility or actual covering conclusion. Files q0_switchcap_dual.py/.json, q0_sectornorm_dual.py/.json. These are sample proposers only; no new continuous certificate.
