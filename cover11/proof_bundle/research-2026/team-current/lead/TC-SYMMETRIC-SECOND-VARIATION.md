# Positive symmetric common-active tangent block at C891

## Exact object and scope
Let f:R7→R5 be TC res5; (z*,lambda*) is the exact C891 isolated root, Df(z*)^T lambda*=e_R. Set H=−Σlambda_i* D²f_i(z*). On ker Df(z*) this is the Hessian of the radius constrained to f=0 in the boundary-saturated symmetric chart. All variables and radii are physical as in C891. This is a two-dimensional tangent statement, not full local optimality and certainly not global optimality.

## Interval graph basis
`certify_tc_symmetric_hessian.py` evaluates J=Df and H on the entire original12Droot box. Select dependent coordinates (a0,a1,a2,a3,R), free coordinates (y0,y1). Certified nonzero interval pivots permit interval Gaussian elimination of the5×5 dependent minor. With Z_dep=−J_dep^{-1}J_free and Z_free=I2, columns of the exact Z span kerJ. The interval matrix Z encloses this exact graph basis, not an approximate SVD nullspace.

The output `tc_symmetric_hessian.json` records exact rational endpoints extracted from mpmath interval internals. At the exact root:
G=Z^T H Z has
 G00∈[.5782359965,.5897772454],
 G01=G10∈[−.3141969061,−.2984278099],
 G11∈[.9650777969,.9866240938],
 detG∈[.4593230259,.4928292825].
These printed decimals are conservative summaries; comparisons use exact dyadic endpoints. Both Sylvester tests are strictly positive. Moreover detG/traceG>.2913>1/4 proves G>(1/4)I2 in the free-hub-coordinate metric. Do not compare these eigenvalues with an orthonormal TC basis or physical Euclidean coordinates without the metric change.

## Interface to full physical second variation
The symmetric active equality manifold in physical12Dspace is first parametrized by the seven-dimensional TC boundary chart and then by f=0. At stationary points, the Hessian of the constrained objective on a tangent vector equals the Lagrangian Hessian evaluated on that vector; chart-curvature terms cancel using the full multiplier stationarity. Thus once the physical multiplier lift is fixed, this G is congruent to its symmetric common-active tangent block. This is an exact differential-geometric identity, not an assumption that second derivatives commute with a nonlinear coordinate substitution without curvature.

The full reflected problem has symmetric and antisymmetric tangent subspaces. An invariant Lagrangian has no cross terms between those subspaces. Exact positive full minimax weights are now certified in C897. The antisymmetric block modulo rotation is under final implementation/branch audit. No local-minimum claim is made in this note alone; see LOCAL-CERTIFICATE-ASSEMBLY.md for the complete inference.
