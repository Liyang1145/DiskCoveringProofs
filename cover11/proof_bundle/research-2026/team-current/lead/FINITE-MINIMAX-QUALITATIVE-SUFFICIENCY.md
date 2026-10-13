# Qualitative strict local minimax sufficiency, no guessed remainder radius

Let g1,...,gm be C² near x*=0 in a finite-dimensional linear slice, all gi(0)=r*. Suppose positive weights wi>0 satisfy Σwi=1 and Σwi Dgi(0)=0. Let K=∩ker Dgi(0), and H=Σwi D²gi(0). Assume H restricted to K is positive definite (including the vacuous case K={0}). Then there exist c,epsilon>0 with max_i gi(x)>=r*+c|x|² for 0<|x|<epsilon.

Proof. Write a(v)=max_i Dgi(0)v for unit vectors v. Weighted stationarity implies a(v)>=0. Because every weight is positive, a(v)=0 implies all Dgi(0)v=0, hence v∈K. Thus the zero set of a on the unit sphere is exactly K∩sphere.
If K is nonzero, H is uniformly positive on K∩sphere by compactness. By continuity it is still uniformly positive, say v^THv>=eta>0, on an open neighborhood U of that set in the sphere. Taylor's formula for L=Σwi gi, whose gradient vanishes, gives L(tv)>=r*+(eta/4)t² for all v∈U and all sufficiently small t>0. Uniformity of the o(t²) remainder follows C² smoothness on a ball. Since max gi>=L, this proves the required lower bound in U.
On the compact complementary directions sphere\U, a(v)>=delta>0. Finite-family Taylor expansion with bounded second derivatives gives max_i gi(tv)>=r*+delta*t−M*t², hence >=r*+c*t² for sufficiently small t. If K={0}, apply this argument to the entire sphere. Combine the two bounds. QED.

## Rotations
For the disk-cover objective rotation invariance gives an orbit. Choose a smooth local slice transverse to it (e.g. require the distinguished nonzero ring C4 to lie on the positive x-axis). At a stationary point the Hessian of the weighted branch function restricted to a slice equals the pullback of the ambient weighted Hessian; gradient-dependent curvature terms vanish. The slice theorem and the result above give a strict local minimum modulo rotation and a local quadratic growth bound in slice coordinates. Relating to distance to the orbit only requires local coordinate comparability; exact equality of those distances is unnecessary.

## Application requirements (closed in C902)
1. Exact C891 candidate, all active physical face/boundary covering-radius branches smooth and equalR at it.
2. Strict geometric margins ensure these branches remain actual critical distances near the point. Hence true cover objective >=max active branches; equality at the base is C892. This lower-support property suffices; one need not show which inactive branch becomes active at every nearby point.
3. Exact positive minimax weights (root identities + chart lift + interval signs).
4. Positive H on common-gradient kernel modulo rotation. Reflection gives invariant symmetric/antisymmetric subspaces and exactly zero cross terms; each block still needs proof. C893 provides the symmetric block, via its nonlinear-chart constrained-Hessian congruence; C901 provides the antisymmetric quotient. LOCAL-CERTIFICATE-ASSEMBLY.md assembles them into C902.

This theorem establishes an EXISTENTIAL local neighborhood without explicit third-derivative constants. If a finite numerical neighborhood is later needed for global domain coverage, explicit remainder bounds and chart coverage are additional quantitative obligations. They should not be confused with the logical requirements for qualitative local optimality. None of this excludes remote configurations.
