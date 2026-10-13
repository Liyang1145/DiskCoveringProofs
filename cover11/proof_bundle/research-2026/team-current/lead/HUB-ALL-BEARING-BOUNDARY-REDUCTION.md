# All-bearing hub boundary reduction: separation axis and radial curvature

Theorem (analytic reduction + interval certificate): fixed frozen seven-factor objective, actual r in [3/8,19/50], both legal bearings bj in(acos(r)/2,acos(r)], legal C858 hub lens. Its maximum lies on at least one of the three disk boundaries. No ridge-only conclusion, no low-bearing objective upper yet.

## 1. Reduction to universal three variables
Let Q1=(r sin2b1,2r sin²b1), Q2=(r sin2b2,-2r sin²b2), d=|Q1-Q2|>0, e=(Q1-Q2)/d, n=(e_y,-e_x). The coefficient of the linear hub objective is exactly A=(d/2)n. Rotating positively oriented coordinates (n,e) and translating to the midpoint sends Q1,Q2 to (0,d/2),(0,-d/2). Additive angle constants do not affect derivatives; reflected atan angles have chirality sigma1=-1,sigma2=+1. The gradient equations, independent of the separate r,b1,b2, are given in HUB-SEPARATION-AXIS.md and hub_axis_stationary.py. Exact Sympy check_hub_axis_identities.py verifies both gradient equations, their mixed derivatives and the separation-direction curvature.

Constants beta1=-z16/(4R0²), beta2=z20/(4R0²), c1=z78/(2R0), c2=-z82/(2R0), a1=z1-z9, a2=z3-z9, allpositive. R0=19/50; z exact9decimal frozen row. Universal constraints Lj<=2r<=.76 follow from face disk conditions; this is a relaxation of the lens, not equivalence.

The radial lemma below implies L1,L2<.43 at any interior local maximum, hence d<=L1+L2<.86<1.049. This bypasses C862 completely and applies for all r∈[3/8,19/50]. Since bj>=acos(r)/2, d>=2r(sin²b1+sin²b2)>=2r(1-r)>=.46875>.45. In these rotated coordinates |x|<=.76, while |y-d/2|<=L1<=.76 and |y+d/2|<=L2<=.76 imply |y|+d/2<=.76, hence |y|<=.535. These bounds safely cover every interior local-maximum candidate of the entire bearing class. Only such candidates, not every stationary point, obey the radial lemma.

## 2. A radial curvature lemma removes large distances
For one summand beta L²-c L+a theta at distance L from its source:
H=2beta I-(c/L)(I-uu^T)+a Hess(theta),
where u is unit radial and Hess(theta) has operator norm 1/L² for either chirality. Along its own radial direction, the quadratic form is exactly 2beta (both length and angle second derivatives vanish).

At any point choose the unit radial direction to Q1. The full objective's second derivative in that direction is at least
2(beta1+beta2)-c2/L2-a2/L2².
Likewise along radial to Q2 it is at least 2(beta1+beta2)-c1/L1-a1/L1². Both bounds are increasing in their corresponding L, and directed evaluation at L=.43 is positive. Thus if either L1>=.43 or L2>=.43, some direction has positive curvature and the point cannot be an interior local maximum. IMPORTANT: the radial direction is to the OTHER source than the distance used in the lower bound. No stationarity needed for this cut, and no assumption of positive Laplacian.

## 3. A small pole neighborhood contains no stationary point
Both 2beta_j*.76<c_j. The radial part of source j's gradient has magnitude c_j-2beta_j Lj<=c_j. Project the total gradient onto the angular unit direction at source j; its own angular term has magnitude a_j/Lj and its own radial term vanishes. If Lj<=.005, the other distance Lk>=d-Lj>=.445. All other terms have magnitude at most d/2+c_k+a_k/Lk <=1.049/2+c_k+a_k/.445. Directed checks give a_j/.005 strictly larger, for each j. Hence no zero gradient in either pole neighborhood. This uses Lj,Lk<=.76 from actual feasibility.

## 4. Remaining stationary equations: interval root exclusion or positive curvature
On the universal box d∈[.45,1.049],x∈[-.76,.76],y∈[-.535,.535], retain only stationary local-max candidates with .005<=Lj<=.43. Evaluate the two gradient equations directly using full-extension interval AD. Boxes meeting a pole cause the smooth evaluator to refuse, never a false rejection.

The parameterized Krawczyk contractor holds d variable and centers only x,y. For any fixed d and true root X*,
X*=m-C g(d,m)+(I-C Jbar)(X*-m),
where Jbar is the integral Jacobian on the segment between m and X*. Any fixed finite matrix C is allowed; a floating midpoint inverse merely proposes it and is then treated as exact binary rationals in directed arithmetic. The Jacobian interval encloses every Jbar for every d in the parameter interval. Intersect the resulting coordinate enclosures with the box; an empty intersection excludes all roots, not an existence or uniqueness proof. Reapplying a sound contraction retains roots. Refusal on singular boxes simply leaves them for subdivision.

On surviving boxes: a component of the gradient excluding0 rejects stationarity; a strictly positive Hessian diagonal or strictly positive trace rejects local maximality. Both cases are ordinary second-order necessary conditions at an unconstrained smooth interior maximum. Both children and common endpoints of every split are retained. All queues must be empty for the conclusion.

## 5. Boundary conclusion
The C858 lens is compact; C862's wedge-exclusion argument holds for all legal bearings (positive width forces bj>acosr/2). Norm disk excludes v=0; each wedge edge would force the hub onto Qj, whose translated unit-disk site violates the inward norm. The hub angle and length terms are smooth on a neighborhood of the feasible set: sources Qj are outside the norm disk. An interior maximum would have zero gradient and negative-semidefinite Hessian, excluded by the radial/pole/interval analysis above. Hence every maximum is on at least one of the three disk boundaries.

Remaining: bound low-bearing circle arcs. Existing norm/ridge/face upper certificates C863/C869/C870 assume bj>=1 and must NOT be promoted to this larger domain. For b1+b2<pi/2, the sign of the face ridge-side inequality reverses; at pi/2 the two face circles coincide. These cases require explicit coverage.

## Replay and independent inference control
`certify_hub_axis_boundary.py` → `hub_axis_boundary_certificate.json`: 1495 evaluations, 0 live, exact frozen SHA5671967c5a3d..., outward initial domain. Radial lower margins >.05927317258411749 and >.07212548371958189.
`certify_axis_no_contraction.py` → `axis_no_contraction_control.json`: 1851 evaluations, 0 live; 151 geometric/radial/pole rejections, 691 gradient rejections, 84 positive-curvature rejections. This second run entirely bypasses Krawczyk and any linear-algebra inverse, so the main conclusion need not depend on a root contractor. It still shares interval AD; exact symbolic identities and direct Cartesian controls validate that interface, not an independent arithmetic backend.

R19 member audit initially included errors: other-source angular radial derivative incorrectly0; lower bound mistaken for equality; linear term confused x/y; |y| bound not recognized; allstationary confusedwithlocalmax. None are used here. Correct inequality is the operator-norm bound in §2, and the domain proof is the elementary two-distance intersection in §1. Lead proof/source take precedence; no claim rests on report approval.
