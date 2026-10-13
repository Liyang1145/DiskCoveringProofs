# Exact compatible-edge support reduction (solo continuation)

## Object

Unit-disk equal-radius covering, r<=R=.38, same inward-root nearest-cell and refined-dual setup as C812. This note strengthens the area interface without assuming acute triangles, positive signed circumcenter offsets, equal radii at distinct Voronoi vertices, or metric symmetry.

## 1. Compatible area of one Voronoi edge

Take sites i,j at separation d>0. For an interior edge, a,b are opposite site-triangle angles in its two incident Delaunay triangles. For an edge ending on the target boundary, a is its interior opposite triangle angle; define b=pi/2−gamma, where gamma∈[−pi/2,pi/2] is the signed angle from the site-to-site ray to the site-to-boundary-switch ray (positive toward the exterior side). Both cases have a,b∈[0,pi], a+b<=pi. The latter is just nonnegative Voronoi edge length.

Signed distances along the bisector from its midpoint to the two edge endpoints are d cot(a)/2 and d cot(b)/2; they need not both be positive. The endpoint distances from either site are rho_v=d/(2sin a), rho_w=d/(2sin b), both <=r. Combined area of the two site-edge triangles is
  d²/4 (cot a+cot b).
Since the cotangent sum is nonnegative and d<=2R min(sin a,sin b), this area is bounded by
  G(a,b)=R² sin(a+b) min(sin a/sin b, sin b/sin a).
Define G=0 at triangle-domain endpoints by continuous extension. Artificial zero-length edges have a+b=pi and contribute zero. Thus the formula is valid through cocircular triangulation, not just generic input.

This replaces the old independent-wedge bound R²sin(a+b) and is strictly stronger when the two adjacent endpoint radii could not simultaneously equal R.

## 2. Exact support theorem, eliminating a two-dimensional supremum

For ANY real p,q, on T={a>=0,b>=0,a+b<=pi},
 sup_T [G(a,b)+pa+qb]
 = max(0,pi p,pi q, sup_{0<=t<=pi}[R²sin t+(p+q)t/2]).

Proof. On the branch 0<a<b and a+b<pi, sin a<sin b, and G/R²=sin a cos a+sin²a cot b. Its Hessian determinant is
 -4 sin²a (sin a cot b+cos a)² csc²b
 = -4 sin²a sin²(a+b)/sin⁴b <0.
Thus adding an arbitrary linear function cannot create an interior local maximum. The other branch is symmetric. Maxima on the compact closed triangle must lie on a=b, a=0, b=0, or a+b=pi. On the last three G=0 and extrema are vertices; on a=b=t/2 it is R²sin t. All singular endpoints are continuous (G<=R²sin(a+b), and the ratio is <=1). This proves the exact support formula, not a sampled envelope or numerical concavity assumption.

The scalar supremum for c=(p+q)/2 is 0 when c<=−R², c*pi when c>=R², otherwise at cos t=−c/R². This avoids any bivariate grid or unknown local stationary points in the certificate.

## 3. Triangle/site equations and dual assembly

Use the straight-site realization of the nearest-site dual. A true primal vertex is the center of an empty circle through its incident sites. Those sites, in cyclic order, form a convex cyclic polygon; triangulate that polygon consistently with the established dual. Empty-circle polygons from different primal vertices form the usual noncrossing Euclidean Delaunay cellulation, so this realizes the same clipped dual with straight edges. A three-site collinearity cannot occur on a finite positive-radius circle with distinct sites. Thus refined face triangles are nondegenerate; zero-length primal diagonals mean cocircularity, not collinear sites. At an interior hub the full star winds once. Boundary-switch spokes delimit the omitted outer sector of each ring star. These facts justify using actual triangle angles rather than merely abstract topological corner variables.

Each refined Delaunay triangle f has three nonnegative angles A_fi summing to pi. At each hub i, sum_f A_fi=2pi. At each boundary ring i, its owned boundary-sector angle alpha_i satisfies
 alpha_i+sum_f A_fi−b_left−b_right=pi.
Derivation: summing paired Voronoi edge angles gives sum_f A_fi+gamma_left+gamma_right; add alpha_i to obtain 2pi, and substitute gamma=pi/2−b. This derivation retains signed gamma and does not assume the boundary switches lie in a centered sector.

Dual multipliers: mu_i for the nine ring equations and two hub equations; nu_f for face-angle sums; lambda,eta>=0 for the total owned-width and outside-six width constraints from C813.
Constant term:
 pi(sum_ring mu+2sum_hub mu+sum_f nu−2lambda−2eta)+2eta asin(2R).
An edge opposite angle at vertex k in face f gets coefficient p=−nu_f−mu_k. A boundary endpoint variable b gets coefficient q=mu_i+mu_j. Interior edges have a second face coefficient of the same type. Take exact edge supports from §2. Ring supports are the univariate suprema of F(alpha)+(lambda+eta*1_outside)W(alpha)−mu_i alpha, using C812's corrected chord envelope. The result is a global upper bound on area for every legal covering with that graph.

Numerical findings (NOT certificates): linear face compatibility alone barely changes the old area maximum; two hub sine-product holonomies also do not change it in the tested optimizations. Retaining G lowers local degree-(5,7) optima below pi, but local optima are not global bounds. The finite-grid factor dual only gets below pi for start7/span3, so certify that position only unless another proof is found.

Evidence: `area_face_angles.py`, `area_holonomy.py`, `area_edge_compatible.py` (diagnostics); `edge_compatible_dual.py` (finite-grid multiplier proposal); `certify_compatible_position.py` (exact edge support + directed interval ring supremum with global Lipschitz enclosure).
