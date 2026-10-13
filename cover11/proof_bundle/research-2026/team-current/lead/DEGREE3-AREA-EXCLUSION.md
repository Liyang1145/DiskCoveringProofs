# Refined degree-three hub exclusion, r <= 19/50

## Proposition and scope

Conditional only on the previously proved 9+2 reduction and dual-topology results C450/C451/C464/C801/C802/C809: in any inward-root representative of an eleven-disk covering of the unit closed disk with radius r<=R=19/50, every locality-preserving refined dual has BOTH hub degrees at least four. This excludes refined degree splits (3,10) when q=0 and (3,9) when q=1 (and swaps). It does not exclude q=1 or prove the optimum. Artificial zero-length edges are allowed. Do not conflate refined degree with the number of positive-length physical Voronoi edges.

## 1. Angles and exact area decomposition

All eleven distinct centers lie in int D and in the interiors of their own clipped nearest-site cells. Each of the nine ring cells owns one connected boundary arc; hubs own none. Join each site to the endpoints of every straight cell edge and to the endpoints of its own boundary arc. This partitions each convex cell into triangles and one curved sector for boundary cells. Every positive straight-edge wedge angle theta_e is in (0,pi): the edge lies on a bisector whose positive distance from the site is half the site-site distance. The two triangles on the sides of one edge are reflected across that bisector; hence their site angles agree and their combined area is at most r² sin(theta_e)<=R²sin(theta_e). For a refinement edge with zero primal length, insert theta_e=0 and zero area.

The boundary sector angle alpha_i is in [0,pi]. Indeed the inward-root condition gives rho_i²<=1-r². For every u on its actual boundary arc, u·c_i >=(1+rho_i²-r²)/2 >=rho_i², so (u-c_i)·c_i>=0. All rays to that arc lie in one closed semicircle. The nearest-owned subarc inherits this. It does not matter whether its endpoints are equidistant from the site.

Thus for each site j,
  sum_{e incident j}theta_e + (alpha_j if j is a ring else 0) = 2pi.
All variables lie in [0,pi]. The nine actual owned boundary angular lengths w_i sum to 2pi.

## 2. Correct bound for skew boundary sectors

Let a,b<=r<=R be distances from a ring site to its two boundary endpoints, and alpha their site angle. Squared chord length is a²+b²−2ab cos(alpha). This is separately convex in a,b on [0,R], so it is at most R² max(1,4sin²(alpha/2)). The owned arc is minor (subset of the actual ring arc, whose length<pi), hence
  w <= W(alpha) := 2 asin(R max(1/2,sin(alpha/2))).
The site lies on the inward side of the endpoint chord: the chord has distance cos(w/2)>=sqrt(1-r²)>=|c_i| from the origin, since w<=2asin r. Thus the triangle and outward circular segment have disjoint interiors. The sector area equals the triangle area plus the unit-circle segment area:
  A_sector = (ab sin(alpha))/2 + (w−sin w)/2
            <= F(alpha):= R²sin(alpha)/2 + (W(alpha)−sin W(alpha))/2.
This is valid even for very skew endpoints. The formerly imported w<=2asin(Rsin(alpha/2)) is not justified below alpha=pi/3 and is NOT used.

Consequently a covering must satisfy
  pi <= R² sum_e sin(theta_e) + sum_i F(alpha_i),
  sum_i W(alpha_i)>=2pi,
with the site angle equations above.

## 3. Complete degree-three graph enumeration

By C801/C809 the refined dual has q=0 or q=1 and 21 edges. If hub 9 has degree three, two of its neighbors are ring transition vertices u,v and the third is hub 10. They must be consecutive in the ear-deleted core. Hub 10 joins every core ring vertex. Boundary edges are (i,i+1 mod9); q=1 adds ear chord (0,2) and removes ring 1 from the core. Rotation fixes the ear at (0,1,2). For q=0, all nine choices of uv are equivalent by rotation; retain (0,1). For q=1, retain all eight core edges:
 (0,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,0).
This includes every position relative to the ear and allows hub exchange. No symmetry of the metric configuration is assumed.

## 4. Global dual upper certificate (no local optimization inference)

For arbitrary real mu_j (j=0..10) and lambda>=0, let
  D = 2pi(sum_j mu_j−lambda)
      + sum_{edges ij} sup_{0<=t<=pi}[R²sin t−(mu_i+mu_j)t]
      + sum_{rings i} sup_{0<=a<=pi}[F(a)+lambda W(a)−mu_i a].
Every feasible area upper expression is <=D: add lambda(sum W−2pi)>=0 and subtract the exact site-angle equations. So any D<pi contradicts coverage. Neither concavity nor KKT optimality is required.

The saved numerical optimizer ONLY proposes mu/lambda. The certificate rounds each multiplier to eight decimal places, treats those decimals as exact rational data, and upper-bounds the full continuous supremum by interval-evaluated grid nodes plus rigorous Lipschitz margins.

Grid: x_k=22k/(7N), k=0..N, N=2048, covering [0,pi] with step h=22/(7N). The tiny extension beyond pi causes no issue: the defined W,F are evaluated on [0,22/7]. W is piecewise smooth and Lipschitz<=1 there, since its nonconstant derivative has absolute value <=R/sqrt(1-R²)<1. F is Lipschitz<=1 since |F'|<=R²/2+(1−cos W)|W'|/2 <=R²/2+R²<1. Therefore edge residual Lipschitz<=R²+|mu_i+mu_j|, and ring residual Lipschitz<=1+lambda+|mu_i|. Each grid max plus Lh is a valid continuous upper bound, including the kink at pi/3.

`certify_degree3_area.py` uses mpmath directed interval arithmetic, dps=35, to evaluate all nodes, coefficients and pi. It does not invoke or trust the optimizer or any unverified stationary-point status. All nine graphs certify D<pi; the largest computed rigorous upper endpoint is below 3.044, while pi>3.14. The slack includes the full grid error, not just roundoff.

Repro:
  py -3 -B research-2026/team-current/lead/certify_degree3_area.py
Input proposed multipliers: area_repaired_dual.json.
Output: degree3_area_certificate.json; certify_degree3_area.log.

## 5. What is and is not gained

Refined hub-degree sums are 13 (q=0) and 12 (q=1). Excluding a degree-three hub leaves unordered splits:
 q=0: (4,9),(5,8),(6,7);
 q=1: (4,8),(5,7),(6,6).
A full hub polygon has at least three positive edges, so no smaller refined degree is possible. These are remaining necessary topology cases, not claimed realizable.

The original global sharp lower bound remains unproved. The next promising structural use is to combine these degree limits with ring radial/arc constraints or a stronger area budget. This result alone does not certify any radius better than the existing global bound.

Independent arithmetic control added: `check_degree3_fraction.py` (no mpmath/scipy/transcendental functions, N=1024, rational Taylor/asin-series enclosures) verifies all nine cases with upper bound <=3.0678<3.14159<pi; output `degree3_fraction_control.json`. This changes the arithmetic support from one interval engine to two distinct inferences. It is a same-agent independent mathematical representation, not an independent member review.
