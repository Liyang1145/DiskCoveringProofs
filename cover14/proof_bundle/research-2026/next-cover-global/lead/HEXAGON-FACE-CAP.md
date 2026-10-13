# Universal face area cap via signed hexagon — analytic proof

## Object
One genuine oriented triangular dual face f=(u1,u2,u3), counterclockwise; circumcenter O. Across edge ui,u(i+1) the facet's other endpoint is Ai (neighbor circumcenter or boundary anchor), with Ti=|Ai−ui|=|Ai−u(i+1)|<=U. Indices cyclic. Delaunay/nearest orientation gives each pairedfacetarea Qi=R Ti sin beta_i>=0, equal to the signed area of quadrilateral (ui,Ai,u(i+1),O). This uses the same signed-area interface as C1199/C1227 and does not assume circumcenters inside triangles.

## Cancellation
Summing quadrilateral cross-products cancels the six O spokes. Thus
 sum Qi = signed_area(u1,A1,u2,A2,u3,A3).
This holds even for a self-intersecting or nonconvex polygon. All six edge lengths are respectively T1,T1,T2,T2,T3,T3. Consequently their squared-length sum is 2 sum Ti²<=6U².

## Signed polygon inequality
For any closed n-gon z_j in C, n>=3,
 signed_area = (1/2) Im sum conj(z_j) z_(j+1)
 <= (1/4) cot(pi/n) sum |z_(j+1)−z_j|².
Proof: write discrete Fourier expansion z_j=sum_k a_k exp(2pi i k j/n), with arbitrary complex a_k. Orthogonality gives area=(n/2)sum_k|a_k|²sin(2pi k/n) and edgeenergy=n sum_k|a_k|²(2−2cos(2pi k/n)). k=0 vanishes. For1<=k<n, quotient is cot(pi k/n)/4<=cot(pi/n)/4. Negative oriented modes automatically satisfy the inequality. Equality with nonzero area requires only k=1, hence regular positively oriented n-gon up to translation/rotation/scale.

## Conclusion, local universal exact maximum
 sum_i Qi <= sqrt(3)/2 sum_i Ti² <= (3sqrt(3)/2) U².
No assumptions on B=sum beta beyond the genuine local interface. Equality at regular hexagon with Ti=U, real face equilateral andR=U, all beta_i=pi/3. Bound extends by continuity to degenerate limits and does not rely on division by sin beta.

This proves the conjecture in SHARED-RADIUS-UNIVERSAL-CAP.md by a different representation, without the unproved Jensen route. It does NOT prove the n14 global optimum: boundary wedges/siteangle constraints and overlapping face costs still need global accounting. Edge-disjoint packs can safely use the cap. Weighted sum over all faces requires edge capacities as before.

## Certificate use
On each beta-box, alongside oldloss and exactroot upper bounds, use
 3sqrt(3)U²/2 − sum_i p_i beta_i
with boxwise affine support. sqrt(3) must be outward-enclosed by exact integer/sqrt arithmetic. Stronger radius-dependent cap sqrt(3)/2 sum Ti² may help coupled-radius patches but not yet used.
