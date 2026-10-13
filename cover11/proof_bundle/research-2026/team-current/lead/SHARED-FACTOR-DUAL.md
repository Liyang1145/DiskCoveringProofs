# Shared squared-radius factor dual

Uses C816 exact shared-side geometry, but avoids logarithms and retains compact boxes including zero radii as a relaxation. Scale R=19/50. Let x_f=rho_f²/R² for11 triangular faces, x_j=sigma_j²/R² for9 boundary switches, all in[0,1]. Ring sectors have endpoint copies u_i=sigma_(i-1)/R,v_i=sigma_i/R. Enforce u_i²=x_(i-1),v_i²=x_i. Face angles sum to pi; ring/hub equations as in C814. Side matching is x_f sin²(A)=x_g sin²(B), with boundary face-to-switch matching x_f sin²(A)=x_j sin²(b_j).

## Exact area alternative

Summing site-edge triangles across faces gives
 A=sum_faces 2R² x_f sin A sin B sin C
   +sum_switches R² x_j sin(2b_j)/2
   +sum_rings S(alpha_i,u_i,v_i),
 S=R²uv sin(alpha)/2+(w−sin w)/2,
 w=2asin(R sqrt(u²+v²−2uv cos alpha)/2).
The factor 1/2 in the switch term is essential: one signed circumcenter-side contribution is d² cot(b)/4=rho²sin(2b)/2. This exact identity is independently checked against the previous edge sum on saved candidate coordinates and20 perturbed diagrams (`check_radius_tree.py`). The first diagnostic script version briefly omitted this1/2; it was fixed before any certificate or claim, and its output replaced.

## Boundary angle domain

The adjacent site midpoint m lies strictly inside the unit disk; the outward bisector ray meets its circle at w=m+ell*n with ell>0. Thus b=atan2(d/2,ell) lies in(0,pi/2), not the larger interior-edge opposite-angle domain.

Also, inward-root sites satisfy |c_i|²<=1-r² and sigma<=r. Hence w·(w−c_i)=(1−|c_i|²+sigma²)/2 >=sigma²; average over the two sites gives ell*w·n>=sigma². Since w·n<=1, ell>=sigma² and cos b=ell/sigma>=sigma. Optional boundary cap x_j<=min(1,cos²b/R²) is therefore valid. Certificates below enlarge back to x∈[0,1], so do not depend on that cap.

## Dual assembly

Multipliers indexed as scripts: mu[0:11] for site equations; beta[21] for signed squared-side matching; delta[18] for switch-to-sector radius copies; kappa[21]>=0 for pi−a−b>=0; lambda,eta>=0 for total and outside-six width. Constant:
 pi(sum_ring mu+2sum_hub mu+sum kappa−2lambda−2eta)+2eta asin(2R).

Face factor (angles A_k sum pi):
 sum_k (−mu_k−kappa_opposite)A_k
 +max(0, 2R²sin A sin B sin C+sum_k sign(f,e)*beta_e sin² A_k).
Here sign=+1 at the first face of each sorted edge,−1 at the second; face radius maximization is EXACT since affine in x_f.

Switch factor b∈[0,pi/2]:
 (mu_i+mu_j−kappa_e)b
 +max(0,R²sin(2b)/2−beta_e sin²b+delta_(i,right)+delta_(j,left)).
Again switch squared radius has been maximized exactly over[0,1].

Ring factor alpha∈[0,pi],u,v∈[0,1]:
 S(alpha,u,v)+(lambda+eta*1_outside)w−mu_i alpha−delta_(i,left)u²−delta_(i,right)v².

The constant plus these29 global factor suprema bounds the exact covering area. Dropping side matching/endpoint-copy equations only after adding multipliers is valid weak duality; unlike independent edge factors this retains their aggregate effects.

## Certification kernel

`shared_factor_capdual.py` only proposes coefficients using finite grids. `certify_shared_factors.py` rounds them to exact9-place decimals and reconstructs the graph independently. Directed mpmath.iv bounds are applied on full factor domains: 11 triangular face domains (a,b rectangle intersected with0<=pi−a−b),9 switch intervals,9 sector boxes. Adaptive subdivision is ONLY an efficiency device; live interval upper bounds prove domain coverage. Floating priorities are rounded outward using nextafter; coefficients and final sum are interval quantities. Sampled lower values only determine subdivision/stopping; interval upper bounds remain the evidence. In the final kernel even pruned boxes retain their greatest interval upper bound in `discarded_upper`; the final bound is max(live queue upper, discarded upper), independent of sampled lower validity. Zero-radius and zero-angle boundary points are included. No optimizer optimality assertion is used.

Ring intervals intersect two enclosures: direct interval evaluation and a centered mean-value enclosure. Put q=(u−v)²+4uv sin²(alpha/2), w=2asin(R sqrt(q)/2), H=C+(1−cos w)/2, C=lambda+eta*1_outside>=0. The scalar h(w)=Cw+(w−sin w)/2 is monotone, so its interval uses only endpoint evaluations, avoiding cancellation. Where q>0:
 w_alpha=Ruv sin(alpha)/(sqrt(q)*sqrt(1−R²q/4)),
 w_u=R(u−v cos(alpha))/(sqrt(q)*sqrt(1−R²q/4)), and symmetrically w_v.
The chord norm is 1-Lipschitz in each of u,v and alpha (u,v<=1), so each derivative is globally bounded in absolute value by L=R/sqrt(1−R²). At q=0 use [-L,L]; the norm is Lipschitz and the mean-value integral inequality still holds across its nondifferentiable locus. Ring gradients are R²uv cos(alpha)/2+H w_alpha−mu, R²v sin(alpha)/2+H w_u−2delta_left*u, and the symmetric v derivative. The code retains two-sided alpha derivative bounds even for outward-rounded domains extending a floating epsilon beyond pi. This validates the centered enclosure without finite-difference derivatives or smoothness assumptions at coincident endpoint copies.

Scope: at present only q1 degree-(5,7) representatives are targeted for certification. Balanced(6,6) finite-factor proposals remain above pi and do not settle those classes.
