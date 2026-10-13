# Analytic regularity of the saturated odd-ring boundary chart

Local only near the repaired symmetric candidate; not a saturation WLOG for global optima.

## Regular radial coordinates
For a ring site with polar radius rho and target disk radius R, let
 a(rho,R)=acos((rho²+1-R²)/(2rho)).
At the candidate and an open neighborhood: 0<rho<sqrt(1-R²), 0<a<pi/2. Thus
 a_rho=(1-R²-rho²)/(2rho² sin a)>0,
 a_R=R/(rho sin a)>0.
The first derivative makes rho↔a locally invertible on the inward branch rho=cos a−sqrt(R²−sin²a). Check 1-R²-rho²>0 with the existing root-box interval geometry; it follows directly from rho<cos a and rho²−2rho cos a+1−R²=0.

For neighboring ring sites let unwrapped angular gaps be delta_i=theta_{i+1}−theta_i, cyclic sum2pi. Define gap constraints
 g_i=delta_i−a_i−a_{i+1}, i mod9.
Near the candidate, g_i=0 precisely when the disks meet at the relevant covered unit-boundary tie. The other radical-line unit-circle point is at distance strictly greater than R from this neighboring pair (it may of course be covered by other disks), so no branch exchange occurs. The boundary covering radius branch t_i(c_i,c_{i+1}) is smooth and g_i(c,R)=0 iff R=t_i(c), locally. Since g_{i,R}=−a_{i,R}−a_{i+1,R}<0,
 dg_i=(a_{i,R}+a_{i+1,R}) d(t_i−R) at g_i=0.
Thus positive gap-constraint multipliers and physical boundary-radius multipliers have the same sign.

## Rank without a numerical determinant
Keeping theta and R fixed, D_rho g=−(I+S)diag(a_{i,rho}), where S is cyclic shift. Since9 is odd, v_i+v_{i+1}=0 for all i implies v=0. Hence this9×9 radial Jacobian is invertible.
It commutes with the reflection after the appropriate edge-index permutation, so it restricts to an isomorphism from reflection-invariant radial variations (dimension5) to reflection-invariant gap variations (dimension5). Thus the five representative g constraints have rank5 on the symmetric12D physical variable space. Five representative boundary-radius constraints have the same rank by the positive row factors above.

## Explicit inverse and surjectivity
On g=0: delta_i=a_i+a_{i+1}, and summing gives sum_i a_i=pi. Reflection about x-axis identifies a=(a0,a1,a2,a3,a4,a3,a2,a1,a0), so a4=pi−2sum_{i=0}^3 a_i. Fix theta4=0 (the self-reflected site is on the positive x-axis, stable locally). The gap equations uniquely recover all theta_i by recursion. Recover rho by the inward root. The two symmetric hubs have free x-coordinates y0,y1. Thus (a0,a1,a2,a3,y0,y1,R) is a genuine local7Dchart of the boundary equality manifold, not merely a parametrized subset of the same dimension. Its inverse is the four site halfwidths plus hub coordinates and R.

No circle-ratio/angle-gluing compatibility is missing: these are actual physical center coordinates. The only local branch requirements are the explicit radial inequalities and stable cyclic order/reflection, all strict at the candidate.

## Interior residual conversion
For any chord a,b, let pin and pout be its two radius-R circle intersections, oriented so the tested third vertex h is on the pin side. With y its nonzero signed height over the chord,
 4y²(Rc²−R²)=Fin Fout,
 Fin=|h−pin|²−R², Fout=|h−pout|²−R².
At Fin=0 and Fout>0, for f=|h−pin|−R and G=Rc−R, the differential identity is
 dG=[Fout/(4y²)] df.
This is valid with all chord endpoints and R varying; derivatives of the prefactor and Fout vanish from the product at Fin=0. It applies to fan res5 and the central waist res5 by choosing hubs as chord endpoints, ring site C6 as third vertex, waist W+=(m,+sqrt(R²-ell²/4)) as pin, where ell=|y1-y0| is the FULL hub separation (the res5 symbol d=(y1-y0)/2 is the signed HALF separation, so equivalently the height is sqrt(R²-d²)). Need interval Fout>0 and y!=0; do not simply equate df and dG. The conversion is positive, preserving KKT multiplier signs.

Combining this chart proof and residual conversion with TC-TO-PHYSICAL-KKT-LIFT.md leaves explicit boundary multiplier sign enclosures as the first-order stationarity obligation. It still proves neither a local minimum nor global optimality.
