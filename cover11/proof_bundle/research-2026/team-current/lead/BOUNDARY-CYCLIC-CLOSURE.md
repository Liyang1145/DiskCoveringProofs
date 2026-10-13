# Local cyclic boundary closure: recovering missing unit-circle geometry

Object: reduced inward-root9-ring+2-hub unit-disk cover, r<=R=.38. Boundary switches P_i between sites c_i,c_(i+1) have owned arc widths w_i from P_(i-1) toP_i, sector angle alpha_i at c_i. Endpoint distances are R*u_i,R*v_i. Switch opposite half-angle b_i as in C817.

Define sector triangle base angles
 L_i=atan2(v_i sin alpha_i,u_i−v_i cos alpha_i),
 T_i=atan2(u_i sin alpha_i,v_i−u_i cos alpha_i).
For positive noncollinear triangle, L_i+T_i=pi−alpha_i. At switchP_i the site triangle angle is2b_i. The boundary polygon's interior angle is pi−(w_i+w_(i+1))/2, since its vertices lie on the unit circle. Thus the exact local equation is
 T_i+L_(i+1)+2b_i+(w_i+w_(i+1))/2−pi=0.

Why unsigned angles are legitimate: each boundary chord has width<=2asin r, hence its supporting line lies at distance>=sqrt(1−r²) from origin; inward-root sites have norm<=sqrt(1−r²). All sites are on the polygon-interior side of every boundary chord. The refined straight-site triangulation plus site-switch triangles and sector triangles tiles the inscribed switch polygon; angles at each switch add to its interior angle. Limiting tangencies handled by closed-domain relaxation. This is a necessary constraint, not asserted sufficient to realize the embedding.

Add9 unrestricted multipliers h_i. Switch factor gains2h_i*b_i; constant gains−pi*sum h_i; sector i gains h_(i-1)L_i+h_i*T_i+(h_(i-1)+h_i)w_i/2. Use T_i=pi−alpha_i−L_i for two-parameter formula. Summing all closure equations only recovers total width and existing site angle equations: there is a linear redundancy, not9 independent obligations. Individual equations nevertheless recover missing curvature distribution. No rank count is asserted.

Calibration `check_boundary_closure.py`: independently reconstructs actual Euclidean coordinates, circumcenters and unit-circle switches on saved certified upper candidate plus20 perturbed diagrams; maximum switch residual<1e-9 (saved candidate≈5.6e-16). Numeric calibration is not proof; polygon-angle argument above is the universal proof.

Interval sector derivatives for q=u²+v²−2uv cos alpha>0:
 L_alpha=(uv cos alpha−v²)/q,
 L_u=−v sin alpha/q,
 L_v=u sin alpha/q.
Use natural atan2 intervals on any box meeting q=0 or angle boundary; no derivative bound through singularity. Fully positive interior boxes intersect direct enclosure with mean-value gradient enclosure. A radius-zero corner can have multiple limiting base angles, so atan2(0,0) must never silently fix a value in a purported full-domain certificate. The direct interval enclosure must include[0,pi] when necessary.

Files: q0_closure_dual.py sampled proposer; certify_q0_closure.py interval kernel (work in progress). No new exclusion follows until kernel passes full-domain audit and a continuous bound below pi is obtained.
