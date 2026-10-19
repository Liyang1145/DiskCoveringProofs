# q0 closure exclusions and unconditional r_D(11)>3/8

Object: unit closed disk,11 equal covering disks, arbitrary sites/overlap. Existing C450/C451/C464 reduce any hypothetical cover r<=19/50 to inward-root9essential ring+2indispensable hubs. C818 eliminates q1 entirely; C819 eliminates q0(4,9); surviving q0 graphs are k3=(5,8),k4=(6,7).

C820 supplies nine universal exact cyclic closure equations. Define sector i=(A=P_(i−1),C=c_i,B=P_i), |CA|=Ru,|CB|=Rv, angleC=a. L_i is angle atA, T_i atB (NOT L_i atP_i). AtA, dot/cross formula gives
 L_i=atan2(v sin a,u−v cos a) in[0,pi], T_i=pi−a−L_i.
No supplement choice: nonnegative triangle cross magnitude and signed dot uniquely give ordinary base angle. q>0 follows positive owned width. Thus C820 atP_i uses T_i+L_(i+1)+2b_i+(w_i+w_(i+1))/2−pi=0 exactly as the code coefficients. Collinear limiting triangles handled by closed intervals; proof needs no generic perturbation.

The existing shared first/second moment area dual C817/C818 is augmented by arbitrary real multipliers h_i times these zero residuals. Nonnegative multipliers remain on established Delaunay edge slack and total width slack (total width actually equals2pi on real covers). Exact formal coefficient assembly checked using Fraction for each new coefficient set. Every genuine area pi<=dual sum<=constant+sum factor suprema. Domains face(a,b,c>=0,sum pi,y∈[0,1]); switch(b∈[0,pi/2],y∈[0,1]); ring(a∈[0,pi],u,v∈[0,1],q>=qmin). These domains intentionally include unrealizable combinations, so exclusion of this superset is sufficient.

## Full-domain arithmetic results
1. k3 atR=19/50: upper interval [3.09579300912180273035495257169,3.09579300912180273035495443285]<pi. File q0_closure_dual_certificate_0_3.json, coefficients therein exact9place decimals. Thus no q0(5,8) genuine cover at anyr<=.38.
2. k4 atR=3/8: upper interval [3.10878894698666798598029369521,3.10878894698666798598029534957]<pi. File q0_lower375_dual_certificate_0_4.json. Thus no q0(6,7) genuine cover at anyr<=3/8.

Combining1,C818,C819 leaves ONLY q0(6,7) for r<=.38. Combining2 eliminates this final class at r<=3/8. Therefore r_D(11)>3/8. Strictness of infimum: center projection into closed unit disk cannot worsen coverage; compact11site parameter space plus continuity of covering radius gives attainment. No actual cover at3/8 hence attained optimum strictly exceeds3/8. This is NOT sharp optimality and does not attain Tcert as lower bound.

## Verification and independent interfaces
- Analytic proof of new geometry: CLOSURE-LOCAL-HALFPLANE-PROOF.md (C820); no false four-cell argument.
- Analytic directed-kernel audit: CLOSURE-KERNEL-ANALYTIC-AUDIT.md, derivative_control.json, existing Q-support Fraction checks. Branch-and-bound accounts for ALL discarded terminal UBs, not just remaining queue; interval transcendental directed rounding at25decimal precision.
- Exact formal coefficients: check_q0_closure_symbolic.py, check_q0_lower375_symbolic.py.
- Independent scalar geometric dual: check_q0_closure_scalar.py, residual<9e-16 (calibration only).
- Separate65digit scalar formulas vs random interval boxes: check_closure_boxes.py,0violations among13439legal scalar points on4350boxes (calibration only, no continuum inference).
- One full interval implementation, not a duplicate independent full certifier. Teammate kernel audit pending, not a premise nor a claim of independent review. Agent identities and workflow statuses do not establish proof.

Reproduce:
 py -3 -B research-2026/team-current/lead/certify_q0_closure.py 0 3
 py -3 -B research-2026/team-current/lead/certify_q0_lower375.py 0 4
 plus coefficient/scalar/box control scripts above. Each verifier uses its saved coefficients, NOT rerunning LP proposals.
