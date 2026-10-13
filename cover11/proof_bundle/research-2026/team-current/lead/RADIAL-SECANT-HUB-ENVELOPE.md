# General convex-program upper envelope for the Cartesian hub fiber

This is a proposed next certification representation, not a completed bound.
Fixed outer(r,b1,b2), hubX=(v,t) lies in the C858 convex lens. The Cartesian objective has linear area A·X and two terms
 f_j(X)=a_j theta_j + beta_j L_j² + gamma_j L_j,
 L_j=|X-Q_j|, theta_j=atan2(Y_j,X_j), where the two local coordinate maps differ only by reflection.
For the current exact coefficients, a_j>0,beta_j>0,gamma_j<0, and 2beta_j*(2r)+gamma_j<0 uniformlyr<=.38 (verify directedbeforecertification). Distances are bounded above2r and below by |c_j|-(1-r) when positive, or general1/50000.

## Radial upper bound
For any verified intervalL∈[l,u], convex quadratic secant gives
 beta L²+gamma L <= [beta(l+u)+gamma] L-beta*l*u.
This is an exact identity with gap beta(L-l)(u-L)>=0. If m=beta(l+u)+gamma<=0, the rightside m|X-Q|-beta*l*u is concave in X. Thus all radial terms have a concave upper envelope with explicit known error <=beta(u-l)²/4.

## Angle upper bound
An angle lives on the verified Y>0 branch. On any convexbox/path region whosedistancefromQ is>=l>0, its Hessian operator norm is1/L²<=1/l². Therefore theta(X)<=theta(X0)+gradtheta(X0)·(X-X0)+|X-X0|²/(2l²), PROVIDED the whole segment stays awayfromQ and remains on the sameanglebranch. Actualhubconvexity alone does not automatically bounddistancealongsegment unless allpointsinlensalreadyhaveL>=l; C858lensdoes supplynecessarynormlowerbound ifpositive. For a>0 this is an upperenvelope. Could use a triangle-angle sector tighterthanisotropicremainder.
With globalcoarse l thistermcanbeuseless; must exploitlocalboxes or the fullhubnormdistance lowerbound. No unproved angleconcavity.

## Certification direction
Keep exact concave radialnormterms (or replace by tangentaffinemajorants) and upperbound angle via tangent+quadratic. Maximize the resulting upperbound overthree-disks/wedge using validated disk-support duality. A numerical convex optimizer is only a proposal for dualmultipliers. This works for arbitraryhubmaximizers; C860 forbids globallyassumingridge. No claim of finite stationaryrootexhaustion or concavity oforiginalobjective.
