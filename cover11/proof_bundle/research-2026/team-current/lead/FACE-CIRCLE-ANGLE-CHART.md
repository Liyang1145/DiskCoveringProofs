# Exact saturated-face circle angle chart

Same C858 Cartesian displacement (v,t), high bearings or any nondegenerate C848 patch. This is an algebraic representation, NOT a curvature/maximum claim.

Face1, parameter A=b1-delta: H=2r sin(b1+A), delta=b1-A. Product-to-sum gives
v=r[sin(2b1)+sin(2A)], t=r[cos(2A)-cos(2b1)].
Thus it is the face1 circle centred (r sin2b1,-r cos2b1), radius r; Cartesian circle parameter theta=pi/2-2A. The legal A interval must still satisfy the other face disk, norm disk and wedge.

Face2, parameter B=b2+delta: H=2r sin(b2+B), delta=B-b2. Then
v=r[sin(2b2)+sin(2B)], t=r[cos(2b2)-cos(2B)].
The face2 circle centre is (r sin2b2,r cos2b2), radius r; theta=2B-pi/2.

The common positive-H face intersection is delta=b1-b2, A=b2,B=b1,H=2r sin(b1+b2). In high-bearing domain T=b1+b2>2>pi/2, equality sin(2b1-delta)=sin(2b2+delta) gives 2 cos(T) sin(b1-b2-delta)=0; legal wedge then selects delta=b1-b2. The second Cartesian face-circle intersection is H=0, outside the norm disk. No half-difference collar.

Use for an independent derivative control: for a circle x(theta)=c+r(cos theta,sin theta),
d²F/dtheta² = x'(theta)^T Hess(F) x'(theta) + grad(F) dot x''(theta).
A positive ambient Laplacian does NOT imply positive circle second derivative. Need both terms, including curvature normal acceleration. Since theta is affine in A/B/delta with speed2, d²F/ddelta² =4 d²F/dtheta².
