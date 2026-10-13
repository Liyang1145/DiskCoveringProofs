# Exact grouped face-area envelope for sum beta >= pi

## Object and domain
A genuine triangular dualface f has circumradius R=xU, opposite real angles gamma_i summing pi. Each of its three facet endpoints on the other side has radius T_i=y_i U (neighbor circumcenter or boundary anchor), 0<x,y_i<=1. Its facet angles satisfy 0<beta_i<pi and gamma_i+beta_i<pi; shared chord gives
 x sin gamma_i=y_i sin(gamma_i+beta_i).
The sum of the three pairedfacetareas is A=U² x sum_i y_i sin beta_i. Edge-disjoint packs may group these areas without doublecounting.

## Theorem
Write Bsum=sum_i beta_i. For pi<=Bsum<2pi let x0 be the unique number in(0,1] satisfying
 sum_i atan2(sin beta_i,x0−cos beta_i)=pi.
Then A<=U² x0 sum_i sin beta_i. This is the EXACT maximum over the local radius/angle interface: equality is attained by x=x0, all y_i=1, and gamma_i=atan2(sin beta_i,x0−cos beta_i).
For Bsum<pi use the safe (not generally sharp) bound A<=U² sum sin beta_i. For Bsum>=2pi no positive nondegenerate local interface exists; closed degenerate limits must be handled separately, not discarded by strict assumptions.

## Proof
For fixed beta∈(0,pi), x,y>0, the chord identity uniquely gives
 gamma=atan2(y sin beta,x−y cos beta)∈(0,pi−beta),
 d gamma/dy=x sin beta/(x²−2xy cos beta+y²)>0,
 d gamma/dx=−y sin beta/(x²−2xy cos beta+y²)<0.
Consequently pi=sum gamma_i<=H(x):=sum atan2(sin beta_i,x−cos beta_i). H is strictly decreasing. H(0+)=3pi−Bsum>pi and H(1)=(3pi−Bsum)/2<=pi, so a unique x0∈(0,1] exists with H(x0)=pi, and x<=x0. Therefore A<=U² x sum sin beta_i<=U² x0 sum sin beta_i. Conversely x=x0,y_i=1 satisfies all three identities and the real-angle sum; so bound is attained in this local relaxation. No assertion that every local interface embeds into a global cover.

## Algebraic representation (branch explicit)
Let a=sum sin beta_i>0, b=sum_{i<j}sin(beta_i+beta_j), c=sin Bsum<=0. Imaginary part of product_i(x−cos beta_i+i sin beta_i) is a x²−b x+c. For pi<Bsum<2pi, c<0, there is exactly one positive root:
 x0=(b+sqrt(b²−4ac))/(2a).
It is the H(x)=pi root: H runs from( pi,2pi ) to <=pi, so its only integer-pi crossing is pi. At Bsum=pi use x0=1 by continuity. At Bsum→2pi, x0→0 for beta staying inside(0,pi). Boundary beta=0/pi may have a=0 and require continuous inequalities or original geometric limits, not division by a.

## Calibration
`shared_face_radius_probe.py/json` numeric12starts each: candidate slackfaces14/15 attain this all-neighbors-saturated maximum≈.282630433281426, consistent with true R=.3208208546. This diagnostic motivated the monotonic proof; proof does not use optimizer.

## Certification route, no need to divide by small a
For a beta-box with sumlower>=pi, choose rational X∈(0,1). If an interval upper bound of H(X) is <pi, then x0<X for every beta in box, so A<=U² X sum sin beta. But atan bounds may be avoided: certify polynomial branch atX, or use monotonic gamma in beta (not globally monotone without checking). Safe default X=1. Boxes touching degenerate branches revert to old nonnegative loss bound. Do not promote numeric maxima to certified support.
