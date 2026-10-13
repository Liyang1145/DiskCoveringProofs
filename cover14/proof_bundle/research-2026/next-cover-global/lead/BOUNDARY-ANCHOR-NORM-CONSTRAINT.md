# Exact shared-anchor norm constraint (new polynomial necessary interface)

Work at fixed threshold U: every r<=U cover is a U-cover; apply innerroot normalization at U afresh, then C1171 clipping and constantgraph limit. Hence |c|<=s=sqrt(1−U²). This can change the graph; catalogue is existential and covers all new possibilities. Angles are limiting actual geometry, not unconstrained atan branch.

Let A∈S1 be shared boundaryanchor, |A−u|=|A−v|=a<=U, and angleuAv=2gammaA with gammaA∈[0,pi/2]. Put d_u=(A−u)/a, d_v similarly; both are unitvectors. The normcap gives
 A·d_u >= (a²+U²)/(2a)=k(a), and similarly v.
Consequently a>=1−s>0 (reverse triangle inequality) and both d's lie in a cone of halfangle acos k(a). Therefore
 **cos gammaA >= (a²+U²)/(2a).**
Equivalently the midpoint m=(u+v)/2 obeys |A−m|=a cosgammaA, and the minimal possible max(|u|²,|v|²), over anglebisector orientation, is 1+a²−2a cosgammaA. This independently gives same inequality. Equality when bisector points radially inward and |u|=|v|=s.

Use realface radius R, pairedangle beta and a. Let D=sqrt(a²+R²−2aR cosbeta), the distance between A and realcircumcenter O. On strictboundaryfacet D>0,
 cosgammaA=(a−R cosbeta)/D, sin gammaA=R sinbeta/D.
Thus exact necessary polynomial constraints, after introducing c=cosbeta and D>=0, are
 D²=a²+R²−2aR c;
 a−R c>=0;
 **4a²(a−R c)² >= (a²+U²)² D².**
The square is legitimate only WITH the unsquared nonnegative sign. At D=0 anglelimit must be retained: polynomial inequality alone becomes vacuous but remains necessary. For D>0 this is equivalent to norm-cone inequality; it is not sufficient for global realization.

Normalize a=Uy,R=Ux: D=U d, d²=y²+x²−2xy c. Then
 y>= (1−sqrt(1−U²))/U,
 y−xc>=0,
 **4y²(y−xc)² >= U²(1+y²)²(y²+x²−2xyc).**
This is stronger than replacing k(a) byU since k(a)>=U for0<a<=U (a+U²/a>=2U). It couples the anchor deficit directly to boundaryface radius and beta; unlike the relaxed cone cap, it may penalize non-saturated anchors. Candidate all a=U gives previous cone inequality. No global optimization conclusion.
