# Degree20 necessary polynomial for shared-hub fiber stationarypoints

C849 fixed(r,b1,b2,A); B=b1+b2−A; D_j=2r sinbj, theta1=A,theta2=B. Put Cj=Dj cos(theta_j),Yj=Dj sin(theta_j)>0 onnondegeneratefacebranch; Xj=H−Cj,Qj=Xj²+Yj². WithphysicalH,
 FH=constant+lambda H+a1 atan2(Y1,X1)+a2 atan2(Y2,X2)+beta1 Q1+gamma1 sqrtQ1+beta2 Q2+gamma2 sqrtQ2,
 lambda=(Y1+Y2)/2,
 a1=z1−z9,a2=z3−z9,beta1=−z16/(4R0²),gamma1=−z78/(2R0),beta2=z20/(4R0²),gamma2=z82/(2R0).
All formulas reference zeroangle-inequality multipliers z50..z72 ofjoint_nested_frozen.json. SinceQi>0,
 FH'=lambda+2beta1X1+2beta2X2−a1Y1/Q1−a2Y2/Q2+gamma1X1/sqrtQ1+gamma2X2/sqrtQ2.
Set polynomials inH:
 P=(lambda+2beta1X1+2beta2X2)Q1Q2−a1Y1Q2−a2Y2Q1 (degree<=5),
 U=gamma1X1Q2,V=gamma2X2Q1 (degrees<=3).
Then Q1Q2 FH'=P+U sqrtQ1+V sqrtQ2.
Every stationarypoint satisfies
 **G_H=(P²+U²Q1−V²Q2)²−4P²U²Q1=0**, degree<=20.
Proof: isolateV sqrtQ2=−P−U sqrtQ1, squareonce to obtainP²+U²Q1−V²Q2=−2PU sqrtQ1, squareagain. No divisions byP,U,V, so zerocoefficients arecovered. Extra roots introducedbysquaring mustnotbe mistakenforstationarypoints; evaluateallextraneousroots gives safeuppercandidatepool. IdenticallyzeroG requiresseparatehandling; do notclaimfinitepool then. Endpointvalues mustalso becompared. PhysicalpairseparationC840 boundsQi awayfromzero foractualpatches, andpositiveYj givesQi>0 throughoutnondegenerateHfiber.

Together withWIDTH-STATIONARY-POLYNOMIAL.md, atfixedfourouterparameters the exactfibermaximum canberepresented by endpoints and up to8+8+20 polynomialroots, exceptidenticallyzerocaseshandledseparately. This is NOT acertifiedglobalouteroptimization, norlicense to usefloatingroots asrootexhaustion. Parameterintervalisolation must include rootcoalescence andboundarycrossings.
