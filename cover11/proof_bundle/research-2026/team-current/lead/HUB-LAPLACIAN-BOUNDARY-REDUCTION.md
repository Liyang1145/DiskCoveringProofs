# A subharmonicity route to eliminate interior hub maxima

Fixedouter(r,b1,b2), objective F(X)=linear+sum[a_j theta_j+beta_j L_j²+gamma_j L_j], gamma_j<0,beta_j>0, sameC858convexhubdomain. AwayfromQ_j theangle is harmonic, Delta theta_j=0; in2D Delta L_j=1/L_j,Delta L_j²=4. Thus EXACTLY
 Delta F = 4(beta1+beta2) - |gamma1|/L1 - |gamma2|/L2.
Unlike Hessianconcavity thistrace calculation accounts for bothdirections and needs noangleHessian estimate. StrictpositiveLaplacian prohibits interior localmaxima (trace ofnegative semidefiniteHessianwouldbenonpositive), and nonnegativeLaplacian givesmaximumprinciple onbounded connecteddomains.

Let d=|Q1-Q2|,u=2r; actualfacebounds giveLj<=u and triangleinequalityL1+L2>=d. If d>u then bothLj>=d-u>0. To maximize c1/L1+c2/L2 overthisrelaxation, monotonicitypushestoL1+L2=d; theconvexonevariablefunction attainsmaximumatendpoints. Therefore
 c1/L1+c2/L2 <= max(c1/(d-u)+c2/u,c1/u+c2/(d-u)).
If 4sum(beta) exceeds this quantity, DeltaF>0 onENTIREC858domain andsupremumoccurs onitsboundary (or boundaryofclosure, withcontinuitychecked). This removes BOTH hubcoordinates in favorof finitelymanyboundaryarcs, withoutassumingridge; differentarcpoints may maximize(C860).

Exact d²=4r²[(sinb1 cosb1-sinb2 cosb2)²+(sin²b1+sin²b2)²]. In T=b1+b2,D=b1-b2, sin²b1+sin²b2=1-cosT cosD and sinb1cosb1-sinb2cosb2=cosT sinD, so d²/(4r²)=1+cos²T-2cosT cosD. Do NOT confuseQsitecenters withtheface-diskcenters: thelatterhavedifferentdistance.

Ifcriterionholds, potentialboundarypiecesarethethreecirclearcs andwedge-lines. Thewedgeisopen but closuremay beincluded forupperbounds. Since actualC848facespositive anduniformsiteseparation, needverifyFcontinuity onclosure: Lj>=d-u ensuresnonzero; angleYj>=0continuityrequiresavoidnegative-axisjump (branchfromupperhalfplane iscontinuousincludingnegativeaxiswiththeta=pi).

Scope: sufficientfixedoutercriterion, notallouterdomain. It can certifyabearingregionuniformlyby directedbounds onr,b1,b2. Failingcriterionisnotcounterexample toboundarymax. Candidate next calibration: computeexactcriterion onlocalQ0 andb1,b2>=a, then deriveparameterthreshold analytically.
