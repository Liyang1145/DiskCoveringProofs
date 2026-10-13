# Local arbitrary-center route after C1175 — missing exact interface explicit

Numeric mechanism (not theorem): true10boundaryswitch squaredradii +14tightcircumradius²constraints,28sitecoordinates+R=r²,gauge X+y=0. `local_cover_kkt_probe.py` has18potentiallypositivemultipliers and6identicallyzero candidates, feasiblefloatKKTresidual1.1e−16. 10Dlinearcriticalspace haspositivefinite-differenceLagrangianHessian, min~.05474, stable3steps. All8boundedlocalperturbationruns returncandidate. No globalboundorlocalcertificate yet.

## Bearing exact stationarity issue
D2invariantpositiveconstraintorbits are3boundaryorbits+2faceorbits. SevenD2siteparameters(a,b,c,d,s,z,t). Reduced5orbitgradientmatrix numericallyrank4; s,z columnszero atroot. Notacceptabletoassumeexactrankfromnumeric. Needanalyticnullspaceexistence usingF=G=H=0, THEN intervalpositiveweights and SOSC.

Atcandidate, boundaryX/A squaredradius derivativewrt s iszero (maximal X arc). AZT facecircumradius derivativewrtz iszero (witness(z,r)); allpositiveconstraints havezero s,zgradients. Hence eachD2symmetricgradient effectivelyacts on5coordinates(a,b,c,d,t), plusR.
Threebasecontactconstraints canbeexplicitlysolved by
s=sqrt(1-r²), z=2a-s,
b=r+sqrt(r²-(a-s)²),
d=1-sqrt(r²-c²),
t=r+sqrt(r²-z²).
The5positiveorbitcontactequations reduceoriginalF=G=0 on(z,c,r) bysubstitution a=(s+z)/2. ExactH=F_zG_c−F_cG_z=0 ispreciselysingularity of2x2Jacobian in(z,c) atfixedr, hencea5orbitlinear dependence inphysicalcentergradients. Nonzero∂(F,G)/∂(c,r) andallbaseradicaldenominatorsguaranteeradiuscomponentnonzero. ThisproducesexactnormalizedKKTweights withoutintervals-containing-zero pretendingtoproveidentity. Needwritechainrulematrixexplicitly/checkconstraintscaling, andboundresultingweights>0 byintegerintervals.

## SOSC kernel target
UseexistingdirectedI kernel, extendJet dimension from3 to29 (newmodule, doNOTmodifycertifiedrootkernel). Boundaryswitch branch formula andtruecircumcenter squaredradiusrationalfunctions differentiable inneighborhood sincepairdifferences, line-circle discriminants,triangleareas strictlynonzero. Atroot activecontactsetstable; offbranchcandidatesstrictslackprovedC1167. ExactpositiveweightKKTandpositiveLagrangianHessian onnullspaceofpositive-gradientrowsplusgauge impliesstrictlocalcoverminimum (strongerthancriticalcone, sosufficient). Zero-multiplierconstraints onlyrestrictcriticalcone further.

Avoidintervalnullspace pitfalls: chooseexactrationalcoordinatechartbyanintervalnonsingulargradientminor, parameterizeM v=0 withfreevariables, thenintervalLDL/Cholesky ofNᵀH_LN on10D. Interval-overenclosureofroot isenoughforHboundonceexactKKT existence known. Needboundallmixedblocks; individualorbitscannotreplacefullquadraticform.

## Scope after completion
Wouldprove localoptimality amongARBITRARY14centers modulo rotations, notglobal. Doesnotsettle1000q10+1042q11 metricfamilies. Theproofmay neverthelesssupplyrigorousexclusionneighborhoodandrepairthecandidate-branchstationaritydependencyforlaterglobalcertification.
