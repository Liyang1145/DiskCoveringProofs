# Closing the remaining metric gap by an explicit quadratic minorant

## Scope and inputs
All14site covers, r<=U=.33173203427623414. Inherited C1330 reduces them to fullgraph879; inherited C1366 bounds normalizedgapdeficits in its896vertex polytope. This note proves the missing metric implication, conditional on those reductions and local C1355. No symmetry or generalposition is added. Full16face/20anchor witnesssystem remains the feasibility object, although the lowerbound uses only40edges.

Use exact site relabeling production->literal [7,5,1,8,0,4,6,2,9,3,13,11,12,10] and anchor j->j+2mod10 (orientationpreserving). Every16face andownerpair checked exactly against catalogue879 in q10_adaptive_flow_fraction_audit.py. Retain literal faces0,2,3,5,6,8,9,11, drop4anchor edges atsites8,9. Necessaryconstraints remain; capgaps still inherited from FULLsystem.

## A large box, not a neighborhood guess
Reference th0 are explicitrational principalangles nearcandidate, with negativeangles forliteral5..9. Set delta=theta-th0 byonecommonrotation so sumdelta=0. Atproductionanchorj, mean-centeredangle is
 (j-9/2)L + D sum_i[((9-i)/10)-1_(i<j)] x_i,
where L=2asin(U), D=10L-2pi. Compare with th0 relabeledandunwrapped. Exactinterval evaluation overALL896vertices in C1366 gives |delta_j|<.004245<eps=.005. Affinity gives fullpolytopecoverage, not sampling. q10_current_angle_width.py/.json. No roundedcandidate defines this necessary domain.

Alternative independentrepresentation, removing finalvertexlistcompleteness fromboxentry: `q10_halfspace_angle_dual.py/.json` supplies20 rationalLPdualcertificates directlyfromthe128halfspaces N*x>=b,sumx=1,x>=0. For eachobjective c, explicit y<=0,lambda satisfy c=yN+lambda*1+e, so c*x<=y*b+lambda+max(e). FloatingLP onlyproposes y,lambda; exactFraction residualaccountsforallproposalerror. Independent `q10_halfspace_angle_dual_replay.py/.json` reconstructsidentities withoutoptimizer/producerimports orANYvertices and evaluates(L,pi,s)multi-affinecorners. It provesallangles<.004244853<.005 forEVERYpointofhalfspaceintersection. Thus finaldomainvertexcompleteness isnotneededforthisboxentry. Necessityofhalfspaces andpriorrootcoverageforexteriorcuts remainsinherited.

## Explicit balanced affine flow
Start with rationaltree-repaired z0,T from independentbaselineaudit; damp derivative by1/4 (notbaseflow). The saved newjet is exactly T/4, so balance D^Tz(delta)=0 for allangles. Put
 F(delta)=sum_e b_e(theta) dot z_e(delta)-U sum_e |z_e(delta)|,
where b=-A_j onanchorrows and0elsewhere. For fullfeasiblewitnesssystem withr<=U, balance andCauchy give F<=0. Allnumericaloptimizers are proposals only; no optimalvalue regularity/rank/KKTpremise.

## Norm minorant lemma (the central new representation)
For eachflow, z0=n u, |u|=1; w=Tdelta; let a=u.w, b=(Ju).w, and l=n-eps||u^TT||_1>0. Thebox guarantees n+a>=l. Exactly,
 |z0+w| = sqrt((n+a)^2+b^2) <= n+a+b^2/(2(n+a)) <= n+a+b^2/(2l).
The first inequality is sqrt(1+t)<=1+t/2 for t>=0. Therefore -U|z| has a uniform explicit quadratic lowerbound. This is NOT a Hessian bound and avoids norm-nearzero intervaldependency. l certifiedpositive, minimum>.00562379.

For ananchor term -A(th+d).(z0+w), separately expand:
 -A(th+d).z0 >= -A.z0 - A'.z0*d +(A.z0)d²/2 - n|d|³/6;
 -A(th+d).w >= -A.w - A'.w*d - |w|d²/2.
Unitcircle derivatives have norm1; these are Taylorintegral/Lagrange remainders with globalbounds. Use |d|<=eps, |w|<=eps sqrt(sum_k||T_k||_1²). Thus every term is bounded by explicitconstant/linear/quadratic expressions, INCLUDING mixedangle terms -d A'.Tdelta.

Sum the terms. Let C have capnormals e5-e4 and e0-e9. Add 3C^TC ONLY to the quadraticmatrix. Exactmatrixcertificate proves H>=.01I on sumzero subspace. The resulting valid bound is
 F(delta)>=f0+g.delta+.005|delta|²-1.5[(delta5-delta4)²+(delta0-delta9)²].
It is essential to KEEP the final negativepenalty; F is not replaced by F+penalty in the feasibility inequality.

RationalbasisV has sumzero andrank9. Both directed240bitinteger producer and independent55decimalFraction auditor find ||V^T(H-.01I)V-I||_infinity<3.874e-14<1. V comes from a floatproposal but itsrank andcongruence inequalities are exact. No sampledHessian or eigenvalue premise.

## Capgradient cancels the penalty
q=.03374975397719135 exactly. Let gcap=-q(C1+C2). Certified ||g-gcap||_1<5.067e-15 and f0>=-3.795e-17. Write t1=delta5-delta4,t2=delta0-delta9. Because theoriginalXowners give actualcyclicgaps<=L,
 t1<=L-(th0_5-th0_4+2pi), t2<=L-(th0_0-th0_9).
Both upperbounds are <=0 in the directedcalculation; each t>=-2eps=-.01. On thisinterval,
 -q t-1.5t²=(-t)(q+1.5t)>=0,
since q>.015. Hence F>=f0-eps*gradienterror+.005|delta|². Feasibility F<=0 yields
 |delta|²<=1.265464e-14 <(1e-6)^2.
Genericcode alsohandlesa tinypositive capupperbound byexplicitcaploss; herecaploss=0.

## Exactcandidate and existinglocal conclusion
q10_adaptive_local_bridge.py directlyevaluates C1167rootbox anchorformulas againsttrig(th0); eachchorderror<1e-14, hence liftedangleerror<2e-14 ontheidentifiedbranch. After the aboveonecommonrotation, allanchors are within2e-6 oftruecandidate. Fullsystem still has all16sharedwitnesses, so C1355 applies: no r<r*, and r=r* forcescandidatecenters up toallowedrigidmotion/relabeling. Attainment remains C1167.

## Evidence
Producer q10_quadratic_minorant_certificate.py/.json; independent q10_quadratic_minorant_fraction_audit.py/.json; q10_quadratic_global_bridge.py/.json; sourceboundanglewidth q10_current_angle_width.py/.json. All under lead/. Repro py -3 -B for each. Analyticindependentaudit requested existingstressmember; do notconfuse registry/workflow withtruth.

This closesmetricgap if inherited globalnecessity/localcertificates stand. Before globalcompletion, audit those interfaces and originalgoal; this note itself is not independentvalidation of allhistoricaltopologyclaims.
