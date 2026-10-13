# Adaptive balanced flow enlarges the effective local entry cell

## Object and scope
Unit disk, Euclidean radius, arbitrary positions, literal graph879 relabeling in fixed-anchor-convex-probe.json. Retain faces0,2,3,5,6,8,9,11 and allanchor incidences, then remove sites8,9 and their4anchor edges. These deletions are relaxations; every original witnesssystem satisfies the40remainingedges. No symmetry of unknown configuration assumed. Candidate C1167 is used only for reference/local theorem C1355.

Angles use principal lifts near the savedreference: anchors0..4 positive,5..9 negative. Actual cyclic gap4 is theta5-theta4+2pi; gap9 is theta0-theta9. Other gaps continue in their obvious order. A commonrotation is free. Choose it so delta=theta-th0 has sumzero, where th0 are explicit rational angles in q10-adaptive-flow-interval.json.

## Explicit function and lower-bound interface
For core incidence D (freepointcolumns) and anchor offset b_e(theta)=-A_j(theta) on boundaryedges,0otherwise, the saved rational affine flow is
 z_e(delta)=z0_e+T_e delta.
Every coefficient is checked EXACTLY balanced: D^Tz0=0 and D^TT=0 separately forbothCartesiancomponents. Thus for any realization whoseedge norms<=r<=U,
 F(delta):=sum_e b_e(theta) dot z_e(delta)-U sum_e |z_e(delta)| <=0.
This uses only triangle/Cauchy inequalities, not optimization, stationarity, exactcandidateweights, or differentiability oftheoptimum. Rationaltree repair gives a soundexplicitflow even if optimizerproposal inaccurate.

## Hessian theorem
On |delta|inf<=3/100000, sumdelta=0, everyflow norm is strictlypositive. The savedintervalcomputation and separateFraction replay prove
 h^T Hess F(delta) h >= (1/1000)|h|² for every h with sumh=0.
For normterm use exact identity Hess_z|z|=(Jz)(Jz)^T/|z|³ in2D. For anchor term -A_j(theta_j) dot z, the second derivative is
 A_j dot z * h_j² + 2 h_j * (-A'_j) dot (T h).
This includes ALLmixedterms. Angles are bounded by the elementary Lipschitz |cos(t+d)-cos t|,|sin(t+d)-sin t|<=|d|. BasisV has exactzero columnsum andexactrank9. The intervaltest proves V^T(HessF-.001I)V positive: rownormdistancefromI<.878335<1, with exact rationalupperbound saved. This proves continuum positivity, not sampled positivity. Produceruses240bit directedinteger arithmetic; auditor uses55decimal directedFraction operations andindependent80term Taylortrig. Sharedformula is disclosed; sourceedges rebuilt by auditor. Optimizedjet/Hessian diagnostic eigenvalues are NOT premises.

## Gradient + cap inequalities localize every feasible system
The savedconstant has F(0)>=-3.795e-17. Let q=.03374975397719135 exactly and
 gcap=q*(-1,0,0,0,1,-1,0,0,0,1).
Certified l1error |gradF(0)-gcap|_1<7.724e-15. Maximum boundarygap<=L=2asin(U), sinceadjacentanchors sharea disk inoriginalgraph (includingdeletedXsites). Consequently
 gcap dot delta >= q*(th0_5-th0_4+th0_0-th0_9+2pi-2L).
Directedpi/arcsine intervals give rightside >=1.80035e-17. It is legitimate to usecapconditions inheritedfrom originalgraph despite deletingtheXsites intheflowproblem.
Taylorintegral alongthe segment inmeanzerosubspace gives
 0>=F(delta)>=F(0)+gcap.delta-eps*gradienterror + .0005|delta|².
The exactreplay obtains |delta|²<=4.033981e-14, hence |delta|<1e-6 (actualboundabout2.009e-7).

## Entry into existing local theorem
Directrootbox expressions (C1167) enclose truecandidateanchorcartesiancoordinates. Independent rationalangle trigbounds give referencepointchorderror<1e-14 for eachanchor; near-chordangleerror<2e-14. Thus the abovefeasibleanchors lie within2e-6 oftruecandidate after onecommonrotation. C1355 applies: r>=r*, and equalitygives candidateuniqueness inthiscell, modulo its existinggauge/relabeling.
A convenient candidate-centered statement is: if mean-centered liftedangle displacement fromcandidate has supnorm<=.00002999, then aftergauging toth0 thedifference is<.00003 (reference mean-centererror<4e-14); conclusion holds. More intrinsically use the exactrational th0 cell directly. This is ~15times priorentry width, NOT full remainingdomain exclusion.

## Evidence/repro
- q10-adaptive-flow-interval.json: explicit rationalflow,jet,basis, Hessianintervals andexactrowbound; q10_adaptive_flow_interval.py 3/100000.
- q10-adaptive-flow-fraction-audit.json: independent balance/incidence/basisrank/arithmeticreplay; py -3 -B research-2026/next-cover-global/lead/q10_adaptive_flow_fraction_audit.py .
- q10-adaptive-local-bridge.json: exactTaylor/cap/rootcomparison; py -3 -B research-2026/next-cover-global/lead/q10_adaptive_local_bridge.py .
- q10_adaptive_flow_jet.py and q10_adaptive_hessian_control.py propose/calibrateonly. RandomHessiantests do notcertifyanything. NoKKTbranchcoverage required for thisexplicitflow proof.

Remainingimplication: show every remaining879configuration is inthisenlargedcell, or exclude its complement. C1366 domain is still larger. Goal NOTcomplete.
