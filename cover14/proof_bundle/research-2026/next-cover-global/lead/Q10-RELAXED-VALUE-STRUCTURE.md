# Positive-support relaxation: valid route and bounded control

Keep all20anchor incidences and8positive faces of literal fixed-anchor-convex-probe ordering: 0,2,3,5,6,8,9,11. Delete otherfaces. This has44edges, not52. Value Vrel(theta)<=V879(theta), so a lowerbound onVrel is sufficient without showing deletedfacesinactive.

## Exact decomposition at arbitrary fixed anchors

Sites8,9 occur in no retainedface. Each has exactlytwo anchorconstraints: owners8 at anchors4,5; owners9 at9,0. Eliminate eachfreeXsite independently by the elementary smallestdisk containingtwoanchors. Thus
 Vrel(theta)=max{ |A4-A5|/2, |A9-A0|/2, Vcore(theta) }.
Vcore is the remaining12sites and8witnesses problem with24faceedges and16anchor edges. Sharedanchor terminal locations mean these three functions are not functions of disjoint anglevariables. The decomposition does NOT authorize independent rotations ofanchor subsets whileholdingVcorefixed.

This removes the two Xpair degeneracies before any branch analysis. Work with squaredradius rho andconstraints |e|²<=rho. For strictlypositive edgeweights in thecore, the site/witness Hessian of theLagrangian is a weightedDirichletLaplacian tensorI: positive definite whenever every free connectedcomponent reaches a fixedanchor throughpositiveweightedges. This is independent ofedge directions. However an explicitcoreKKTbranch additionally requires certifiedweights/activeconstraints and a constraint-qualification/rank or suitablequotient argument. RawprimalconstraintJacobian is NOTfullKKT; no branchregularity follows from itsrankalone.

## Numerical control (not proof)

lead/q10_relaxed_anchor_probe.py uses existing analyticnorm-Jacobian SLSQP solver, checks44rows andlegalorderedgaps, and explicitlyPERTURBS ANCHORS. Savedcalibration is anapproximation, notexactroot. Sevenboundedsolves:
- control Vrel-r* =1.1e-16;
- rotateXpluspair by1e-4/1e-3: +4.90328e-9/+4.90340e-7;
- moveone noncapanchor by1e-4/1e-3: +2.44924e-6/+2.46016e-5;
- shrinkXpluscap by1e-4/1e-3: +6.75246e-6/+6.77510e-5.
No continuumconclusion/noexactduality claimed. This only calibrates intendedobject andmakesa reducedcorebranch worth investigating; no-descent onthree directions does notprove localminimum.
Evidence q10-relaxed-anchor-probe.json/log/err. Repro py -3 -B research-2026/next-cover-global/lead/q10_relaxed_anchor_probe.py .

Member shared-radius relaxed-value report usedwrongrowcount/fixedanchor-sitejitter andwasquarantined beforeclaims. No mathematicalroutekilled by that instrumentfailure.

## Core active-set compatibility diagnostic

q10_core_dual_control.py/.json uses the actualcore J40x41 and KKT81x81 (stationarity included). LP findspositivecorestress withminimum .0080726, stationarityresidual1.9e-17; freeHessian mineigenvalue .0214174. YetKKTsingularvector is purelydual numerically, notfreepointflex. J hasoneleftdependency numerically. Itsanchorcompatibilityrow is approximately
 (0,.1749582,-.3125745,.1749582,0,0,-.1749582,.3125745,-.1749582,0).
Thus attempting tokeepALL40coreedgesactive onarbitraryanchorperturbations has a firstordercompatibility condition; do notsolvea single smooth allactivebranch bydeletinganequation withoutcheckingthe omittedconstraint. Theunknowncorevalue mayrequirebranches/activechanges. This is distinctfrom witnessLaplaciansingularity; apositivecorestress exists numerically.

AselecteddualfromSLSQP initially hadsomezeroedges, but this doesNOTmean everydual hasthosezeros; maxminimumLP repairs thatdiagnostic. Stressnullintervalendpoints numericallyzeroentireouterfaces, suggestingpiecewiseactivebranches. Exactcertification ofdependence/branchcoverage stillmissing.

Added namedC1175fixedstress-obstruction direction toboundedprobe: Vrel-r* is +1.6710e-8 atstep1e-4 and+1.67122e-6 at1e-3. Thus fixedstressnegativecurvature doesnotnumericallytransfer tooptimizedrelaxedvalue. Total9solves, no scaling/grid. This supportsworkingonvariabledual/corebranches, NOTtryinganotherfixedstress. Allnumbersnumeric-only.
