# Interpolation slack: accepted identity, unproved uniform control

Object: two complete879 Cartesian incidence systems, candidate radius r*, feasibleendpoint r<=U; one common fixed gauge. x_e(t)=(1-t)x_e*+t x_e, for anchor edges x_e=c_v-A_j. b_j=(1-t)A_j*+t A_j, q_j=|b_j|>0, mu_j=(1-q_j)/q_j. For witness edges normalization cost Lambda=0.

## Analytic identities and sufficient condition

Exactly |x_e(t)|²=(1-t)|x_e*|²+t|x_e|²-t(1-t)|x_e-x_e*|². Normalizing b_j to b_j/q_j changes squaredanchorlength by Lambda_e=-2 mu_j x_e(t) dot b_j +(1-q_j)². Let R_t=(1-t)r*+tr. Since both endpointlengths bounded, normalizedsquaredlength <=R_t² -t(1-t)(|Dx_e|²-(r-r*)²)+Lambda_e. Therefore the peredge condition

 t(1-t)(|Dx_e|²-(r-r*)²)>=Lambda_e

is sufficient to interpolate without increasing radius. It is NOT necessary: endpointslack was discarded. Even if it holds, anchororder/oncewinding and gauge requirements must also be checked to apply C1281 and localfirstexit.

At a candidate activeanchoredge lambda_e=1-c_v* dot A_j*=(1+r*²-|c_v*|²)/2. For a smoothendpointmotion with anchorvelocity J A_j* phi_j and relativevelocity d_e, the leading SUF coefficient when r'=0 is |d_e|²>=lambda_e phi_j². This is only a tangent inequality. A vector in the linearized constraintkernel need not be a tangent of an actual feasiblecurve at r<=r*.

## Exact Xpair identity (not a sampled proof)

For X+=(s,0), A±=s±ir*, s²+r*²=1, rotate endpointpair+site by angle a. Write z=(1-t)+t exp(ia), q=|z|>0. Then c_t=s z, b±=(s±ir*)z, so

 |c_t-b±/q|²=|z/q|² |s(q-1) ∓ i r*|²=r*²+s²(1-q)².

The residual is fourthorder in a for fixedt. This identity is local to the rotatingpair; it does not build a feasible wholegraphendpoint or a global gaugeindependent localizationtheorem.

## Rejected inference interfaces in first member report

Memberreport members/stress-cc2/midpoint-rigidity/REPORT.md initially called floatingSVD/LP data exactrank, explicitexactflex and uniformobstruction. Those conclusions are not accepted. Requested revision:
- finitebasisvalues do not bound mixed directions;
- O(s³) without a remainderbound does not constrain amplitude;
- straightsite/witnesspaths are not all feasiblecurves (secondorder corrections matter);
- floatingrank/residual/LP are numerical diagnostics, unless exactanalyticdependencies separately prove the statements;
- no constantfactor upperlimit on improvedlocalcell follows from these diagnostics.

No registeredclaim depends on those unaccepted conclusions. Retain the exactSUF identity as a representation; the unresolved obligation is a quantified domainbound on gain minus repair, including allincidenceedges and endpointslacks, or an exact counterexample in the intended endpointdomain. The current data do not settle that obligation.
