# Combine shared-radius face envelopes with coherent real-angle system

Variablesgamma_(f,e) oppositeedges, gammaA_e boundaryvirtual, beta_e. Linearnecessaryrelations:
(1) sum_einf gamma_fe=pi for everyrealface;
(2) gamma_fe+gamma_ge+beta_e=pi interior; gamma_fe+gammaA_e+beta_e=pi boundary;
(3) at hiddenv sum_fcontainsv gamma_(f,oppositev)=2pi;
(4) at boundaryv sum_fcontainsv gamma_(f,oppositev)+alpha_v−sum_boundaryeincv gammaA_e=pi.
Allgamma_fe∈[0,pi], gammaA∈[0,pi/2] (C1250). Existingbeta siteledger isretained. Theseaddmetricflatnessangledatadroppedbyperfaceenvelope; no claimlinearrelationssuffice.

AddLagrangemultipliers a_f,b_e,t_v for(1),(2),(3/4). Letlhs−rhs convention andsubtractallfromobjective. Then
- beta_e coefficient gains−b_e;
- boundaryalpha_v gains−t_v;
- realgamma_(f,e) hascoefficient−a_f−b_e−t_(oppositev);
- boundarygammaA_e coefficient−b_e+t_u+t_v;
- constant adds pi sum a_f+pi sum b_e+pi sum_boundary t_v+2pi sum_hidden t_v.
Supovergamma boxes becomes pi max(0,−a_f−b_e−t_opp) perrealincidence, (pi/2)max(0,−b_e+t_u+t_v) perboundaryedge.
Thus add linearhingevariables toexistingfactor-dualLP. Facelocal E_f(beta) supportsuseindependentlyallocatedp_fe unchanged. Residualedge beta potential becomes y_u+y_v+b_e−sum p_fe. Boundarypotential becomes y_v+t_v. Allcoefficients rationalproposals, exactcertificatecanreuse kernelsplusfinitehinges.

Notice faceangle sumconstraintsalreadyintrinsictoE_f but coherentgamma_arekeptasadditionalexistentialvariables; relaxation mayloosebecausegamma maximizinglinearhinges neednotmatchradiusparameters usedinE_f. Validnevertheless, candidatecontrolrequired. Bounded6+candidate comparisonfirst; ifallmultipliersunhelpful stopscaling.

## Analytic dependency diagnosis (after bounded probe)
The vertex real-angle equations are IDENTITIES once face sums, edge gamma+gamma+beta=pi and existing beta-ledger hold. At hidden degree d, sum incident beta = d*pi − [(d*pi)−sum gamma_at_vertex] = sum gamma_at_vertex. At boundary degree d there are d−1 faces, so sum incident beta = pi+sum gamma_at_vertex−gammaA_prev−gammaA_next. Thus no extra flatness constraint is added by those vertex rows! Only existence of a positive coherent gamma assignment (including gammaA<=pi/2) could tighten projection. Bounded candidate+6 LP all unchanged within2e−15; do not scale this representation unchanged. This diagnoses exactly why adding apparent new equations has no leverage; they must be coupled NONLINEARLY to shared radii or to cyclic boundary endpoints.
