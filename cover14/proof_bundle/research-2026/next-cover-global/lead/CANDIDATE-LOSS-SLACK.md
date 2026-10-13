# Candidate calibration exposes the next bearing gap

`candidate_slack_decomposition.py/json`, numeric diagnostic on savedactualrationalcover:
- exactgeometricarea reconstruction residual0atfloatprecision;
- boundarycornerarea slack≈7.6e−17 (essentiallytight);
- oldedgearea budget exceedsactualpairedareasby0.01922463202573166;
- bestintegralpack ofpresentlinearface-lossbounds recovers0.007226840252262487;
- remainingactualpointslack≈0.01199779. So presentface-lossrelaxation is not expected tosharplycertifycandidateclass, regardlessofbetterdualoptimization. Numericobservation, notyetintervalmethodimpossibility.

All14tightfacecircumradii≈r*. Two slackfaces [4,6,12] and[5,7,13] haveR≈.32082085460538173. ALL6positiveedgedeficits touchthese2faces. Thisisstructurallyuseful: exactradiusratio relation, ratherthanweaklinearloss, can potentiallyremovealllossatcandidate.

Exactedgeidentityatmaximalradius:
 D_e/U² >= 2sinβ·τ/(1+τ), τ=tan(β/2)|tanΔ|.
Equality iff max(endpoint radii)=U. Thisholdsforallsixcandidatepositive-lossedges(otherendpoint istightfaceorboundaryanchor).

Next structural obligation: retain exacttau-edgecost and realfaceanglebalances insteadofreducingto minedgecoefficient. Forface, signedΔ_e withΣΔ_e=(Σβ−π)/2 and |Δ_e|<=(π−β_e)/2. OptimizeinfΣ 2U²sinβ_e tan(β_e/2)|tanΔ_e|/(1+tan(β_e/2)|tanΔ_e|). Ignoring commonRf isstillrelaxation; incorporatingitmaybenecessary. Costnonconvex: secondderivativeford>=0has sign(tan d−tan(β/2)), so doNOTassertglobalconvexity/Jensen. Exactlinearlossboundisprovenlowerenvelopebutnottightenoughnearactualpoint.

Nooptimumclaimfromthisdiagnostic; fullclasspruning continues separately.
