# Exact boundary-center elimination, with reverse arc coverage

This completes the necessary parametrization in BOUNDARY-ANCHOR-PARAMETRIZATION.md. It is a representation theorem, not a global lower bound.

Fix U<1/3, s=sqrt(1−U²), q∈{10,11}, m=14−q. Fix rotation A0=1. Choose strictly positive successive arc gaps theta_i<=2asinU, sumtheta_i=2pi, giving ordered unitanchors A_i. Choose shared nearest distances a_i∈[1−s,U]. For each boundaryowner between A_(i−1) and A_i, put L_i=2sin(theta_i/2), e_i=(A_i−A_(i−1))/L_i and inwardnormal n_i. Define
 t_i=(a_(i−1)²−a_i²+L_i²)/(2L_i),
 h_i=sqrt(a_(i−1)²−t_i²),
 c_i=A_(i−1)+t_i e_i+h_i n_i.
Require radicand>=0 and |c_i|<=s. There is no assumption 0<=t_i<=L_i. Hidden m centers remain free in |c|<=s. Anchor distances and the inward branch determine each boundarycenter uniquely (h=0 allowed).

## Reverse boundary-cover assertion
Every disk B(c_i,U) covers the entire minorarc A_(i−1)A_i, not merely endpoints. Proof: both endpoints lie in the disk byconstruction. A radius U<1 disk cuts S1 in one closed arc of angular length atmost2asinU<pi (ifintersection nonempty with distinctendpoints). This arc contains both endpoints, so contains their unique minorarc. Hence the union of the constructed q disks covers all S1. No all-other-site nearest test is required for this boundarycoverage conclusion; it IS required if asserting these are exactlythe Voronoi ownershiparcs.

## Exact interior-cover check
For a given full set C of14 sites (duplicates merged for this check), boundary alreadycovered. It covers D iff every interior vertex of the clipped Voronoi diagram has nearestsite distance<=U. An interiorvertex is an empty circumcenter of at leastthree noncollinear sites. Finite predicate: enumerate all noncollinear site triples; whenever their circumcenter O lies inD and allothersite distances>=the triple radius, require radius<=U. Boundaryvertices/smootharcs arecovered byprevious paragraph. Proof: on each compact convex clippedcell squared distance to its site is convex; its maximum occurs on extreme boundary, comprising circlearc points or straightedge endpoints. If a cell has no interiorvertices, only circlearcs/endpoints matter. Equivalent no-uncovered-interiorlocalmaximum argument available. Collinear/duplicate degeneracies do not create an additional interior vertex type; cocircular triples merelyduplicate checks.

## Global implication and limits
Every normalized14cover yields such data with itsq actualpositiveowners, byinnerchordside andcommonanchor distances. Originalzeroarcs/singletons handled withoutwardclipping andcompactlimits; to avoiddivisionbyL=0 retain polynomial relations or limits ratherthan the displayedquotient. Conversely anystrictparameterdata satisfying thefiniteinteriorcheck produces anactualcover, whetherornot proposedq arcs coincidewith nearestownership. Thus this is anexactrepresentation on strictbranch, plusnecessarycompactclosureforglobalproof.

Dimension atfixedU,modrotation: q−1 gaps+q anchorradii+2m hiddencoordinates=27. This agreesfullcoordinatecount, unlike55-radiusvariables/21constraints relaxation. Commonanchors enforceglobalcyclicity fromtheoutset. Degeneratebranch canbehandledwith implicitrelations (a_prev²=t²+h², a_next²=(L−t)²+h², h>=0) withoutdivision.

Candidate calibration boundary_parameter_control.py reconstructs all10 boundarycenters to6e−16. Equalanchorstratum a_i=U isnotWLOG: proving it globally remains open. Numericalsolver success or smallresidual isnot acovercertificate; finitepredicate and exact/intervalhandlingstillrequired.
