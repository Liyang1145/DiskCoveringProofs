# Exact compact anchor domain at threshold U

For any normalized cover at r<=U, each owner arc has length theta_i<=L=2asinU<pi, because a radiusU disk intersectsS1 in an arc of length at mostL. This remains true after normalizing afreshatU. Anchors incyclicorder have gaptheta_i>=0,sumtheta_i=2pi. GaugeA_0=(1,0). Set d_i=L−theta_i. Then
 0<=d_i<=L, sum d_i=Delta_q=qL−2pi.
Anchorangles t_j=jL−sum_{i<j}d_i (chooseindexconventionconsistently).

Atq10: 0<Delta_10<L since9L<2pi<10L (directintervalcheck requiredbelow), so allupperbounds d_i<=L areredundant. The fullanchor-domain is exactly a 9-dimensional simplex with10vertices d=Delta_10 e_i. Inparticulareveryarc ispositive with theta_i>=L−Delta_10=2pi−9L. ThereareNOzerogapanchor degeneracies inq10 belowU.
Atq11: L<Delta_11<2L since9L<2pi<10L. The 10-dimensional clipped simplex hasvertices withonecoordinateL, anotherDelta_11−L=Delta_10, allothers0:110orderedvertexchoices. This follows standardpolytopevertexcriterion: atmostonecoordinate strictlybetween0andL. Zerogaps areallowed here. Bothdomainscontainallnormalizedcovers; candidateboxesmayfurtherrestrict butnothingelseisneededfortheouterdomain.

## Balanced-flow lower bounds on the angular simplex
Let g_j=−b_j be the anchorcoefficients of anexactbalancedflow. The fixedanchor lowerboundnumerator is F(d)=sum_j g_j·(cos t_j(d),sin t_j(d)).
If each term remainsnonnegative throughoutagivenconvex d-polytopeQ, its Hessian is −[g_j·A_j(d)] gradt_j gradt_j^T, negative semidefinite. Thus F isconcave onQ and F(d)>=min_{v∈verticesQ}F(v). Afterdividingbytheupperbound onflow-normsum thiscertifiesallanchorsinQ usingonlyvertexevaluations, NOT sampling. This is a proved reduction: concavity hypothesis must itselfbeproved overwholeQ (anintervaldotbound suffices). Separatepositiveblocksarenotbeingcombined; displayedHessian isfullsum ofnegative rank-one matrices.

Whenconcavityfails, a genericrigorous alternative is Taylor's lowerquadratic bound atd0: eachanchor term has second derivativeinitsangle boundedbelowby−||g_j||, giving
 F(d)>=F(d0)+gradF(d0)·(d−d0)−(1/2)sum_j ||g_j||(t_j(d)−t_j(d0))².
The RIGHTSIDE isconcave in d globally. ItsminimumoverQ isatavertex, yieldingasafevertexbound withoutassumingconcavityoftheactualF. Exact/intervaltangentcoefficients andnormupperboundsaremandatory. It canalsobeapplieddirectlyinanchoranglecoordinates where polytopeverticestransformaffinely. Barycentricsimplexsubdivision can thereforeuse the elementaryflowdual withnoradius-eliminationNewtonor38-variableclosuresearch.

No actualconfiguration isexcludedbythisnote. Fixedflowvertexbound may beweak; ifso adaptflow/partition geometrically. The benefit is exact finite-dimensional outerdomain and rigorousinterpolationremainder, not sampledcontinuumclaims.

## Precise conventions and certification
Arcindices are0,...,q−1; theta_i is gapfromA_i toA_{i+1}; t_0=0, t_q=qL−Delta_q=2pi. GaugeA0=(1,0); allflowsuseit. Subtracting2pi fromindividual t_j andt0_j together changesneitheranchorvalue norTaylorinequality; implementations dothisforanglesoriginallynegativefromatan2.
U isALWAYS exactdecimal .33173203427623414, NOTanoutputduallowerbound. Both `anchor_simplex_certificate.py` (240-bitdirected) and `anchor_simplex_fraction_replay.py` (independentFractions/Machin+asinseries) assert2pi−9L>0 and10L−2pi>0. Noextra numericalassumption. The flowlower.3477467 appliesONLYtotheanchorregiondefinedatthisU; no claimglobalboundsatlargerthreshold.
Here 'exactdomain' means exactlythe gapinequalitypolytope, NOTallpointsarerealizablecovers; geometry⇒domain isnecessary only. For q10 the redundantboxinequality isd<=L (theta>=0), NOTd>=0. AtU=sin(pi/9) thepolytope remains9-simplex; zeroarc occursatitsvertices, domain doesnotcollapse. Hessian signsforallterms areSUFFICIENT, notnecessary, forconcavity; t0constant contributeszerogradient. Taylor's −1/2 norm dt² hasHessian−norm gradt gradt^T, andweightsarenonnegative.
