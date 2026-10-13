# Exact intrinsic characterization of a unit cyclic polygon

Let a closed oriented polygon A_0,...,A_(q−1) have nonzero edges E_i=A_i−A_(i−1) (indices modq). Prescribe theta_i∈(0,pi), sumtheta_i=2pi, and assume |E_i|=2sin(theta_i/2). Suppose its signed exterior turn at A_i is (theta_i+theta_(i+1))/2 (in(0,pi)). Then all vertices lie on one unitcircle, in the prescribed cyclic order.

Proof: put t_0=0 and t_i=sum_(j=1)^i theta_j with indexorigin adjusted toA0. There is a rotation z, |z|=1, such that E_1=z(e^(it_1)−e^(it_0)), since lengths match. The model chord z(e^(it_i)−e^(it_(i−1))) has argument argz+(t_i+t_(i−1))/2+pi/2; its nextchord argument increments(theta_i+theta_(i+1))/2. Thus all modelchords equal E_i by induction. Summing gives A_i=O+z e^(it_i), O=A0−z. Closure followsalreadyfromsumtheta2pi, independentofextrinsicembedding. This also proves strictconvexity/winding1; it neednotbeassumedseparately ifsignedturnequalities hold.

Conversely anorderedunitcyclicpolygon with successive minorarcs theta_i∈(0,pi), sum2pi haspreciselythese lengths andturns. Ifonlyunsignedtriangleanglesknown, mustfirstproveactualsignedturn (noorientationbranchshortcut). CandidatetilingproofinBOUNDARY-ANCHOR-OUTSIDE-EDGE.md addresses thisforgenuinecovers.

Application: flat metric patch builtfromsite triangles + Voronoi facets + ownerwedge triangles yields intrinsicboundarysidelengthsL_i, theta_i=2asin(L_i/2). Localcyclicityconstraints
 2gamma_A+delta_u+delta_v=pi−(theta_u+theta_v)/2
 exactlyspecifythese turns whenpatchboundary isordinary(nonoverlapping). Hence localcyclicity+sumtheta2pi is sufficientforunitcirclegeometry onthatbranch. Theoremislocalrepresentation equivalence, NOTclaimanyangle/radiusassignmentembedsflatpatchglobally orhasemptycircumcircles.

Numericrankdiagnosticexplained: qlocalturn equations+oneperimeter addonlyq−3 independentconstraints to a closedflatpolygon atcyclic configurations; thetwo translationclosuredependencies andone angleturn sum are geometric. Forn14,q10 coupledprimal55variables,21oldconstraints, adding10cyclicityequations givesrank28atcandidate (27DOF). ThisrankcountisNUMERIC ONLY untilindependence/properflatpatchmanifoldproved. It is not used inpolygonproof.

Degeneracies: iftheta_i=0, collapsezerolengthedges first; limitinganglevariablescanretaindeletedwedges. Unitcircleconclusionforremainingpositiveedges bycontinuity, butq<3 degeneratepolygonnotclaimed inthisstrictlemma.
