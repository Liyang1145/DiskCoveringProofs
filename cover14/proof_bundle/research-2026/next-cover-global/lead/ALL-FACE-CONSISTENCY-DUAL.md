# Simultaneous local-face envelopes, not edge-disjoint packs

For each genuine triangularface f, A_f=sum_{e incident f} a_e, where a_e=RfT sin beta_e is itspairedfacetarea. Localexact/sharedradius upper E_f(beta_f)>=A_f fromC1227 andlowerbranchlemma. For anynonnegativeweightsw_f withc_e=1−sum_{f incident e}w_f>=0:
 totalpairedarea=sum_f w_f A_f+sum_e c_e a_e
 <=sum_f w_f E_f(beta_f)+sum_e c_e U²sin beta_e.
Noedgeisdoublecounted; boundaryedgeshaveoneface, interioredgestwo. Allfacesw=1/2 islegal. Weight0 permitted.

Let y_v be siteanglepotentials; arbitrarilyallocatep_fe tofaceincidences. Setp_e=y_u+y_v−sum_{f incident e}p_fe. Then
 totalpairedarea−sum_e(y_u+y_v)beta_e
 <=sum_f sup_beta_f[w_f E_f−sum_{e inf}p_fe beta_e]+sum_e sup_beta[c_e U²sin beta−p_e beta].
Combine boundaryjointcornerduals exactlyasbefore. Thisisfactor-graph Lagrangedual; arbitrarysignedp_fe retained. Edgeconsistency doesnotrequirepositivepotentials. SampledLP canjointlychooseweights,potentials,supports becauseallconstraintslinearinthedualvariables. SampledLPisproposalONLY.

Structuraldifferencefromfractionalfacepacks: faceincidencepotentials canredistributefreelywhilepreservingtotaledgepotential; constraintsfromALLtrianglesactive simultaneously. Edge-disjointpacksareincludedasspecialchoices. Eachfacecontinuumsupportstill3D, notfull29D.

Certificateinterface: forw_f>0, reuseexactfaceboxboundwithpotentials p_fe/w_f thenmultiplybyw_f. Forw_f=0, usesafeexactlinearboxsupport (orB<=2pi polytope). Residualedgescoefficientc_e>=0 useconcavesinetangent. Boundarykernelunchanged. Roundingweightsdownpreservescapacity; potentialsarbitraryrational. NeedfullpartitioncoverageperfaceandFractionreplaybeforenegativeclaims.

Boundedmechanismtest: candidate+sixclosestremainingcases, compare sampledLPgap andthenintervalcertificationonlyifproposalsmeaningfullyimprove. Notagloballowerboundandnotmetricrealization.
