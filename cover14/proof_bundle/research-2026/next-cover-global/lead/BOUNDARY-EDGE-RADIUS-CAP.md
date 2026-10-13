# Boundary-edge radius cap using normalized site cone

For existence arguments at thresholdU, anycoveratr<=U isalsoaU-cover. ApplyC1171 innerrootnormalization afreshatU (graphmaychange; existentialcatalogueallowsit). Henceallsitesnorm<=s=sqrt(1−U²) andfacetendpointdistances<=U inconstantgraphlimit. Workwiththatrepresentation, notoriginalr-normalizedgraph.

AtunitanchorA, bothsitevectorsu−A,v−A lieinradialconehalfangleacosU. Theirangle2gammaA therefore<=2acosU (fromboundaryhA<0 proof). Thus gammaA<=acosU. Withx=Rf/U,y=anchor_radius/U,beta∈(0,pi):
 gammaA=atan2(x sinbeta,y−x cosbeta),
 so y>=x[cosbeta+k sinbeta], k=U/sqrt(1−U²).
IfD(beta)=cosbeta+k sinbeta>1, infer x<=1/D andxy<=1/D. D>1 exactly0<beta<2asinU. Boundarypairedarea therefore
 Q_e<=U² sinbeta min(1,1/D(beta)).
This improvesordinaryU²sinbeta onlyforsmallboundarybeta. Exactsharpnessofthelocalendpointbound: y=1,x=1/D saturatestheconeangle; no globalembeddingassertion.

Simultaneousfaceenvelope: whenevera facehasboundaryedge e, itscentralradius x<=1/D(beta_e). CombinewithC1227rootupperand x<=1. For anybox, compute lowerboundD_e thenX<=min(1,1/D_lower). ThenA_f<=U²Xsum sinbeta. This maytightenupperANDlowerbranches safelywithoutchangingtheirproofs. D concavewherepositive; onbeta∈[0,pi], D''=−D, D maynegativeforlargeangles. To boundminimumonsmallbeta interval useendpointminimum (Dsinglemaximumon[0,pi]); trueglobalminintervalatendpoint becauseonlystationarypointatan k ismaximum.

Independent kernelcheckneededbeforecountpromotion; localconeproofandfixedU-normalization bridgependinganalyticreview. Numericprobe shouldcompare sixsurvivors, notblindscale.
