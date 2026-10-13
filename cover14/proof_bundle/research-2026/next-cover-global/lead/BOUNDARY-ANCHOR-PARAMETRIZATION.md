# Exact boundary-owner elimination using unit-circle anchors — draft

Scope strictnormalizedcovers withqpositiveowners, cyclicswitchanchorsA_i∈S1, consecutiveangular gaps theta_i∈(0,2asin r], sumtheta=2pi. Sharedanchorradii a_i=|A_i−c_i|=|A_i−c_(i+1)|∈(0,r]. Everyownercenter liesoninnersideofitsanchorchord, bynormalization|c_i|<=sqrt(1−r²)<=cos(theta_i/2).

Forowneri betweenA_(i−1),A_i putL=|A_i−A_(i−1)|=2sin(theta_i/2), e=(A_i−A_(i−1))/L andinwardnormaln pointingtoorigin. Thenuniquecenteroninnerside:
 s=(a_(i−1)²−a_i²+L²)/(2L),
 h=sqrt(a_(i−1)²−s²),
 c_i=A_(i−1)+s e+h n.
Requires |a_prev−a_next|<=L<=a_prev+a_next; alsos>=0and<=Lnotassumed. Innernormconstraint mustberetained: chordinnersidealoneweakerthan|c_i|<=sqrt(1−r²).

Necessity exact bytwocircleintersection, includingh=0 bylimit. Reverseconstruction doesNOTbyitselfgive nearest-ownedarcs orcover; mustcheckall-other-site anchornearest andcellfaceconstraints. Atstrictnormalizedconfiguration, samearcconnectedness lemma plusanchorsnearestoneachowner andarccoverage couldsimplifyboundaryownership, butnotassertedwithoutaudit.

Variables afterglobalrotation: q−1 arcgaps + q sharedanchorradii +2m hiddenpositions =2q+2m−1=27 forq+m=14. Atcandidate alla_i=r* (verify separately), soactiveboundarystratum reduces10variables. Global assumptionalla_i=r isUNPROVED. Needtestwhetheranyfreeanchorcanbeeliminatedbyamonotonecoverpreservingdeformation; boundarysaturationwouldremoveqparameters butmayfailduetointeriorcontacts.

Potentialcertificationroute: branchonarcgaps+anchor-radiusdeficits. Saturatedcandidate boundaryfamily maypermitconcavecover-capacitybound; nonsaturatedbranches payexplicitperimeterloss. UnlikeindependentwedgeLP, common a_i couples neighboringownercenters exactly. Suchcouplingisalreadyvisibleinlocalcyclicityequations butthisformulaeliminatesboundaryclosureautomatically, avoidsrankdeficiencyfrom31angleequations.
