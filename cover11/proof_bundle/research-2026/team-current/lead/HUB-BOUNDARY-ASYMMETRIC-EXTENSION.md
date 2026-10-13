# Asymmetric boundary reduction via a single distance invariant

Extend C861 to alllegalC848/C849bearings satisfying
 **sin²b1+sin²b2 >= 69/50**.
This condition replacesbj>=1, includesasymmetricpairs, and remainsonlyasubfamily ofsector2.

The proof isidentical except d>=2r(sin²b1+sin²b2), so d-u>=2r*(19/50). Therefore
 DeltaF>=4(beta1+beta2)-(4/3)max((50/19)c1+c2,c1+(50/19)c2)
       >.04761102216066>0.
This is uniformr∈[3/8,19/50]. Alternatively onecanuse thelargerexact-distancecondition d>= (69/50)*2r (the sine-squarecondition is merely sufficient), where
 d/(2r)=sqrt(1+cos²T-2cosT cosD),T=b1+b2,D=b1-b2.
The EXACT-DISTANCE conditionis thestatement; itcoversatleastthe sine-squarefamily and C861.

Wedgeexclusion extendswithoutbj>=1: legalpositivewidthg requires bj>=bmin(r,g)>acosr/2. Thus x0=2bj-acosr>0 and x0<=acosr<pi, so |cj|²-(1-r)²=2r(1-cosx0)>0. Atwedgeedge thefacecircumradiusconstraint Lj<=2r sin(Aj) forcesLj=0, hencehub=cj outside normdisk. The v=0edge excludedby s>1-r. This compactness/smoothnessproofholdsforalllegalC848bearings; underd>=1.38u we additionallyhaveLj>=.38u>=.285, makingangleoriginsimpossible.

An operationaldomain split is thus:
- boundaryregion d/(2r)>=69/50: optimizeonly3diskarcs;
- complement d/(2r)<69/50: generalhuboptimizerstillneeded.
A parameterbox whollyinsidefirstregion permitsboundarykernel. Straddlingboxes requiregeneralbound orsplit; cannotprojectthemonto boundaryregionwithoutconditionalfiltering. C860witness has d/(2r)~1.303<1.38, so unaffected.

Evidence certify_hub_distance_boundary.py; directedexactcoefficients. This doesnotcertifyobjectiveupper or discardthecomplement; itremovesinteriorhubconfigurations onaproveddistance-definedregion.
