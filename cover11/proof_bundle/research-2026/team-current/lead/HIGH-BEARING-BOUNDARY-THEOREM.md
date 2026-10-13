# Uniform hub boundary reduction for b1,b2 >= 1 radian

Object: C848/C849 flatsector2 necessary patch, actualr∈[3/8,19/50], bearings b1,b2∈[1,acosr], current exact9decimal frozen dual5671967c... . Fix(r,b1,b2) and anylegalwidths. Only hub objective is optimized; all otherterms areconstant. Cartesianhubdomain is C858 three-disks intersectedwithwedge. Claim: maximum occurs on at least oneof the THREE diskboundaries. No ridge-only conclusion.

## Positive Laplacian
Let Q1=(r sin2b1,2r sin²b1),Q2=(r sin2b2,-2r sin²b2); Lj=|X-Qj|. Objective islinear+sum(ajtheta_j+beta_j Lj²-cj Lj), with beta1=-z16/(4R0²),beta2=z20/(4R0²),c1=z78/(2R0),c2=-z82/(2R0), allpositive. Angles areharmonic awayfromQj. Thus DeltaF=4(beta1+beta2)-c1/L1-c2/L2.
C848faceconstraints imply Lj<=u=2r. Also L1+L2>=d=|Q1-Q2|>=2r(sin²b1+sin²b2)>=4r sin²1. Hence d-u>=2r*a>0, where a=2sin²1-1=-cos2. Reciprocalcap underLj<=u,L1+L2>=d is endpointmaximum of convexfunction onL1+L2=d:
 c1/L1+c2/L2 <= max(c1/(d-u)+c2/u,c1/u+c2/(d-u))
 <=max(c1/a+c2,c1+c2/a)/(2r)
 <=(4/3)*max(c1/a+c2,c1+c2/a).
Directed25digitcertificate gives uniform DeltaF>=.39660921894598305>.39. This is NOT aHessianconcavity claim; it means nointeriorlocalmax canexist (traceHess atlocalmax<=0).

## Compactness and boundaries
The three disks give a bounded closedset. Closing thewedge introducesno newfeasiblepoints:
- v=0 impossible sincehubnormrequiresv>=sqrt(1-r²)-(1-r)>0.
- Upperwedge raydelta=b1: A=0, faceupperH<=2r sinb1; hubnorm impliesseparationH>=2r|sin delta|=2r sinb1. ThereforeH=2r sinb1 andhubsiteequalsc1. But |c1|²-(1-r)²=2r[1-cos(2b1-acosr)]>0, contradiction. Thepositiveangleliesstrictlybetween0andpi. Lowerwedge ray analogously hub=c3 outsidehubnormdisk.
Thus the intersectionwithclosedwedge is compact and liesstrictlyinsideopenwedge. DistancesLj>=d-u>0, Yj>0 fromC848positivefaces; the anglebranch remains smooth onthecompactset. F attainsmaximum. Ifmaxwerenot onanydiskboundary, pointwouldbeinterior toallconstraints, contradictedbypositiveLaplacian. Degenerate disk-lens interiors cause noissue: then everypointalreadyonadiskboundary. CoincidentfacecirclesT=pi/2 cannotoccurhere(T>=2), but proofdoesnotrelyondistinctness.

## Scope and payoff
The entire two-dimensionalhubmax for thisbearingregion reduces to the unionofthreecircle-boundaryarc families, including theirintersections. It doesNOTreduce to intersections alone andNOTtoC855ridge. It doesnotcover min(b1,b2)<1. C860counterexamplehasbothbearings<1 anddoesnotcontradictit. Width optimization andouter(r,b1,b2) stillremain. Noflatsector2exclusion orsharpn11proof yet.

Evidence: certify_hub_laplacian.py ->hub_laplacian_certificate.json. Laplacian derivation independentofADkernels; reciprocalcap usestriangleinequalityandconvexonevariablemax, notsampling. Next executable step is to parameterize thethreeboundaryarcs withvalidcoverage and comparetheir intervalbounds; separatelyboundlowbearingregion.
