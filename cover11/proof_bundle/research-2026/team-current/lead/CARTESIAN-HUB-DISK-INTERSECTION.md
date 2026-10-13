# Cartesian version of the full C848 hub fiber

Letv=H cosdelta,t=H sindelta,c9=(s−v,−t),r>0,H>0. Legalangles implydelta∈(−b2,b1)⊂(−pi/2,pi/2), hencev>0. SetA=b1−delta,B=b2+delta.

Eachfacecircumradiusconstraint becomesaDISK:
 H≤2r sin(2b1−delta) iff (v−r sin2b1)²+(t+r cos2b1)²≤r²;
 H≤2r sin(2b2+delta) iff (v−r sin2b2)²+(t−r cos2b2)²≤r².
ProofmultiplybypositiveH thencomplete-square. NormconstraintisthirdDISK (v−s)²+t²≤(1−r)². H≤2r automaticfromeitherfirstdisk (itscenter hasnormr). SeparationH≥2r|sindelta| becomes TWOdiskEXTERIORS:
 v²+(t−r)²≥r² andv²+(t+r)²≥r².
Legalanglewedge exactly −v tanb2<t<v tanb1. ThusC848domain isintersectionofthreecloseddisks, outside twootherdisks, withinopenwedgev>0. No symmetry/numericalpremise.

Atfixedr,b1,b2,v, thethreeinteriordisksgiveclosedtintervalintersection (emptyifanyradicandnegative):
 t∈−r cos2b1±sqrt(r²−(v−r sin2b1)²),
 t∈ r cos2b2±sqrt(r²−(v−r sin2b2)²),
 t∈ ±sqrt((1−r)²−(v−s)²).
Then remove theopenintervals(r−sqrt(r²−v²),r+sqrt(r²−v²)) and(−r−sqrt(r²−v²),−r+sqrt(r²−v²)) if0<v<r. ResultatmostTHREEclosedintervals; don'tkeepjustcentralcomponentwithoutproof. Wedgeclosesupperrelaxationasneeded. Actualv>=s−(1−r)>4r/5. Thisisanalyticalternativechart (r,b1,b2,v)+t,width1,width3scalarfibers.

WhenT≠pi/2,thetwofacecircleboundariesintersectatoriginand(v*,t*)=(2r sinT cosD,2r sinT sinD); originhasH=0andnotlegal. ThusC855ridgeisuniqueothercircleintersection, automaticallyinsidehubnormdiskandoutsideforbiddendisks. AtT=pi/2 theTWOcentersCOINCIDE (sin2b1=sin2b2,cos2b1=−cos2b2), hencefacecirclesidentical andthereisno uniqueintersection; ridgepointisstillfeasiblebutnotcharacterizedbytwoindependentactiveconstraints. ThisgivesindependentEuclideanrepresentationofridgeandC848interface. Noobjectiveconvexity/maximum-atintersectioninference follows.
