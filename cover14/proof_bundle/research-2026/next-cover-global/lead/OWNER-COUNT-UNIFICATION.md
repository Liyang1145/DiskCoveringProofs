# Positive boundary owners unify k10/k11 — C1171 proved analytic necessary reduction

## Target
Replace actual disk activity k by q=#Voronoi cells owning a positive-length S1 arc. Show q∈{10,11}, q10 has the same no-chord triangulated-disk interface with3/4 interior sites even when k11; q11 has3 interior sites and only second-neighbor ring chords. Boundary singleton ties are handled by outward clipping and a limit, without a generic-position premise.

## 1. Normalize and prove connected ownership without essentiality
Start any14-disk cover ofD at0<r≤U<1/3. Project sites intoD, merge coincident sites (retain multiplicity metadata), apply same-arc inner-root replacement for every actual active disk. This preservesD coverage and actual boundary arcs. C1142 gives k10/11 before merging; positive owner count will not need k-labels. Every site norm≤s=√(1−r²): active sites byreplacement; inactive norm<1−r<s. All distinct sites lie inintD and in the interior of their FULL-plane convex Voronoi cellsW_i.

For distinctsitesi,j, bisector distance d=||ci|²−|cj|²|/(2|ci−cj|)<s STRICT: ifequalnormsd=0; otherwise d≤(|ci|+|cj|)/2<s since at leastone norm<s. Each actual boundary arcA_i has length≤L=2asinr, while twoS1 bisector crossings have smaller separation2acosd>L. Hence g_ij(x)=|x−ci|²−|x−cj|² has at mostone zero onA_i; its nonpositive subset is interval/empty (possibleendpoint singleton). Intersect constraints: J_i=W_i∩S1 is connected or empty, since coverage gives J_i⊂A_i. Inactive sites haveJ_i empty.

Letq count positive-lengthJ_i. These closed arcs coverS1: a point not in their finite union would have an open neighborhood devoid of positive arcs, impossible because finitely many empty/singletonJ_i could not coverit. Their interiors are pairwise disjoint (ties lie on finitely many bisector lines), so they form a cyclic partition. CapacityqL≥2π givesq≥10; q≤k≤11 byC1142. No actual-arc essentiality assumed.

## 2. Hidden cells lie entirely insideD
IfW_i hasJ_i empty/singleton, thenW_i⊂D. Proof: ci∈intW_i∩intD. Ify∈W_i lies strictly outsideD, take a small open ball aroundci containedinW_i. Convex combinations withy produce an open cone inW_i crossingS1 in a positive-length arc, contradiction. Thus every hiddenW_i is bounded and containedinD. Its outer-circle intersection disappears upon any outward clipping.

## 3. Outward clipping regularizes boundary singleton ties
Fix sites, putRε=1+ε and rε=r+ε. Anyx∈D_Rε is withinε ofD, so original coverage and triangle inequality coverD_Rε with same sites at radiusrε. Every original positive owner remains positive for sufficientlysmallε: choose apoint insideJ_i avoiding all finite pairwise tiepoints, giving strict nearestmargin that persists outward. Everyhidden cell stayswithinD by§2 and hasno new boundaryownership. Hence exactlyq positive owners and no singleton/empty otherboundarycells onS_Rε for all sufficientlysmallε.

NormalizebyRε. Allsite norms≤s/Rε < sqrt(1−(rε/Rε)²), because Rε²−rε²=s²+2ε(1−r)>s². Thus the connectednesslemma stillholds. Every boundaryswitch hasexactlytwoowners: threeconnected nondegenerate closedarcs with disjointinteriors cannotshare apoint on acircle. Thebisector transverse becauseallnorms<Rε; marginfrom othercells givespositive inwardfacet.

Takeε→0 through values withrε/Rε<1/3, possible sincer<1/3. Also require asin(2rε/Rε)<.73 and asin(rε/Rε)<.34; both hold uniformly for allsmallε because they hold strictly atU and continuity applies. Merelyrε/Rε<1/3 isnotbyitselfthequoted3.11bound. This is a perturbation of clippingdomain+allowedradius, NOT ofcenters or assumptions. In theend allmetric witnesses arepassedto limits.

## 4. Owner-arc measure replaces actual-arc endpoint order
For anytwoowner disksi,j at inflatedradiusrε sharingp, their ownedboundaryarcsJ_i,J_j⊂S_Rε∩B(p,2rε)=K, anarc. Everyintervening ownedarc in theliftinsideK is alsocontainedinK, becauseJ_i partitiontheboundary cyclically. Eachownedarc length≤2asin(rε/Rε) inangularunits.

Ifq10 andcyclicdistance≥2, Kcontains≥3ownedarcs, leaving≤7others. Ifq11 anddistance≥3, Kcontains≥4, againleaving≤7. Either forcesπ≤asin(2rε/Rε)+7asin(rε/Rε)<3.11<π. Thus q10 nonneighbor disksdisjoint; q11 onlyfirst/second-neighbor pairs canintersect. Noessentialityofactualarcs needed. For anysharedprimalvertex siteshavecommonp, so these restrictions apply todual edges/faces.

## 5. Dual topology and zero-epsilon limit
Atε>0, use the regularcurveddual collar of `K10-CATALOGUE-AUDIT.md` (doesnotneedinnernormwindow forinteriorsites, onlyconvexcells andpositiveboundaryarcs). Fullgraph sitesconsistofqboundarynodes andm interiorsites. C1142 supplies≥3 distinctinactive sites, henceq10 givesm3/4, q11 givesm3; total≤14. Coincidentlabels alreadymerged.

Forq10 everydualfacehasatleastoneinteriorsite, hubfan introducesnoringchords. Completenessenumerationgivesoneof the1000 correctedq10graphs.

Forq11 everycommonringclique is≤3consecutivelabels. Fanfaceswithanyinteriorsitefromthatnode; faceswithnorinteriorsites arealready3-ringtriangles. Thetriangulateddisk has11outer+3innernodes, onlysecond-neighborringchords. ChordmiddlelabelsindependentinC11, hence≤5chords, eachcuttingoffa3-gon pocket thatmaycontaininteriorsites.

Therearefinitelymanytriangulatedsimplegraphs on≤14fixedlabels. Alongasequenceε→0 chooseasubsequencewithconstantincidenceandfanchosenfaces. BoundaryanchorpointsandallprimaltrianglewitnesseslieinD_(1+ε), hencecompact; passafurther subsequenceonwhichallconverge. Atlimitanchors lieonS1, allincidentdistances≤r, cyclicgaplengths≤2asinr, copiedtrianglewitnessdistances≤r. Combinatorialtopologicaldiskisstored abstractly; itsgeometricrealizationmaydegenerate, whichisallowedbythecertificateinterface. Thusallcovers mapsintothesegraphrelaxations, evenwithoriginalsingletonboundaryties.

## Status / gap
Registered C1171, analytic global necessary reduction. Lead checked connected-owner, owner-order, clipping and finite-limit interfaces; independent member full-cell argument accepted only after false no-singleton/no-empty-ear corollaries were withdrawn. Independent exact enumeration C1168 reproduces corrected1000 q10 classes; q11 pocket enumeration gives5277. No metriclowerbound follows merelyfromthis reduction. C1172 retains emptycircumcircle equalities, globalnearestinequalities and noncollinear facetriples in thelimit (stronger than the permissive relaxation above). C1177 Q11-DOUBLE-CHORD-EXCLUSION.md strengthensdouble-earboundtoanychords, excludes4235 q11graphs leaving1042, atmost2chords. C1167 exactattainment is independent of this topological reduction.
