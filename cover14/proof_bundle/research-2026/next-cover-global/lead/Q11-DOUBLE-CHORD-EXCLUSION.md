# q11 has at most TWO chords, and if two their middle labels differ by2

## Scope and input
C1171 positive-owner representation of any14diskcover with0<r≤U. Workfirstatsmallε>0 outwardclip, normalizecircleto1 andsetρ=(r+ε)/(1+ε). Retain strictinequality 4asin(2ρ)+10asinρ<2π (provedatU byrationalseriesin q11_double_ear.py andpersistingforsmallε). Thisisstrongerthanempty-earpruningandincludespopulatedpockets.

## Any chord controls three consecutive owner arcs
Supposechord joins ringlabels i−1,i+1. TheyhaveacommonVoronoi-facewitnessp (eitherincidenttriangle suffices), hence theirwholeownedarcs J_(i−1),J_(i+1) lieinK=S1∩B(p,2ρ), aconnectedarc oflength≤B=2asin(2ρ)<π. Theirinteriorspositive anddisjoint. Bycyclicpartitionorder,K containsallownedarcsbetween them alongoneofthetwocyclicdirections. ShortdirectioncontainsJ_i (threewholearcsincludingendpoints); longdirectioncontainsnine-or-morewholearcs (in fact10). Thelatterisimpossible: ifKcontainedatleast4wholearcs, totalcoverage≤B+7L<2π, L=2asinρ, byC1171strict3.11bound. ThusKcontains theSHORT consecutive triple, and
|J_(i−1)|+|J_i|+|J_(i+1)|≤B.
ThisdoesNOT requireJ_i'ssitetomeetp, noranemptytriangularpocket. Itisownerorderandpairintersectiononly.

## Two disjoint triples impossible
Ifchordmiddlelabels i,j havecyclicdistance≥3, theirthree-labelsetsaredisjoint. Sixarcslength≤2B; remainingfive≤5L; hence2π≤2B+5L, contradictingstrictcapacityabove.
Noncrossingsecond-neighborchordshavenonadjacentmiddlelabels (distance≥2), fromC1171/pocketfactorization. ThereforeANYtwodistinctmiddlelabelsmusthavecyclicdistanceEXACTLY2. Therecannotbethreemutuallydistance2labels inC11: thedistance2adjacencygraphisitselfan11-cycle, trianglefree. Thusnumberofchords≤2; if2, theyshareoneoutervertexandtheirpocketmiddlelabelsaredistance2.
ThistrianglefreeargumentisaboutDISTANCE-EXACTLY2 graph, notC11² (whichDOEScontainconsecutive3cliques). DoNOTrepeatmember'searlierfalseinference.

## εlimit and catalogue
Allargumentsholdatsmallε withsamepositiveq=11. Noexcludedgraphcanoccurforallsufficientlysmallε, hencefinitegraphsubsequenceyieldsonlytheallowedpatterns. Genuinediskcoverthereforemapsintoarestrictedq11family:
- no chord:85classes;
- one chord:557classes;
- twochords,middlesdistance2:400classes.
**Total1042**. Removed4235from5277, including231additionalbeyondempty-earpruning. All3/4/5chordclassesexcluded, whetherpocketsemptyorpopulated. `q11_double_chord.py` reconstructschordsfromcanonicalfaceedges (metadata'smiddlelabelsmayusepredihedralcoordinates), storesoneforbiddenmiddlepairperremovedrowandallretainedindicesin `q11-double-chord-pruning.json`.

## Remaining gap
Globalmetricboundstillnotproved:1000q10 and1042q11graphsremainasNECESSARYsystems. Retaineddoesnotmeanrealizable. Thegainisacompletegeometricexclusionofentirechord-patternclasses, notnumericalinfeasibility.
