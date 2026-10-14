# Isolated stationary root and exact attaining construction (not optimality)

## Object and local root
Use original F,G,H of `root_scout.py` and positive radical branches:
s=√(1−r²), a=(s+z)/2, t=r+√(r²−z²), b=r+√(r²−(a−z)²), d=1−√(r²−c²).
F=(v1 d−v2 b)²+(a v2−c v1)²−det², v1=(1+a²+b²−r²)/2, v2=(1+c²+d²−r²)/2, det=ad−bc.
G=((a−c)²+(b−d)²)(c²+(d−t)²)(a²+(b−t)²)−4r²[(c−a)(t−b)+(d−b)a]².
H=F_zG_c−F_cG_z. No assumption b=t; they are different radicals.

`root_integer_certificate.py` independently implements integer-directed fixed-dyadic intervals (240fractionbits), second-order multivariate AD, and a Krawczyk contraction. Every rounding is explicitfloor/ceil integerdivision; sqrtusesintegerisqrt ofendpoint*S. Exactcontrols include polynomial mixedderivatives, reciprocalderivatives andsignedintervalmultiplication. mpmathonlyproposes aninversepreconditioner, convertedtoanexplicitexactdyadicmatrix; inverseaccuracy isnotanassumption.

`root-integer-certificate.json` records exactbox endpoints, preconditioner, Krawczyk image andmargin. Boxis outwarddyadicenclosure of root-scout decimalcenter ±10^−20, NOTtheprinteddecimalbox silentlytreatedasbinaryexact. Thechosen rationalcenter m itself isinterval-enclosed; foritsfixed exactvalue thecomputedKinterval remainsanouterenclosure. rho=||I−YM||∞<3.807e−16, Kstrictlyinsidebox withmargin>9.999e−21. Themap x→x−YΦ(x) mapsboxstrictlyinsideit andisacontraction. Y is nonsingular: ||I−Y DΦ||<1 makesY DΦ invertible foranypoint. Banachfixedpointthereforegives exactlyoneΦzero inthebox. Radicalpositivityandallnonzerodenominatorsarecheckedbyintervalguards. Thisisolatesanalgebraicallydefined rootlocally, notgloballyamongallcontactbranches.

## The14 centers
Take(±a,±b), (±c,±d), (±s,0), (±z,0), (0,±t). Allindependent signs areincluded in4-elementorbits. Thisis14, not10. DefineA=(a,b), C=(c,d), X=(s,0), Z=(z,0), T=(0,t). Strictintervalcontrols arein `root_cover_check.py` / `root-cover-controls.json`.

## Boundary coverage exactly
Letp=((v1d−v2b)/det,(av2−cv1)/det). det≠0onrootbox. F=0 means|p|=1. Sincep·A=v1 andp·C=v2, |p−A|²=|p−C|²=r² exactly. Noinvalidsum-of-squares orcircle-intersectionbranchargumentisused.
Theotherfirst-quadrant anchorsare(s,r) and(0,1). TheylieonS1; (s,r) isdistance rfromX andA because a=(s+z)/2 implies(s−a)²=(a−z)² and b−r=√(r²−(a−z)²). (0,1) isdistance rfromC because1−d=√(r²−c²). Reflecttheseanchors toobtain10cyclicanchors. Intervalcrossproductsproveconsecutiveangleincrements in(0,π), andthelistedownercenters connecteachpair bytheiractualshortcirclearcs. A radiusr<1diskintersectsS1 inaconnectedarc oflength<π, so ifitcontainsbothanchorsitcontains theirshortinterveningarc. The10arcs coverS1 exactly, includingendpoints.

## All interior nearest-site maxima ≤r
Enumerateall364 unorderedsite triples overtheentirerootbox. Scriptcontrols:
-4triples exactlycollinear bysymbolicpolynomialidentities;
-64circumcenters strictlyoutsideD;
-280triples haveanothercentrestrictlyclosertotheircircumcenter;
-16remaininsideD, ofwhich2strictlyhavecircumradius<r.
No approximatezero testisused: determinantintervalsnotexcludingzero requireexactSympyzero polynomial; allotherclassificationdecisions usestrictintegerintervalsigns.
The14nonslackremainingfaces splitintoexacttypes:
1. 4 D2imagesof(A,C,T): G=0 givescircumradiusr bytheusualnoncollinear triangleformula R²=l1l2l3/(4cross²).
2. 4imagesof(A,X,Z): commoncircumcenter(a,b−r), eachdistancer bythedefiningradical and a midpointidentity.
3. 4imagesof(A,Z,T): commoncircumcenter(z,r), eachdistancer byb/t definitions.
4. 2faces(Z,−Z,±T): commoncircumcenter(0,±(t−r)), eachdistancer byz²+(t−r)²=r².
The2slackfaces are((−c,d),(c,d),T) anditsreflection.

Tofinishcoverage, clipordinaryVoronoicellsbyD. Anyuncoveredpoint wouldgivea cellwith maxdistance>r. OncellboundarywithinS1allpointsarecoveredandnearest, soatdistance≤r. Alongstraightcellfacets, squaredistanceisconvex, hencecannotstrictlyexceedbothendpointvalues. Amaximuminsidea2Dcellcannotbeastrictinteriormaximumof squaredEuclideandistance. Thusanyvalue>rrequiresaninteriorVoronoivertex, where≥3noncollinearsitesareequidistantandnearest. Suchavertexappearsinthe364tripleenumeration andhasdistance≤r. Contradiction. Thisalsohandlescocircularhigherverticesbychoosinganynoncollineartriple.

Atp thetwoincidentcentersareexactlyatdistancer. `root_cover_check.py` additionally verifiesstrictsquaredistance>r²for everyothercenteratp overthewholebox. Thus min_i|p−c_i|=r exactly, andtheconfiguration's coveringradius equalsr.

## Scope and next implication
Thisisanexplicitexactconstructionat thelocallyisolatedstationaryroot, withrnear.3317320342762341225578155488024. ItisNOTa global lowerbound, notsymmetryWLOG, andnotproofthatthisstationarybranchislocallyminimal. Missing mainimplication remains: everyarbitrary14centercoverhasradius≥thisr.
