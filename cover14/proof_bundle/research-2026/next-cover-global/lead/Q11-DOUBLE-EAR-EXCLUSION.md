# Two disjoint empty ears are impossible: a strict q11 metric pruning

Scope: arbitrary normalized14diskcover at0<r≤U=.33173203427623414, q=11 positive boundaryowners. UseC1171 outwardclipgraph, thenstrictcontinuitymargin; this isnotasymmetryoractual-arcessentiality assumption.

Letf={i,j,k} be anALL-BOUNDARY triangularface. Itscommonwitnessp iswithinr ofallthreecenters. EachownedboundaryarcJ_i liesinB(ci,r), henceJ_i⊂S1∩B(p,2r). Because2r<1, thelatterarc hasangularlength≤2asin(2r) (maximumoveranycenterp). Distinctownedarcs have disjointinteriors. Therefore
|J_i|+|J_j|+|J_k|≤2asin(2r).
ThisdoesnotrequirepinsideD, buttheconstructiondoesgivep∈D.

If TWO all-boundary faces have DISJOINT vertexsets, theirsixownedarcs have totalmeasure≤4asin(2r). Eachoftheremainingfivearcs haslength≤2asinr. Summingthepartitiongives
2π≤4asin(2r)+10asinr.
TheRHSincreasesinr, yetatU itisSTRICTLYlessthan2π byatleast3.8938865969777676e−5 (displayonly; exactrational lowerboundinJSON). Contradiction. Forε-outwardclipnormalizeρ=(r+ε)/(1+ε); strictmarginpersistsforallsufficientlysmallε, soeverychosenfinitegraphsubsequencealreadyhasnodisjointall-ringfacepair. Nozerolimit-labeldegeneracycaninvalidatepruning.

## Rigorous constant check
`q11_double_ear.py` sums100exactrationalpositiveasinseries terms. Coefficients binom(2n,n)/(4^n(2n+1))≤1, so remainingtail≤x^(201)/(1−x²). πlower usesMachinπ=16atan(1/5)−4atan(1/239), with80-termalternatingbounds. AllcalculationsPythonFraction, onlyfinaldisplayusesfloat. Theexactlowermarginispositive.

## Catalogue consequence
Anemptytriangularpocketispreciselyanall-ringface; populatedpocketsarenot. Testallpairs ofall-ringfacesin5277graphs, requiringemptyvertexintersection. **4004 areexcluded;1273remain.** Retainedcountsbytotalchords0..5:85,557,520,105,6,0. The6survivorswith4chords usepopulatedpockets; all5-chordgraphsaredisprovedbythiscondition. Fullremovedpairwitnessesandretainedindicesin `q11-double-ear-pruning.json`.

Thisisagenuinemetricexclusionofacompleteconfigurationclass, notonlyanincidencecount. ItdoesNOTexcludeallq11 covers;1273necessarygraphsremain, plus1000q10graphs. ItdoesNOTshowthat2overlappingemptyearsareimpossible: sharedownedarcswouldbedouble-counted, andourproofexplicitlyrequiresdisjointvertexsets.
