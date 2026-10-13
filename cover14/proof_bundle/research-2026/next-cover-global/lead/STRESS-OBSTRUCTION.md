# Fixed sharp stress cannot certify this literalgraph (proof + interval kernel)

## Precise method, not main theorem
LetGbe theliteral10boundary/4interiorcandidategraph with16facewitnesses and20boundaryanchor-site incidences. Assignfixednonnegativeweightsw_e, Σw=1. Forordered10unitcircleanchors withgaps∈[0,L*], sum2π, L*=2asinr*, defineE_w=min overALLsiteandfacewitness positions Σw_e|u−v|². Theproposedsharpcertificatewouldrequire E_w≥r*² forEVERYanchorconfigurationinthiscapped-simplex. Theclaimhereisno suchfixedw existsfor thisG. Thisdoesnotdisprove thecoveroptimum, piecewiseenergybounds, graphstrengthenings, orrestrictedanchor domains.

## 1. Saturation and symmetry are necessary
Assumeasharpwexists. AttheC1167candidate allgraphincidencedistances≤r*, with2slackfaces. Thusweightedenergy≤r*²; theglobalcertificategives equality. Allslackfaceedgesmusthavezero weights, andcandidatefreepositionsmustminimizequadraticenergy. Thereforeallsitesandwitnessesareforcebalanced.
TheD2group permutesliteralgraphandanchor gapdomain. Eachtransformedstress isasharpstress; averagewbar alsois: min_x Σ_g E_unmin_g(x)/4 ≥ Σ_g min_x E_unmin_g(x)/4 ≥r*². (Minimumoflinearfunctionsisconcaveinweights.) CandidateisD2invariant, soavgstillsaturates. Hence it sufficestoruleoutD2-symmetricsharpstresses.

## 2. Exactly which weights need remain
Analytic siteforcecascade `STRESS-SUPPORT-ANALYTIC.md`: 4X-adjacentfaceweightsand2centralfaceweightszero. Acutewitnesses haveunique positive barycentricstressratios β, soallotherfaceweightsaretotalfaceweight t_f timesβ. The6zero-face conclusionusesonlysite+witnessbalance, notgapKKT.
The44remainingedges splitintotwoX2-edgepathsandonecentralcomponent. D2symmetry gives6centralweightorbits (2faceorbitsand4anchor-edgeorbits). `stress_obstruction_certificate.py` builds theirsiteequilibriumusingexactroot-boxintervalcoordinates. Normalize firstfaceorbit to1. Aselected6x6system(consistingofthisnormalizationand5site-forcecomponents) isintervalnonsingular byguardedGaussianelimination, giving6strictlypositiveweightintervals. Theexactrowindices,orbitmembers,andboundsarerecorded in `stress-obstruction-certificate.json`.
If firstfaceorbitweight=0, thesamehomogeneousnonsingularsystemforcesallcentralweightszero. Thusanynonzerononnegative symmetriccentralstresshasfirstfaceorbitweight>0 andafterrescalingliesinthesecertifiedintervals. Noapproximate-rankorLPfeasibility premiseisused.

## 3. Nonzero central network has a feasible descent
Anchor orderstarts(s,r),p,(0,1),(-px,py),(-s,r),(-s,-r),(-px,-py),(0,-1),(px,-py),(s,-r). Useangularvelocities
vθ=(0,−1/4,−2/3,−13/12,−4/3,−4/3,−13/12,−2/3,−1/4,0).
Bothcap-activegaps(index4and9) havezero derivativeandremainconstantforθ(ε)=θ+εvθ. Othergapsstrictlybetween0andL*, so±smallεarelegal. (Strictness followsradicalintervals/cyclicordering; onlyXarcsmaximal.) Move ALL freecentralnodes, INCLUDING facewitnesses 24+f, linearly withthefixed rationalvelocitiesstoredinthecertificate; thesevelocitiesareproposedbyfloatSchursolve butvalidatedasEXPLICITdyadicconstants, notassumedto beexactoptimalvelocities. RotateeachXsitewithits2anchors; those2-edge energiesstayconstant.

Forcentraledge(u,v), secondderivative ofweighted squareddistanceis
2w[|v_u−v_v|²+(p_u−p_v)·(acc_u−acc_v)],
wherefreecentralaccelerations=0 andanchoracc_k=−(vθ_k)² p_k. Thekernelinterval-evaluatesthisexactformulaandfinds normalizedcentralcurvature in
[−.1445582359335557,−.1445582359335545] (displayrounded; exactrational endpointsinJSON).
Theexactcandidate therefore CANNOTminimizethisunminimizedpathenergy atε=0: iffirstderivativeisnonzeroonesideddescentalreadyexists; ifzero, negativesecondderivativegivesdescent. SinceE_w isboundedabovebytheenergyofANYchosenfreepositionpath, E_w<r*² fornearbyfeasibleanchors. Contradiction.

## 4. Zero central network also cannot be sharp
OnlythetwoXpathsremain. SiteequilibriumatX gives equalweightsonthetwoincidentedges becauseanchorvectorsare(0,±r*). D2symmetrygivesequalweightsforthebothpaths. EliminatingX giveseachpathenergy apositiveconstanttimes|anchor1−anchor2|²=4sin²(gap/2). On(0,L*) thisisincreasing. Shrinkonecapgap andtransferangletoanystrictlyinactivegap, keepingothersfixed; thepositivepathenergystrictlydecreases. ThusE_w<r*². AtleastonepathhaspositiveweightbecauseΣw=1.

## Controls and limitations
Repro `py -3 -B research-2026/next-cover-global/lead/stress_obstruction_certificate.py`.
OriginalrootboxC1167, integerintervalkernel, analyticgeometricidentities. Orbitlabelsandincidencesarefiniteexplicitinputs; theirphysicalD2mappingmustbecheckedalongwiththeformula. Currentproofrecordawaitsanindependent auditofsymmetryaveragingandfeasible-pathinterfaces. Numericalone-stressnegativeHessianalonewasNOTusedtoconcludeall-stressfailure.

Nextmetricroute mustretain additionalgeometricconstraints (Voronoi/emptycircle/orientation) orusepiecewisebounds, ratherthantrying toproveglobalconvexityofafixedsharpDirichletenergy.
