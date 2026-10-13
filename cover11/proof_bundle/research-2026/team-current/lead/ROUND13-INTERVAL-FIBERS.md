# Round13: exactfiber algebra and intervalinterface

Original target unchanged: unconditionalsharpn11optimum; bounds .375<r_D(11)<=C249 unchanged. Flatsector2notexcluded.

## Analyticstructuralgain
C850 proved: W=2atan2(r sinx,1-r cosx),x=2b-acosr∈[0,acosr]; W>=g iff b>=[acosr+asin(sin(g/2)/r)-g/2]/2. Uniformbmin=.60946080763725372899 (exactformulaauthoritative). ARC-WIDTH-EXACT-INVERSION.md, check_arc_inverse.py,arc_inverse_control.json. Noteactual g=.0464445635914; oldsummaryg>.0466 was inaccurate. Codealwaysusedexactexpression.
C851 proved: scalarwidthstationarypoints satisfydegree<=8 polynomial; Hstationarypointsdegree<=20. WIDTH-STATIONARY-POLYNOMIAL.md,H-STATIONARY-POLYNOMIAL.md; exactsymboliccontrolscheck_width_polynomial.py,check_h_polynomial.py. Extraneousroots, identicallyzerocaseexplicit; notrootexhaustioncertificate. Memberindependentderivativealgebraauditagrees; nofloatingrootsusedasproof.
DELTA-OUTER-CHART.md: delta=b1-A,B=b2+delta, |delta|<=acos sqrt(2r/(1+r))<=acos sqrt(6/11). Necessaryprojectionfromhubnormdiscriminant; removesr,b,Adependency therebutdoesnotuniversallytighten objective.

## Intervalimplementation
interval_joint_patch.py coordinatebased7factorvalue,interval_patch_fibers.py projectedscalarfiberenvelopes,guardedMVTwidthbound. interval_patch_delta.py alternateoutercoordinates. 1632randomactualpatchpointcontrols maxfloatmismatch1.78e-14 andallthickboxcontainment; calibrationNOTproof. Domainandclipaudit inINTERVAL-PATCH-KERNEL-SCOPE.md. Necessaryclippingneedsonlyencloseactualfeasiblepoints; MVTcenter needswholeouter×segment analyticextension, henceexplicitguard. Scalar/outerheapsretainALLpruneduppers; searchfloorisheuristicnotfeasiblelower.
Polynomiallengthtermsbounded jointlybyquadraticextrema; improveddependency. sectoralternateexpression uses exactL+w/2=2b+asinr+w-alpha andarea=(w+cross(c,P0)-cross(c,P1))/2; checkedagainstoriginalfactorcalibration. No symmetry assumption.

## Boundedexperiments(noexclusion)
Immutablecoefficientsjoint_nested_frozen.json SHA2565671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb.
Localfixedouterfiberupper28.104326002; smallouterbox28.104326749, numericallynear28.10432239 butLOCALONLY. patch_fiber_mean_certificate.json historical versionbeforequadratic/alternatechanges.
Fullouter1601boxes: initial29.1114233122, quadratic+bmin28.6796137086, weightedphysicalwidthsplit+alternateformula28.3916801983. Thesearelooseintervalkerneloutputs, no belowpiassemblypossible. Lastdeltaouterpasssame1601budget artifactpatch_outer_delta_certificate.json. Needouterdependencyrepair, NOTlargersimilargrid. 22remainingfactorshavenotbeenrecertifiedfornewcoefficients.
Hashhygiene: oldquadraticjobimportedkernelbeforelateralternateedit; reconstructedexactsourceinterval_joint_patch_quad_snapshot.py andcorrectedstoredhashwithnote. Weightedcertificatecorrecteddriverhash tocertify_patch_weighted.py. Nextcertificatebuild shouldcapturehashesATSTART,notexit.

## Auditfailuresclassified
Memberarcclosedformreportv1 wrongxupperdomain,discriminant,smallgformula,atanidentity; correctedby leadanalyticproofandmemberwithdrawal. Evenrev2dW/dbmissesfactor2 (leadusescorrectdW/dx), doNOTciteextras. MemberwidthguardG1/G2falsekernelobjectionswithdrawn: conflatedactualfeasiblesubset withunphysicalpoints andusedoldcoefficients. Guardproofandexactpolynomialaudituseful. Judge freshroutefailedtwice, alternativev41adapterunavailable; proceededlocallyplusactiveTeam audit. Allmembersnowinactive, noextraassignments.

## Nextobligation
Buildouter-correlatedupperenvelope (intervalgradient/centeredTaylor onvalidbranch, or optimizejointlinearizedscalarfibers withouterdependencies retained); calibrateusingknownlocalpointbeforefullcoverage. C851polynomialrootrepresentationavailablebutouterintervalcollisionsmustbehandled. Do notscalecurrentboxcountwithoutimprovingrepresentation. Neednewremaining22factorboundswithsamefrozenhashbeforetotalclaim. Mainsharpglobaltheoremstillrequiresmuchmorethanflatbranchremoval; no goalcompletion.
