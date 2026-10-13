# Local ridge objective upperbound audit

Uses C853exactlocalelimination. Target Q0:r∈[.379,.38],b1∈[1.106,1.108],b2∈[1.068,1.071],delta∈[.035,.040], allC849width/Hfibers. Frozen coefficienthash5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb.

certify_local_ridge.py coversremaining5coordinates(r,b1,b2,w1,w3) withbinaryintervalouterboundsroundedOUTWARD fromexactrationalbox; wdomainstartsoutwardg, upperoutward2asinR0. Width projections fromC849; rejetiononlyifnecessaryconstraintempty. OutsideQ0 floatpadding allowedasanalyticenlargement, notextraC853domain: everyoriginaltargetpointretainedandformulaonridge iswell-defined there.

patch_ridge_jet.py usesradicalfreehubobjective withdelta=b1−b2,H=2r sin(b1+b2), analyticidentity checkedagainstoriginalfullobjective for100points; cancellation verifiedsymbolicallycheck_patch_cancellation.py andmanualtrigproofinLOCAL-HUB-RIDGE-ELIMINATION.md. ForwardintervalAD overcompleteboxrequirespositiveeveryrelevantsqrtargumentandatan2branchguard. Onunsafeboxfallsbacktooldintervalfiberexpression restrictedtoridge; noMVT throughbranchcuts.

Meanvaluecenter isentireboxmidpoint in5independentcoordinates. Sevenargumentinterfacehasderiveddelta/H butobjectiveoverrides them byridgeexpressions; d/dinputdelta=d/dinputH=0 exactly. Hence extraargumentintervals do notaddunsupportedcenterrelations; thewholejetcorrectlydifferentiates3outer+2widthfunction. Gradientincludesmixedparameterdependencies byforwardproductrule; no separateblockpositivityargument.

Upperthreshold28.1044 is heuristicpruningtarget, notassumedbound. Everyprunedleafupperstoredinterminalmax, allsplitboxesclosedandcoverparent. Runendedwith0liveboxes after879evaluations; largestprunedupper=28.10439974622152. Thus J<=28.1044 onQ0 locally. This isNOTamaximumestimate fromsampling, andNOTupperonrestofflatpatchdomain. Numericcandidate28.10432239 liesbelowbound, sanitycheckonly. No22remainingfactorcertificatesfornewcoefficientsyet; nofullsumcertificate.

Files andhashes inlocal_ridge_upper.json; frozencontrols unchangedthroughrun. Repro: py -3 -B research-2026/team-current/lead/certify_local_ridge.py. Thisreralsooverwritesresultwithoutposthocsourcehashattach; arithmeticresult deterministic. Localtarget rational bounds fixedinscript.
