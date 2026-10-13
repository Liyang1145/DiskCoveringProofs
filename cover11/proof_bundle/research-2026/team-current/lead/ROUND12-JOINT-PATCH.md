# Round12 durable result

Original target unchanged: unconditional sharpglobaloptimum n11. Globalboundsunchanged .375<r_D(11)<=C249. No sector2flat exclusion yet.

## Proved structuralgain
C849: boundaryfirstchart r,b1,b2,A,w1,w3,H; atfixed4outervariables widths lieexplicitindependentintervals[g,W(r,b)] andH liesC848interval. Sevenfactorobjective separates asconstant+3scalarfunctions. Analyticfiles FLAT-PATCH-ARC-CHART.md, JOINT-PATCH-SEPARABLE-FIBERS.md. Localnecessaryrelaxation, notglobalcoversufficiency. alpha canπ; W>=g mustbeexplicit. 6536chartcontrols, 8964independentedge/areaobjectivecontrols. Widthderivative checkedFDmaxerror3.84e-10; nonmonotone, noendpointshortcut.
WIDTH-STATIONARY-POLYNOMIAL.md derivesdegree8necessarypolynomial forfixedouterwidthstationarypoints. ExactSympy identities inwidth_polynomial_control.json. Squaringextraneousroots/identicallyzeropolynomial/parameterrootcollisions explicitlynotignored. Notyetclaimregistered.

## Numericaldecisions
exchange_joint_patch.py +refine:18jointLPexchanges; round17numeric3.138756005 belowpi. Nineold7Dalphastrataattack consistent but INSUFFICIENT.
Independentnested4D+3scalarprobe foundmissedpatch withcluster28.176071525 vs28.165342362; recalibratedtotal3.149485168>pi. OldproposalREJECTEDnumeric. joint_patch_frozen_v2.json sha256a856f2c12bcc24c428c2ac6044f81877059cc3039f73db992dc5e3e004c23636 remainsimmutable. 22otherfactorintervalboundsjoint_patch_bound_*.json completed, oldcombinedwithnumericcluster3.143243398 evenbeforeattack. TightpassstoppedPID26560afterattack, nofullcertificate. No mathematicalpropositiondisproved.

exchange_joint_nested.py rounds18..21 reoptimizedwithmissedpatchandnestedoracle. Best21numeric3.13782008466934; newimmutablejoint_nested_frozen.json coefficientsROUNDED9decimal; alloldintervalboundsINAPPLICABLE. Sixindependentseednestedattacks maxcluster28.10432238989225 vsold28.10425650870559; reconstructednumeric3.137885965856<pi. StillPROPOSALONLY: scalarinnersearch samples13gridandlocalpeaks, notrootexhaustion; outerDE notcoverage; notcertifiedupper.

## Audits
Membermetric-chart corecorrect; reportextrascorrected(sign>, Wfloor notautomatic, alphaπallowed). MembersharpHderivative coreuseful; actualr notR0 inareaterm; numericalendpointcounterexamplesnotproof. Fullsumtelescopingknownandirrelevanttopatchtwofacecertificate. Bothinactive/stopped. Leadproofauthoritative.

## Next executable obligation
Build rigorous scalarwidth/H upperenvelopes over4Douterboxes usingC849 andexplicitpolynomial/derivative forms, then boundedintervalattack ofnewfrozenproposal. Firstcalibratepointintervalwithindependentsum; domaincoverage includesbthreshold,W<g,alphaπ,A/Bpositive,Hfiberemptytest. Can firstattack bestcandidatefurther withroot-complete scalarwidthsearch; doNOTreuseoldcertboundsorclaimnumericmaxanupper. Mainsharpinequalitystillmissingevenifflatbranchremoved.
Alllocaljobsfinished/stopped; noactiveTeamassignments. ToolsPowerShell, py -3. Scriptsimportsrequireleadpath on sys.path orlaunchscriptdirectly.
