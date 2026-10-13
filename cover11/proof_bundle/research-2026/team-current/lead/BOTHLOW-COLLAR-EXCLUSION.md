# Both-low bearing-sum collar exclusion, exact flat sector

Object: C849 necessary flat relaxation, alpha2=pi, physical r∈[.379,.37999], both adjacent bearings≤1 and |T−pi/2|≤.005. This does NOT treat nonflat sectors or arbitrary coverings.

C850 gives both bearings≥L=.60946080763725372899>acos(r)/2. C872 maximizes both width fibers at their endpoints; this is valid independently of hub. C871 says every maximum of the remaining hub objective lies on one of the three disk circles. Compactness and absence of sourcepoles are given by LOW-BOUNDARY-ENDPOINT-COVERAGE.md: wedgeedges excluded by normdisk and ownfacedisk. Thus no missing open-domain supremum at a source.

C875 bounds ENTIRE bothfacearcs (includingendpoints,coincidence) by28.106704253080107. No stationary theorem is needed for thosearcs.

Newnormarc certificate: norm_totalangle_jet.py parameterizes FULLnormcircle v=s−(1−r)cosq,t=−(1−r)sinq,q∈[−pi,pi]; chart(r,b1,T,q), b2=T−b1. Bothface constraints use exact squaredCartesian residuals, naturalinterval plusfull-extensioncenteredMVT. They filter positive lower residualonly. Wedgefilter conservative. Feasible-valuebound clips onlyphysicalsourceverticalcap and e≤r/R0; derivativeMVT uses entirelyunclippedobjective. This distinction follows LEGAL-CARTESIAN-VALUE-BOUND.md.

norm_totalangle_control.json gives3 value/fullchainrulegradient comparisons tooriginalnormcirclechart (centralanglepi+q), while certifiedcontrolforlegal_cartesian_value.py was establishedinC873. certify_norm_collar.py fullbinarycover847eval0live47illegal377valueleaves; maximumterminal28.10683268798853. Allsourcehashespinnedandverifiedinassembly.

Consequently a conservative decimal bound for WHOLEhub and width family is F≤28.106833. Add the frozen constant+22-factor certificate upper from C849 chain, namely less than−24.96545276218283632963030154, giving total<3.141380237817164<pi. Thus the specified both-low bearing-sum collar contains NOfeasible flatpatch of the covering relaxation.

assemble_bothlow_collar.py verifies coefficientSHA and allcurrentcertificatekernelSHA beforeassembling detailedintervals. The rounded display uniform bound28.106833 is intentionally larger than storedfloatterminal, so decimal conversioncannot threaten the claim. No globaloptimality or entirebothlowpatch conclusion.
