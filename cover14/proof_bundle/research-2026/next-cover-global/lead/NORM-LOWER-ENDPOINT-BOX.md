# New structural route: exclude artificial zero endpoint corner

Analytic proposal, no certifiedgraphcount. Innernormnormalized centers satisfy|c|<=sqrt(1−r²), so everyunitboundaryendpoint hasdistance >=δ(r)=1−sqrt(1−r²)>0. The earlier jointcornerbound usedthelargerbox[0,r]² andcouldmaximizeat(r,0), impossiblefornormalizedcenters. Replacing with[δ,r]² leavescorners(r,r),(δ,r),(δ,δ); diagonalscale monotonicity makes(δ,δ) dominatedby(r,r).

Important fixed-Uinterface: doNOTreplaceδ(r) withδ(U) forr<U. Instead, for purpose ofexcluding existenceatanyr<=U, enlargeallcoveringdiskstoU first, performinnerrootnormalization atU, then obtain theglobalgraphrepresentation for thisU-cover. Outwardclip radiusrhoε mayexceedU, but compactlimitsrestoreU andδ(U). This maychangetheassociatedgraph, so resultingconclusion is existenceofone survivingU-system, notpreservationofeachoriginalr-graph. Needaudit implication beforepromoting.

Two cornerfunctions now:
 Frr(α)=U²sinα/2+g(2asin(U sin(α/2)))/2+ν·2asin(U sin(α/2)), alreadyconcave;
 Fδr(α)=δU sinα/2+g(2asin(d/2))/2+ν·2asin(d/2),
 d²=(U−δ)²+4Uδ sin²(α/2).

Crossbranchneednotconcave, so doNOTreuse Frr tangents. Needverifiedunivariatesupport (analyticconvexitysplit orintervalbranchbound). Existingpiecewiseaffine capacityh maystillapply. Endpointlowerδ removesimpossiblezeroarea highperimetercorner withaminimalpositivebutboundedchord. Atα=0, chordU−δ instead ofU. Candidatecontrol andknownsymmetriclimits required.

Bounded nexttest: optimizecrossbranch numericallywiththeknown dualpotentials on12closestnonexcludedfulljointsystems; compareupperbound loss. Onlyifpotentialstructuralgain, provefiniteanalyticpartitionorverifiedintervalsupport. No densecataloguegrid beforekernelcertified.

## Boundedtest outcome
Alternative uniformlowerendpointδ_q=1−cos(π/q) follows directly from2π<=q·2asinr ⇒r>=sin(π/q), thenδ(r)>=δ_q. This avoidsU-enlargementinterface butislooser.
`lower_endpoint_probe.py` tested12closestavailablejointsurvivors withδ_q. NUMERIC: all12activeboundscomefromsymmetric(rr)branch, notzeroendpointcorner; replacingcrossbranchchangednone. Thus thisrefinementcannotaddresscurrent12exampleswiththeirsavedduals. DoNOTscaleitnow. Thisismethodlimit, notdisproofoflowerendpointlemma.
