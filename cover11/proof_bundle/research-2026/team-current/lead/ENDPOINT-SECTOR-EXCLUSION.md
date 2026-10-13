# Uniform exclusion of the two common-hub endpoint sector degeneracies

## Scope
Unit closed disk covered by11equal disks at allowance r∈[3/8,U], U=37999/100000. Use inward representative, established q0(6,7) graph: ring0..8, hubs9,10; common hub-adjacent ring endpoints0and4. No symmetry/saturation assumption. Conclusion: sectoralpha_i cannot equalpi for i=0or4. This is a proper boundary exclusion, NOT sharp optimality or exclusion of other7sector degeneracies.

## Exact interface
Let P,Q unit boundary switches of sectori, full nearest widthw∈(0,2asinr]. Rotate toP=(k,h),Q=(k,−h) wherek=cos(w/2),h=sin(w/2). Ifalpha=pi, center lies on chordline: c=(k,y). All inwardcenters have norm<=sqrt(1−r²). Hence
 k²+y²=|c|²<=1−r²<=k²,
forcing y=0, k=sqrt(1−r²), w=2asinr and |P−c|=|Q−c|=r. No equalendpoint premise is assumed.

Keep this same geometric cover. Merely express metric lengths inunitsR0=19/50, with unchangedunit target and centers. All normalized localradii<=r/R0<=1. Every angularclosure/area/matching identity of C820 persists; it was provedgeometrically atactualr and doesnotneed newinwardnormatR0. The remainingnewcorner isalphaπ,u=v=t=r/R0∈[75/76,1]. Widthw=2asin(R0t) exactly. All otherfactor domains in certifiedq0kernel atR0 are validrelaxations; qmin follows ninewidthsum2pi andwidth<=2asinr<=2asinR0. See ENDPOINT-SECTOR-EXCLUSION-INTERFACE.md.

## Exact dual accounting
Use q0_closure_dual_0_4.json coefficients roundedto9decimalplaces, interpretedasexactrationals. Coefficient signs andgraph incidence assertedbykernel. check_endpoint_sector_symbolic.py expands independentformalresiduals and factorassembly withFraction: allcoefficients cancel exactly. Nonnegativeedge multipliers multiplyknownDelaunayangleslacks; lambda/eta0here. Thus actualareaπ<=constant+sumfactorvalues<=constant+sumfactorupperbounds, withoneringsupremum replacedbyconditionalcornerbound. This uses establishedglobalgraph/closure and refinedDelaunay conditions, not arbitraryflatmetrics.

Every unrestrictedfactor is bounded on its full continuous domain by the audited intervalkernel of CLOSURE-KERNEL-ANALYTIC-AUDIT.md. Output endpoint_sector_corner.partial.json contains29completeorderedfactors. Initial22factors tolerance.00015; last7tolerance.0006; tolerances controlstoppingonly andneverreplaceactualintervalupper. Earlier ring2 tighttolrun stoppedfor unnecessaryaccuracy, completed22bounds retained; no pendingboxboundfromstoppedfactor used. Retryfinishedring2 with148681evaluations and allremainingfactors. Eachstoredfloat upper was outwardnextafter ofintervalendpoint, hence anexactdyadicupper whenparsedback byiv.

Conditionalfactor fori is
 F_i(t)=(w−sinw)/2−mu_i*pi−(d_i+e_i)t²−(dl_i+el_i)t+lambda*w+(hl_i+hr_i)w/2.
Fori0,4 the quadraticandlinear coefficients cancel EXACTLY andlambda0. LetH=(hl+hr)/2. Then dF/dw=sin²(w/2)+H >=(3/8)²+H=230338243/2000000000>0. Thus true supremumat t1. Independently a1000boxdirected1Dcover givessup<−.0494554644; derivativeproof gives supin[−.049459584035604419039697407376812700536994670203002,−.049459584035604419039697407376812700536994669890994]. Both imply rationalupper−9891/200000. Files check_endpoint_segment.py and check_endpoint_segment_analytic.py.

Assembleall29factors, omitringi,add rationalcornerupper:
 i0 area <=3.13814481436995130305110649100038994184017254<pi;
 i4 area <=3.13811637509114675917510947719693165090318515<pi.
Contradiction. Output endpoint_sector_uniform_certificate.json.

## Repro/evidence
py -3 -B research-2026/team-current/lead/certify_endpoint_sector_corner.py
py -3 -B research-2026/team-current/lead/check_endpoint_segment.py
py -3 -B research-2026/team-current/lead/check_endpoint_segment_analytic.py
py -3 -B research-2026/team-current/lead/check_endpoint_sector_symbolic.py
py -3 -B research-2026/team-current/lead/assemble_endpoint_sector_certificate.py

Full-domainintervalimplementation is shared with earliercertificates; this is not independentsecondcontinuumcertifier. Independentrepresentations: exactnormsandwich; Fractionassembly; derivativevs1Dintervalcornerproof. A memberinterfaceauditwas corrected to remove equalendpointassumptionandcoordinate-rescalingnotation; itsidentityisnotproof.

Next possible gain: quantitative endpointheightgap or α<=pi−eta using enlargedcornerband. Other7sectors remainallowedtohaveheight0. Sharpglobalangleinequalityunresolved.
