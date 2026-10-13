# Rigorous two-sided bearing-sum collar (NOT a nonflat sector collar)

Scope both-low C849 alpha2=pi flatpatch, r∈[.379,.37999], bj∈[L,1], L=.60946080763725372899, |b1+b2−pi/2|≤.005. BOTH face-circle arcs are bounded in their ENTIRETY; no stationary-only or familygradient premise. Normcirclearcs not on eitherface remain unbounded by this result. The alpha2=pi assumption is unchanged.

## Chart coverage
Onfacej use(r,b_j,T,A), T=b1+b2, A=b_j∓delta; otherbearing=T−b_j. Legalwedge gives0<A<T, so initialA∈[0,pi/2+.005] containsalllegalpoints. Otherbearingfilterretains[L,1]. Coordinates v=r(sin2b+sin2A),t=±r(cos2A−cos2b) areexact. Normresidual is independentofreflection.

FACE-COMPLEMENT-REPRESENTATION.md givesother sourcecomponents without dividingbycosT, validonbothsides. Ownphi=A ande=rsinA/R0, since legal0<A<pi. Generalcomplementarysourceatan2 requiresfullsmoothbranch; refusalretainsbox. Firstorderchainrulecalibrationinface_totalangle_control.json verifiesbothreflections.

Oppositefacecapdifference sign is cosT*sin(2A−T)≤0. This is validforbothreflections; factorsH>0and4r>0 omittedonlyafterpositiveH check. Zero retained, coveringcoincidenceT=pi/2. The inputalsoincludesH=2rsin(b+A), so H≤0illegal.

## Critical near-wedge repair
Straight H²−2scosdelta H+2r(1−r) naturalinterval loses cancellation near source poles. Exact factorization:
 normresidual/(2r)=G(r,b,A)=1−s(sin2b+sin2A)−r cos(2(b+A)).
face_totalangle_jet.legal intersects its natural G bound with a FULL-EXTENSION centered firstorderMVT bound at boxmidpoint. G is smooth on entire r,b,A box. Positive lower means no legalpoint, even if objective extension contains a pole. Noobjective clippingor derivativeatpointremainderassumption isused. face_normcap_identity.json exactSympyfu identity.

## Complete cover
certify_coincident_collar.py sourcepins everykernel+frozencoefficients and twoinitialbranches. Fullbinarysubdivision:2880eval,0live,633illegal+808valueleaves. Maximumterminal28.106704253080107<28.10695. Probe and sourcepinnedreplay must agree before registration.

This removes an OPEN two-sided neighborhood of the coincident-face degeneracy from the facearc obligation (includingitsclosedends), strengtheningC874 exactsurface. It does NOT remove correspondingnorm-circlearcs, mixedbearings, nonflatalpha2 or globalcoveringconfigurations.
