# Unifying exact corner area and normalized perimeter capacity

Analytic interface draft; no exclusion yet. Let h(α) be C1217's concave piecewiseaffine bound on eachactualθ. For ν,λ≥0, using area=π, Σθ=2π andΣh≥2π gives

 π+2π(ν+λ) ≤ Σboundary[wedgearea+νθ+λh(α)] + Σfacetpairarea.

This is just addition of λ(Σh−2π)≥0, not an unjustified exchange ofmaxima. Jointcorner theorem bounds eachboundaryterm by

 max(F_ν(α), c_ν)+λh(α),
 F_ν=r²sinα/2+g(b_r(α))/2+νb_r(α),
 c_ν=g(A_r)/2+νA_r.

F_ν is concave by JOINT-EXACT-CAP-CONCAVITY.md. For a rational tangentpointt, F≤F(t)+F'(t)(α−t). Thus after subtracting sitepotentialyα bothbranches are piecewiseaffine when combinedwithλh. Their maxima occur at0,thetwohbreakpoints,π. Exactintervalevaluation certifies the upperbound for ANYrational ν,λ>=0,sitepotentials,tangencies. SampledLP maypropose, nevercertify.

This unifies two previously separate relaxations. λ=0 recovers exact jointboundarysupport. ν=0 allows the innernormcapacity to bear moreofperimeterrequirement while the cornerbound stillpenalizesunequalendpointtrianglearea. Atfixedr<=U, maximizeover endpointbox[0,U]² directly anduseh_U (C1217transfer); no unprovedmonotonicity ofoptimizedrelaxationneeded. Outwardclip passeslimit first.
