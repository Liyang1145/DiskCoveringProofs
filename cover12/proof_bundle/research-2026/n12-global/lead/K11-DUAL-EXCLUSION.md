# Uniform k11 exclusion via two weighted circles

Level: proved-interval C998; directed-interval certificate plus analytic reduction, independently source/inference audited. Independent custom-kernel replay is supplementary and its critical-point branch repair is tracked in members/finite-reduction/onehub-audit/REPORT.md. Fixed rational U=0.361102963744508672616920293904. Scope: all covers with11 actual boundary-active disks at radiusU, centers arbitrary before projection/inner-root normalization. Together with reclassification after enlargement, also handles any r≤U cover whose radiusU enlarged configuration has11 active disks.

## Necessary geometry
Inner-root replacement makes each boundary ring center c=ρuφ with1−U≤ρ≤sqrt(1−U²), preserving boundary arcs and enlarging its portion withinD. The remaining hubh has norm e<1−U. Ring disks cannot cover the open coreB(0,1−2U), since ρ≥1−U. Closedness forces the hub to cover its closure, hence e+(1−2U)≤U, or0≤e≤3U−1. Rotate h onto the positive x-axis. Its whole radiusU circle lies insideD because e+U≤4U−1<1. At every point of that circle, approach radially from outside the hub; the11 ring disks cover those approaching points. Their closed union therefore covers the hub circle too. Thus rings cover bothS1 andS(h,U).

## Nonnegative measures and capacity
Take weights W(φ)=b0+bc cosφ+bs sinφ onS1 and V(ψ)=h0+hc cosψ+hs sinψ on the hub circle. Use angular measure divided by2, not arclength: total demand π(b0+h0). Exact condition b0≥|bc|+|bs| and h0≥|hc|+|hs| ensures nonnegativity everywhere.

A ring disk has boundary halfwidthα=acos((1+ρ²−U²)/(2ρ)). Putℓ=|c−h|>0. Its hub-circle halfwidthβ=acos(min(1,ℓ/(2U))), withβ=0 whenℓ≥2U. The direction ofc−h has cosine(ρcosφ−e)/ℓ and sineρsinφ/ℓ. Therefore its capture is
C=b0α+sinα(bc cosφ+bs sinφ)+h0β+sinβ(hc(ρcosφ−e)/ℓ+hsρsinφ/ℓ).
If sup C<π(b0+h0)/11,11 such disks cannot cover both weighted circles. This uses a union bound with nonnegative measures, not disjoint arcs or equal centers.

## Continuum certificate
lead/onehub_interval_certificate.py uses mpmath.iv (dps30) directed arithmetic, no numpy or nondirected float bounds. Exact rational inputU, exact decimal rationalized scout weights, full intervals:
ρ=(1−U)+s(sqrt(1−U²)−(1−U)), φ=2πp, e=(3U−1)q,
(s,p,q)∈[0,1]×[0,1]×[j/12,(j+1)/12], j=0..11.
Every arithmetic/transcendental operation on a bearing bound is interval-valued. acos on[0,1] is atan2(sqrt(1−x²),x); the clipping to[0,1] is justified by geometry forα and by the zero-cap branch forβ. ℓ>0 throughout sinceρ−e≥2−4U>0. Width/coordinate split priorities may use floats but partitions/acceptance cannot: each split is at the exact Fraction midpoint, and leaf acceptance requires interval upper C strictly less than interval lower demand/11. A stack becoming empty, with no discarded nodes, covers the complete box. Error/undefined coarse expressions cause subdivision, never acceptance.

Saved scout numerical values are not premises. Their positive rational weights are proposed, explicitly checked for nonnegativity, and then validated over the entire continuum. All12 segments passed in≈30s (not sampled e). Evidence: evidence/onehub-interval-all.json, with segment weights/counts/strict upper and target. Reproduce:
`py -3 -B research-2026/n12-global/lead/onehub_interval_certificate.py`

## Global interface and residual work
At radiusU, k11 is excluded if this kernel audit closes. If an arbitrary smaller-radius cover is enlarged toU then active count is reclassified, givingk9,k10,ork11; it is not legitimate to silently preserve the oldk count. k9 already has a sharp lower-bound theorem applicable to its own radius; for an original k11 cover enlargement cannot decreasek, and k≤11 atU, so this k11 exclusion rules it out. For original k10, enlargement may lead tok10 ork11, addressed accordingly. This note alone does not exclude all k10 covers.

The same certified one-hub two-circle inequality also excludes the separated/tangent(d≥2U) and coincident(d=0) two-hub branches, via lead/K10-SEPARATED-HUB-REDUCTION.md, where only10 rings need to cover these circles. Genuine k10 configurations with0<d<2U remain open.
