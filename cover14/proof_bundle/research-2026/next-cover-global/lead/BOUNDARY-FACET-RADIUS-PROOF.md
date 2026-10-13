# Extension of radius-deficit lemma to boundary facets

## Analytic theorem
The face-imbalance inequality of C1222 holds for EVERY triangular dualface, not only faces with three interior dualedges, in the C1199/C1172 clipped Voronoi representation. Boundaryedges use an auxiliary angle defined below, not a fictitious geometric triangle.

## Proof of the missing orientation/angle interface
Take boundary dualedge uv, actual facet segment from circumcenter O_f to boundary switch A. Coordinates u=(0,0),v=(l,0),l>0, with triangle's thirdsite w=(w_x,w_y),w_y>0. The perpendicular bisector has points z=(l/2,h). Globallynearest inequalities for u versus w give

 |z−u|² <= |z−w|² ⇔ 2z·w <= |w|² ⇔ h <= (|w|²−l w_x)/(2w_y)=h_f.

The last quantity is the ordinate of O_f. Hence A=(l/2,h_A) with h_A<=h_f. Both endpoint vectors from u have positive firstcoordinate; their principal bearings belong to(−π/2,π/2). If γ_f is the angle at w, then bearing(O_f−u)=π/2−γ_f, so

 β = π/2−γ_f−φ_A,   φ_A=atan(2h_A/l).

Define virtual angle γ_A=π/2+φ_A∈(0,π). It follows EXACTLY that
 γ_f+γ_A=π−β,
 R_f sinγ_f=l/2=ρ_A cosφ_A=ρ_A sinγ_A,
 whereρ_A=|A−u|=|A−v|<=r.

These are all the premises used by the edge deficit proof. Therefore D_e=(U²−R_fρ_A)sinβ >= U²(1−cosβ)|γ_f−γ_A|/2. Pairedfacetarea is R_fρ_A sinβ by congruence, as for interior facets. No triangleangle atA is asserted.

For every face f, use its real opposite angle γ_fe on each of its three edges and the corresponding real-or-virtual other angle γ_other. ThenΔ_fe=γ_fe−(π−β_e)/2, andΣ_e Δ_fe=(Σ_e β_e−π)/2 followsfrom the REAL face'sangle sumπ. Thus for ALL dualfaces

 Σ_{e⊂f}D_e >= U²/2 ·min_{e⊂f}(1−cosβ_e)·|Σ_{e⊂f}β_e−π|.

Boundaryedge belongs to one face, interior edge to two. Edge-disjointfacepacks sum with no doublecounting regardless of type. Summingallfaces and dividingby2 is safe (possiblyloose onboundaryedges).

## Degeneracies / radius limit
Distinctsites and genuinefaces in outwardclippedrepresentations provide l>0,w_y>0. Fan-diagonals haveβ=0, contribute0, and anyface involvingone hasminweight0, so no extension issue. First prove at radiusρ_ε with allfacetendpointdistances<=ρ_ε. Pass to constant-graph compactsubsequence ofangles andradii, ε→0 BEFORE replacingr byU. This avoidsclaimingρ_ε<=U. Expression De and finalfacebound continuous; β=π forcesbothoppositeangles0. Increasingr toU only increases relaxedbudget andthe deficit expression paired with it is the actualendpointarea; the directedgeproofappliesatU withfixed endpointdistances<=r<=U.

## Calibration, not proof
`boundary_radius_control.py`: all10boundaryedges ofactualsavedcover havepositivevirtualangles, sharedlengthresidual<2e−14; all16faces satisfydeficitbound numerically. This exercisesbothinterior andboundary formulas, but proof is coordinate/nearest inequality above.

Next bounded test: use allfacepenalties onclosest12survivors; certifyintervalsuprema and independently replay partitionANDedgecounting before anygraphcount claim.
