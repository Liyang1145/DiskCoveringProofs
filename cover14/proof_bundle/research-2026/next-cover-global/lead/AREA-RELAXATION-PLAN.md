# INVALID AS WRITTEN — owned-subarc wedge inequality fails

See AREA-WEDGE-LEMMA.md and DEAD.md. Numeric pruning outputs are NOT necessary-cover bounds and must never be promoted. Known symmetric controls passing did not validate asymmetric owned-subarcs.

# Global area / angle relaxation adapted from Fejes Tóth

Potential structural target: eliminate q11 or graph classes via a concave maximization upper bound on covered area, not numerical search for configurations.

For a normalized cover, each clipped Voronoi cell contains its center (all normalized centers inside D). Split each cell by rays from its site to consecutive vertices. Across an interior cell edge pq shared by sites ci,cj, the two triangles ci-p-q and cj-p-q are congruent (equal distances at both p and q, opposite sides). Their angles at the sites are equal, denote β_e∈[0,π]. Total area of the pair ≤r² sinβ_e. For a ring owner i, the remaining curved wedge has angle α_i∈[0,π] at ci; its boundary arc length ≤f(α_i)=2asin(r sin(α_i/2)), and its area ≤F(α_i)=(f−sin f)/2+(r²/2)sinα_i. This is the paper's formula rescaled from unitcoverradius to unit targetradius; requires separate derivation for endpoints possibly strictlyinsidecoverdisk, to be checked before certification.

Angle sums: interior hub Σ_(e incident)β_e=2π; boundary owner α_i+Σ_(e incident)β_e=2π. Boundary coverage requires Σf(α_i)≥2π. Functions f,F concave on[0,π] at r<1/2 (paper proves R>2). Thus feasible region convex and area objective Σ_e r²sinβ_e+Σ_iF(α_i) concave. Its maximum is an upper bound on areaπ necessary for covering. A supporting hyperplane / dual certificate can rigorously prove maximum<π without optimizing positions or assuming symmetry. Degenerate zero-length edges may be included as β=0; triangulation-added dual diagonals need compatible zero sector angles and must not doublecount cell edges.

First crude aggregate Jensen ignoring pervertex equations yields3.4244 forq10 and3.55056 forq11 atU, bothaboveπ; notenoughtoexclude. Pervertex constraints andhubdegrees may substantiallytighten. Calibrateonknownonehubn8/9/10 exactsolutions andcandidatebeforecataloguescan. Ifcandidateboundnotsharp, only useascoarsepruner, notsharpglobalmethod.

Originalgoalunchanged; thisisrouteproposal, no newclaim.
