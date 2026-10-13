# Cover-to-finite-angle-systems theorem, including degeneracies

## Statement
For any cover of the closed unit disk D by at most14 equal disks of radius 0<r≤U=.33173203427623414, apply C1171's coverage-preserving normalization/merging. There exist q∈{10,11}, N=q+m≤14, a graph G in the fixed indexed catalogues below, and t∈[0,π]^(q+|E(G)|) such that

    B_G t=2π 1_N,
    π ≤ cap(U)+(U²/2)Σ_(j<q)sin t_j+U²Σ_(j≥q)sin t_j,
    cap(U)=π(1−sin(2asinU)/(2asinU)).

Catalogues: q10/m3 and m4 are the ordered lists `k10-catalogue-corrected.json` (68+932); q11/m3 is `q11-pocket-catalogue.json` restricted to `q11-double-chord-pruning.json`'s1042 retained indices. This is a NECESSARY relaxation, not an equivalence or realizability assertion.

## Proof: angle variables pass to the same subsequence as graphs
C1171 supplies distinct normalized fixed sites, q positive boundary owners, hidden full cells inside D, and outward-clipped domains D_(1+ε) at allowed covering radiusr+ε. For sufficiently small ε>0, normalized radiusρ_ε=(r+ε)/(1+ε)<1/3, positive owners persist, and no other cell touches the outer circle. Its regular dual collar has the same q ring vertices and m hidden vertices. Triangulate nontriangular primal-vertex dual faces by the permitted hub-fan rule; the resulting graph belongs to the finite q10 or q11 catalogue. All strict arc inequalities used by C1171/C1177 hold for sufficiently small ε, since they hold strictly atU. Thus the1042 q11 restriction also applies along this sequence, even ifρ_ε>U.

For each such ε, work in its normalized unit disk. Assign to every real facet edge the angle β_e swept by that segment from either incident site. Reflection in the perpendicular bisector swaps the two sites and fixes both facet endpoints; hence the two facet triangles are congruent, and the two site angles agree. No isosceles-triangle assumption is needed. The facet's supporting line does not contain either site (sites are distinct and each is in the interior of its Voronoi cell); all vectors from a site to its facet therefore lie in an open half-plane, so β_e∈[0,π). Assign β_e=0 to each added dual fan diagonal. Such a diagonal corresponds to coincident primal endpoints at the same multiple vertex; it contributes zero angle and area at both incident sites.

For each boundary owner, let θ_i∈(0,2asinρ_ε] be its owned arc. With n the outward normal of its endpoint chord and h=θ_i/2, each endpoint has x·n=cosh. Inner-norm normalization gives |c_i|<sqrt(1−ρ_ε²)≤cosh. Thus both endpoint vectors from c_i have STRICTLY positive n-component. The curved boundary's angular sweep α_i viewed from c_i is the minor angle in(0,π); the whole short arc lies in that outward half-plane. This reasoning invokes no tangents from an interior point (such real tangents do not exist).

Convexity of each clipped cell and the fact its site is interior show its boundary wedges partition a full turn: α_i+Σ_incident β_e=2π for a boundary site, Σ_incident β_e=2π for a hidden site. Added zero angles do not change these identities. The same wedges partition the disk in area. The pair of straight-facet triangles has total area≤ρ_ε²sinβ_e. Each curved wedge has area≤(ρ_ε²/2)sinα_i+(θ_i−sinθ_i)/2. Convexity g''(θ)=sinθ≥0 on[0,2asinρ_ε] gives total segment area≤cap(ρ_ε). This proves the requisite angle/area inequalities atρ_ε.

Now choose a sequence ε→0 and a constant labelled graph subsequence as in C1171 (relabel once to its stored representative). Each t_ε lies in the compact cube[0,π]^(q+|E|); take a convergent subsequence. Linear angle equations and the area inequality pass to the limit by continuity, giving the displayed conditions at radiusr. Finally r²≤U², every sine is nonnegative, and cap(r)≤cap(U), so they hold atU.

For the last monotonicity, putL=2asinr∈(0,π). The derivative ofsinL/L is(LcosL−sinL)/L²<0: sinL−LcosL vanishes at0 and has derivativeLsinL>0. Hencecap is increasing. No numerical monotonicity premise is used.

## Exact exclusion and enumeration outcome
`area_safe_catalogue.py` proposes one supporting plane per2042 graph systems, using the formula in AREA-SAFE-RELAXATION.md. The proposal optimizer need not be correct or even feasible: the exact bound depends only on the stored rational angles and node potentials. Directed240-bit intervals establish strict upper bound<π on441 graphs:

- q10/m3:38 excluded,30 retained;
- q10/m4:148 excluded,784 retained;
- q11/m3:255 excluded,787 retained.

Thus every cover at radius≤U maps to one of **1601 remaining systems =814 q10 +787 q11**. Retained does NOT mean realizable. Smallest exclusion margin by family exceeds .01723708, .00035315, .00038273 respectively.

`area_safe_fraction_replay.py --catalogue` independently re-evaluates all441 excluded supporting planes using exact Fraction arithmetic, an independently coded rational interval layer, integer-scaled square-root enclosure, and Taylor/Machin constants. It does NOT import the dyadic I kernel or call any optimizer. All441 signs agree. Full proposed planes: area-safe-catalogue.jsonl; audit hashes/counts: area-safe-catalogue-metadata.json; independent replay: area-safe-catalogue-fraction-replay.json; explicit retained indices: area-safe-retained.json.

Known controls: area-safe-known-controls.json (n7,8,9,10 optimal star examples not excluded); area-safe-geometry-control.json reconstructs the saved actual14-cover's facet angles, area and sums. These are numeric calibrations, not substitutes for the analytic proof or exact plane evaluation.

## Remaining gap
This removes441 additional graph classes globally but neither proves the remaining1601 impossible belowr* nor derives a sharp bound on the candidate's class. C1182's local exclusion is separate. The unrestricted optimum remains open.
