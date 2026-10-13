# Analytic audit — FIXED-ANCHOR-CONVEX-REDUCTION.md (SOCP elimination + elementary dual)

Auditor: dirichlet-cut-audit-cc2. One focused analytic pass. No numeric jobs, no claims, no review
events; only this file written. Audited: `lead/FIXED-ANCHOR-CONVEX-REDUCTION.md` (17 lines), using the
already-audited `lead/DEGREE-COVER-WITHOUT-EMBEDDING.md` interface
(`members/dirichlet-cut-audit-cc2/DEGREE-COVER-REPORT.md`). C1172 is taken as an explicit conditional
input and is not audited.

## 0. Verdict

**No hidden obstruction to eliminating all site and face-witness coordinates at fixed anchors.** The
program is correctly stated, genuinely convex (an SOCP) in the unknowns at fixed anchors, and its
constraints match the degree-cover theorem's conditions one-for-one, so feasibility with r < 1 does give
a 14-disk cover of D. The elimination is exact in the following scope: at fixed combinatorial type K and
fixed anchors, V_K(A) is exactly the optimum of its witness-certificate family, and the *global* infimum
of V_K(A) over the catalogue and the strict ordered anchors equals the original optimum via the
existential extraction plus sufficiency (no per-extracted-type equality is claimed: a feasible point
yields *some* cover, whose own nearest/Voronoi type need not be K). The only bearing input outside the
program is
the **conditional necessity extraction from C1172** (catalogue completeness + normalized Voronoi data),
which must stay explicit and is not audited here. The elementary dual is correct as written (sign
conventions, Cauchy–Schwarz, separable interval version, gauge caveat), and strong duality via Slater
identifies its supremum with V. What genuinely remains nonconvex and cannot be moved into the program is
the anchor manifold itself: anchors on S¹ in cyclic order with gaps in (0,π) — and that residual
nonconvexity is not an accident of the formulation but exactly what encodes the target region D (polygon
plus caps); see §4.

## 1. The program: statement, convexity, and exact matching with the cover conditions

1.1 Variables: c_v ∈ R² for the 14 sites (28 coordinates), w_f ∈ R² for each of the 16 real faces
(32 coordinates), r ∈ R. Constraints:
  (K1) ‖c_v − w_f‖ ≤ r for every incidence v ∈ f (site-face witness condition);
  (K2) ‖c_u − A_e‖ ≤ r and ‖c_v − A_e‖ ≤ r for every boundary edge e = uv (with A_e ∈ S¹ fixed).
Both families are second-order cone constraints in the joint variables: (c_v − w_f, r) and (c_v − A_e, r)
belong to the second-order cone, so the feasible set is convex and the objective min r is linear ⇒ SOCP.
The convexity claim in the file ("globally convex in all unknowns with FIXED anchors") is correct.
1.2 Slater and attainment. r = 2 with all c_v = w_f = 0 is strictly feasible (‖0‖ = 0 < 2,
‖0 − A_e‖ = 1 < 2), so Slater holds — this is the file's "take big r". Boundedness of the level set
{(c,w,r) : constraints, r ≤ R₀} needs the site-face incidence graph (sites joined when incident to a
common real face, plus the boundary-edge incidences), not just the boundary incidences: a boundary site
is bounded directly by ‖c_v − A_e‖ ≤ r ≤ R₀, a hidden site has no anchor incidence, but K is a connected
triangulated disk, so that graph is connected and every hidden site v reaches a boundary site along a
finite path v = v_0, f_1, v_1, f_2, …, v_k; for two sites incident to a common face,
‖c_u − c_{u'}‖ ≤ ‖c_u − w_f‖ + ‖w_f − c_{u'}‖ ≤ 2r ≤ 2R₀, so each step adds at most 2R₀ and
‖c_v‖ ≤ ‖c_{v_k}‖ + 2k R₀ is finite. Then each w_f is bounded by ‖w_f − c_v‖ ≤ r for any v ∈ f. Hence
the level set is closed and bounded, so V(A) := min r is attained. Both facts are what make "strong
duality identifies the supremum of the elementary bounds with the fixed-anchor optimum" legitimate; they
are not stated in the file and should be (P2, §6). (Correction: the earlier claim that "each c_v is
within 2 of the fixed anchor of any incident boundary edge" is false for hidden vertices, as noted; the
propagation above, with r ≤ 1 in the interesting branch, is the correct bound — each site-to-site step
≤ 2r ≤ 2 there.)
1.3 Trivial scale check. r = 1 with all points at 0 is feasible (‖0 − A_e‖ = 1), so V(A) ≤ 1 always; a
single disk of radius 1 at the origin already covers D. The whole content is therefore the nontrivial
branch V(A) < 1, which is exactly the r < 1 hypothesis of the file.
1.4 Match with the earlier interface (this is the reason the elimination is sound). The degree-cover
theorem needs, for the augmented PL disk K+ on the fixed anchors: (i) the boundary loop winds once about
**the interior of the anchor polygon P** (not about the interior of D; the part of D outside P is handled
separately by the owner-assigned caps) — supplied by "ordered anchors, consecutive arc gaps ∈ (0,π)";
(ii) per real triangle a common witness within r of its three site images — exactly (K1) with witness w_f
(the theorem's witness need not be equidistant and need not be a site); (iii) every site-anchor incidence
within r — exactly (K2). Three consequences I checked explicitly:
 - Virtual triangles A_e u v: covered by the site disks at u,v because ‖c_u − A_e‖, ‖c_v − A_e‖ ≤ r and
  the image midpoint M = (c_u + c_v)/2 satisfies ‖M − c_u‖ = ‖c_u − c_v‖/2 ≤ r, the distance being
  maximized at a vertex of each half-image triangle.
 - Owner triangles v A_prev A_next and the exterior caps: both anchors adjacent to the owner site v are
  the anchors of its two boundary edges, so (K2) gives both distances ≤ r; convexity gives the owner
  triangle, and the cap follows from the single-arc lemma (U = r ≤ 1; the sites need not lie in D).
 - Nothing else is needed: no site positivity/nondegeneracy, no equal distances, no sites inside D, and
  coincident sites are allowed (the theorem permits repeated images). So the constraint list is neither
  missing a condition nor over-specified.
1.5 Counts. For q = 10, m = 4 the program has 28 + 32 + 1 coordinates and the covered configuration has
28 site coordinates (27 modulo the joint rotation gauge that the anchor frame already fixes) plus 32
witness coordinates — the file's "not 27 center parameters or 38 beta/anchor parameters" is a correct
bookkeeping statement inherited from the earlier q11 context: **28 β variables + 11 anchor log-radii
− 1 global scale = 38** (corrected: these are β variables and anchor log-radii, not centre coordinates).
That reference should not be mixed with the present q10 instance: there the anchor family contributes
q − 1 = 9 arc parameters after fixing one rotation. (The q10 β/anchor bookkeeping — 29 β + 10 anchor
log-radii − 1 global scale — also totals 38, but as a separate coincidence, not by the same explanation.
Keep the two counts apart.)

## 2. What the fixed-(K,A) program does and does not say

2.1 Sufficiency (unconditional given feasibility). A feasible point with r < 1 yields an actual cover of
D by the 14 site disks of radius r, by §1.4 and the degree-cover theorem. So for every K and strict
ordered anchor configuration A,
  r_D(14)  ≤  V_K(A)      whenever V_K(A) < 1.
The cover produced is *some* cover; its own extracted nearest/Voronoi type need not be K and its anchor
set need not be A.
2.2 Necessity (conditional on C1172). If a cover with radius r has extracted type exactly (K,A), the
extraction of §3 produces a feasible point of the (K,A)-program with that r, so V_K(A) ≤ r. Equivalently:
V_K(A) is a lower bound for the radii of covers whose extracted type is (K,A). This is the only direction
in which the type and the anchors re-enter.
2.3 What is *not* implied. Equality V_K(A) = (radius of the smallest cover with extracted type (K,A)) is
**unsupported** and must not be asserted: the sufficiency in 2.1 returns a cover whose extracted type may
differ from (K,A), so the two sides of that equality are optima of different families. What is valid is:
 - V_K(A) is exactly the optimum of the *witness-certificate family* for (K,A), i.e. of the program
   (K1)–(K2) with those anchors — trivially, by definition of V_K(A) as that program's value;
 - the *global* statement, using the existential extraction and the sufficiency together:
     r_D(14) = inf over catalogue types K and strict ordered anchor configurations A of V_K(A),
   where "≥" comes from 2.2 applied to each cover's extracted type (every cover has some type in the
   catalogue and some anchor set) and "≤" from 2.1 together with the trivial bound V ≤ 1. No per-type
   equality is used or claimed.
The elimination statement should be read with exactly this scope: the site and witness coordinates of a
*given combinatorial type at fixed anchors* are eliminated (their 60 coordinates are optima of a convex
program, not outer search variables), while the catalogue choice and the anchors remain the nonconvex
outer freedom. Two qualifiers belong in the same sentence: the discrete catalogue K is a finite nonconvex
choice, and the global identity uses the conditional extraction of §3.

## 3. The necessary direction — must stay explicit (C1172), with its elementary content

The file's "Conversely actual normalized cover Voronoi data supply such witnesses (C1172)" is the right
form. Everything after "Thus" is conditional on it, and nothing in §1 can supply it. I record why the
necessity is nevertheless elementary *given* the normalized structure, without auditing C1172:
 - Site-face witnesses. In the normalized structure the real faces are the site triples whose Voronoi
  cells meet; take w_f = the Voronoi vertex (circumcentre) of that triple. It lies in D, so some disk of
  the cover has centre s with ‖w_f − s‖ ≤ r; the nearest site to w_f is one of the triple's three sites
  and is at most as far as s; equidistance then gives ‖w_f − c_v‖ ≤ r for all three v ∈ f. This is even
  an *equal-distance* witness, so the program's (K1) is a strict relaxation of the extracted data.
 - Site-anchor incidences. The anchor A_e is the switch point at which a Voronoi edge of the two
  incident sites meets S¹; A_e ∈ D is covered, so the nearest-site distance at A_e is ≤ r, and the two
  incident sites are at exactly that distance (equidistance), giving ‖c_v − A_e‖ ≤ r for both.
 - What C1172 (with C1171/C1168) must add is therefore the *structure*: that every cover's normalized
  extraction has a type K in the catalogue with the boundary arcs ordered on S¹, and that the anchors so
  defined are the ones used in the program. That structural input is not audited here, and the report
  should not read as if the convexity of the program proved it.

## 4. Hidden-obstruction checklist for the elimination (searched; all cleared)

(O1) Auxiliary witnesses: w_f is not a cover parameter, so eliminating it does not add disks to the
cover; the cover still uses exactly the 14 site disks. Cleared.
(O2) Site degeneracies: the program allows coincident sites, collinear/zero-area images, inverted
triangles, and sites outside D — all permitted by the degree-cover theorem. Cleared.
(O3) Missing virtual/owner/cap conditions: subsumed by (K2) exactly (§1.4). Cleared.
(O4) Boundary/winding condition: fixed by the anchor hypothesis (ordered, gaps ∈ (0,π)), not eliminated;
it is an input, and correctly so. Cleared as an input.
(O5) Catalogue: finite and discrete, hence outside the convex program; the reduction is exact per (K,A)
in the sense of §2 (witness-certificate optimum, with the global identity obtained by existential
extraction, not per-type equality). Cleared as a finite outer search.
(O6) Degeneracies of the anchors (repeated anchors, zero gaps): excluded by the strict statement and left
to the documented compact-limit interface; this is consistent with the weak-order/collapse treatment in
`DEGREE-COVER-REPORT.md` §7 (increments in [0,π), total 2π, contracting zero runs gives a convex polygon).
Cleared as a scope statement.
(O7) Is (K1) too weak to give a *necessary* condition? No: for a lower bound one needs the program to be
a relaxation, and §3 supplies the (stronger) equal-distance witnesses; the relaxation and the sufficiency
direction then give the global identity of §2.3 (each feasible point yields some cover), without any
per-extracted-type equality. Cleared.
(O8) Is anything lost by not constraining the sites to a bounded region? No: with r ≤ R₀ the sites are
bounded by propagation of site-to-site distances ≤ 2R₀ along the connected site-face incidence graph to
an anchored boundary site, and hidden sites are confined through their witnesses. Cleared.
(O9) Could freeing the anchors make the whole thing convex without loss? No, and this is the structural
point: the norm constraints are already convex in the *Cartesian* anchor coordinates, so the only
nonconvexity is "‖A_a‖ = 1 and arcs ordered with gaps ∈ (0,π)". Freeing the anchors would leave the
constraint set convex but would change the target region: the PL boundary would be some convex polygon,
not the inscribed unit polygon, and D would no longer be the disjoint union of that polygon with the
owner-assigned caps. So the residual nonconvexity is not an artefact; it is exactly what encodes the
target disk and the cap tiling. Cleared (no removable obstruction; the obstruction is essential).
(O10) Global rotation: V is invariant under rotating anchors and free points together, but a concrete
flow's bound (and each box certificate) is built in a specific gauge; the file's "global rotation can be
fixed at one anchor; each flow must be used in that gauge" is the right handling. Cleared.

## 5. The elementary dual — verified, with the exact validity conditions

5.1 Derivation. Orient each incidence edge from tail to head, where every anchor is a head; p_e =
x_tail − x_head, so ‖p_e‖ ≤ r by (K1)/(K2). Choose flows z_e ∈ R² with exact balance
Σ_{out} z_e − Σ_{in} z_e = 0 at every free vertex (sites and witnesses). Then
  Σ_e z_e·p_e = Σ_{free x} x·(balance_x) + Σ_a A_a·[Σ_{tail=a} z_e − Σ_{head=a} z_e]
             = −Σ_a A_a·b_a =: L_z(A),   b_a := Σ_{e: head = a} z_e,
which matches the file line for line (the sign convention is correct precisely because no edge has an
anchor as tail). Cauchy–Schwarz per edge gives Σ z_e·p_e ≤ r Σ‖z_e‖, hence
  r ≥ L_z(A)/Σ_e ‖z_e‖   for every feasible system with Σ‖z_e‖ > 0 and L_z(A) > 0.
No duality theorem is needed for this inequality; it is a valid lower bound on any feasible r exactly as
claimed. (If L_z(A) ≤ 0 the bound is vacuous, which is the only failure mode.)
5.2 Sharpness. Slater (§1.2) plus attainment gives strong duality, so the supremum over balanced flows of
L_z(A)/Σ‖z_e‖ equals V_K(A); the file correctly says "supremum" (dual attainment need not hold).
5.3 Floating-flow repair and interval arithmetic. A numerical multiplier candidate need not be exactly
balanced, but the balanced space is an affine lattice (solve the tree system exactly in rational
arithmetic after adding an anchor root; circulations are the remaining freedom), so an exactly balanced
z with a controlled perturbation is obtainable. Then the bound needs two directional bounds:
  numerator lower: L_z(A) ≥ L̲;   denominator upper: Σ_e‖z_e‖ ≤ D̄;   bound = L̲/D̄ < L_z/Σ‖z_e‖.
For anchors known only in angular boxes t_a ∈ [t_a⁻, t_a⁺], each summand −b_a·(cos t_a, sin t_a) =
−|b_a| cos(t_a − φ_a) has an elementary interval minimum, and because L_z is *separable* over anchors,
the minimum of the sum over the box equals the sum of the per-term minima. Under additional ordering /
gap constraints these per-term minimizers may be inconsistent; the sum of minima is then still a valid
(only weaker) lower bound, since the constrained angular set is a subset of the box. So "they sum
independently even when anchor ordering imposes more constraints, hence remain valid" is correct.
5.4 Gauge. V is rotation invariant (rotate the free points with the anchors), but L_z(A) is not: it is
evaluated at the anchors' absolute positions, so a flow constructed for one gauge must not be reused in
another. The file's gauge instruction is necessary; it is also the reason each box certificate must
record its gauge.

## 6. Precision list (P1–P7)

**P1 (bearing).** Attach the conditionality to the elimination sentence: "the remaining nonconvex freedom
is ONLY ordered circle anchors" holds *given* the C1172/C1171 extraction (§3) and the finite-catalogue
completeness. Without them the program is a relaxation only: it still yields covers from feasible points
and lower bounds, but no global identity. State the identity in the §2.3 form — infimum over (K,A) of the
witness-certificate optimum equals the original optimum — and do not state it per extracted type.
**P2.** Record Slater (r = 2) and boundedness of the level set via propagation of site-to-site distances
≤ 2r along the connected site-face incidence graph (hidden sites have no anchor incidence, so the
boundary incidences alone do not bound them); together these justify attainment of V and the
"supremum = optimum" statement.
**P3.** State the edge conventions of the dual explicitly (all anchors are heads; p_e = x_tail − x_head;
balance at every free vertex including witnesses), since the sign of L_z(A) depends on them.
**P4.** Note that (K1) is a strict relaxation of the extracted data (the Voronoi vertex gives an
equal-distance witness), which is why no equal-circumradius or empty-circle condition appears in the
program.
**P5.** Note V(A) ≤ 1 always, and that the r < 1 hypothesis delimits the nontrivial branch; a cover at
r = 1 is the single disk at the origin.
**P6.** Word the anchor count as "q − 1 = 9 arc parameters after gauge-fixing one rotation, plus the
ordering/gap constraints", and keep the discrete catalogue K separate from it; then no reader will read
"q − 1" as a claim that the anchor family itself is convex (it is not, as the file says: V is convex in
Cartesian anchor coordinates but the product of circles with ordering is not). Keep the inherited "38"
comparison figure attributed to its actual source, the earlier q11 bookkeeping **28 β variables + 11
anchor log-radii − 1 global scale** (not centre coordinates), and do not mix it with the q10 instance.
**P7.** Keep the degeneracy boundary explicit (repeated anchors / zero gaps need the compact-limit
interface; the strict statement excludes them), consistent with the weak-order treatment of
`DEGREE-COVER-REPORT.md` §7.

## 7. Scope of what this establishes

Establishes (conditional on the catalogue + C1172 extraction): for each fixed combinatorial type and
fixed ordered strict anchor configuration, the *witness-certificate optimum* V_K(A) is the value of a
finite SOCP in 61 unknowns, hence computable by convex programming, and lower bounds for it are
certifiable by elementary balanced flows with interval arithmetic — no site/witness coordinates remain as
outer nonconvex search variables of that family, and the infimum of V_K(A) over the catalogue and strict
ordered anchors equals the original 14-disk optimum (via the existential extraction and the sufficiency
conclusion; the cover produced by a feasible point need not have extracted type (K,A), so no per-type
equality is claimed). Does not establish: a global lower bound by
itself (no single flow is expected sharp; the cited fixed-stress obstruction concerns a different energy
and does not transfer, as the file says), the necessity extraction (C1172), any statement about repeated
or degenerate anchors, and no numeric certification (none was run). The report's §4 answers the direct
question — there is no hidden obstruction to the elimination — and identifies the one residual
nonconvexity as geometrically necessary rather than removable.

## 8. Next minimal obligation (one)

Put the C1172 conditionality into the same sentence as the "only ordered circle anchors" claim (P1) and
record Slater/attainment with the site-face-incidence propagation (P2). With those two, the fixed-anchor
reduction is a complete conditional theorem: convex in all eliminated coordinates, exactly the
witness-certificate optimum for each (K,A), globally equal to the original optimum through the
existential extraction, and certifiable by the elementary dual as written.
