# Analytic audit — FLAT-DISK-REALIZATION.md + FLAT-DISK-ANGLE-INTERFACE.md (C1254 / C1257)

Auditor: dirichlet-cut-audit-cc2 (task routed on the verified commandcode2 channel). Scope: strict
sufficiency only, i.e. (1) do positive compatible triangles glue into a flat disk, (2) is
developing-map injectivity rigorous from the convex unit-cyclic boundary, (3) do original + virtual +
owner triangles + exterior circular segments give complete coverage of D. No claims, no review events,
no numeric hunts; only this file written (separate from `REPORT.md`).

Files read in full: `lead/FLAT-DISK-REALIZATION.md`, `lead/FLAT-DISK-ANGLE-INTERFACE.md`,
`lead/FLAT-DISK-STRAIGHT-OWNER-EXTENSION.md` (optional file; core passed, so inspected),
`lead/CYCLIC-POLYGON-CLOSURE.md` (C1251), `lead/BOUNDARY-CYCLICITY-PROOF.md` (C1252),
`lead/ODD-EVEN-BOUNDARY-TURN-ELIMINATION.md`. Context: `STATUS.md`, `DEAD.md` (refreshed).

## 0. Verdict

**No counterexample found. The sufficiency chain (glue → develop → boundary → degree → cover) is
correct as a conditional theorem, and the condition set it needs is exactly the strict-branch list the
interface file calls "Need".** Three items in that list are load-bearing and one of them is not
derivable inside these files (the per-anchor closure identity, §6-O1); the cap/segment step is stated
in one clause and needs the four-line proof in §5.4; the signed-turn/orientation step required by
C1251 is not spelled out (§6-O3). Nothing in the sufficiency direction uses a circumcenter-inside
assumption or a nearest-site/empty-circle fact — I re-traced every step for this (§3–§5), which is the
point the task asked to check. The reverse direction (Voronoi extraction) is untouched here and is
where nearest-site facts legitimately live. No global bound follows.

## 1. The abstract object, and which parts are data vs. consequences

Data (strict branch): oriented triangulated disk K with q boundary sites, m interior sites, all faces
nondegenerate triangles; paired β_e ∈ (0,π) for every edge of K; positive numbers R_f (real faces),
a_e (anchors); angles γ_{f,e} := atan2(T sinβ_e, R_f − T cosβ_e) with T = R_g for the face g across an
interior edge and T = a_e for a boundary edge. K+ (as in §5 of the realization file) is combinatorially
verified below.

Elementary facts I re-derived and will use (all are two-angle/three-side trigonometry, no Thales, no
nearestness):
(F1) Sine law in the centre triangle. For an interior edge e shared by f,g: the triangle
(O_f, O_g, u) has sides R_f, R_g, |O_fO_g| and angles γ_{f,e} (at O_f), γ_{g,e} (at O_g), β_e (at the
site u), summing to π. Hence
     R_f / sin γ_{g,e} = R_g / sin γ_{f,e}  ⟹  l_e := 2R_f sin γ_{f,e} = 2R_g sin γ_{g,e},
so the two faces of K automatically agree on the shared edge length once γ_{f,e}+γ_{g,e} = π − β_e
holds. No circle-intersection or nearest-site input is needed for the length agreement.
(F2) Same statement at a boundary edge e = uv with real face f and anchor A_e: triangle
(O_f, A_e, u) has angles γ_{f,e}, γ_{A,e}, β_e, hence l_e = 2R_f sin γ_{f,e} = 2a_e sin γ_{A,e}. Also
the virtual triangle A_euv is isosceles with apex angle 2γ_{A,e}, base angles π/2 − γ_{A,e} > 0 iff
γ_{A,e} < π/2, and base l_e = 2a_e sin γ_{A,e}.
(F3) Owner triangle at boundary site v: sides a_prev, a_next, included angle α_v at v, base
L_v² = a_prev² + a_next² − 2 a_prev a_next cos α_v, other angles δ_{v,prev}, δ_{v,next} = (π−α_v)/2 when
a_prev = a_next, in general from the sine law. θ_v := 2 asin(L_v/2) ∈ (0,π) iff 0 < L_v < 2.
These reproduce the interface file's identifications exactly; I found no convention mismatch. Slot
check (corrected): the general γ is γ = atan2(T sinβ, R − T cosβ) with the *other* radius T in the
y-slot and the *own* radius R in the x-slot. Hence γ_{f,e} = h(f,g) = atan2(a_e or R_g in y-slot,
R_f in x-slot), while γ_{A,e} = atan2(R_f sinβ_e, a_e − R_f cosβ_e) has **T = R_f (the real face's
radius in the y-slot) and the anchor radius a_e in the first/own slot R**, i.e. γ_A = h(A_e, f) with
the anchor playing the own-radius role — matching `BOUNDARY-CYCLICITY-PROOF.md` §4
(γ_A = atan2(R_f sinβ_e, a_e − R_f cosβ_e)). The two are the two angles at the two non-site vertices of
the same centre triangle (O_f, A_e, u), so γ_{f,e} + γ_{A,e} = π − β_e.

## 2. Q1 — do positive compatible triangles glue into a flat disk? Yes, under the stated hypotheses

2.1 Combinatorics of K+. K has V = q+m, faces = 16 (for q=10, m=4), and E = (3F + q)/2 = 29 edges, of
which q = 10 are boundary (consistent with the lead's `interior_edges: 19`). Adjoining 2q site-anchor
edges, q anchor-cycle edges and 10 virtual + 10 owner triangles gives V' = 24, F' = 36, E' = 29+20+10 = 59,
and V' − E' + F' = 1: a triangulated disk (χ = 1). Each edge A_e u is shared exactly by the virtual
triangle of boundary edge e and by the owner triangle at site u; the anchor-cycle edge A_prev A_next is
the boundary, shared only by the owner triangle at v. So the gluing graph is a disk, and (for strict
α_v ∈ (0,π)) every site is an interior vertex. Verified; no gap here.

2.2 Flatness at interior vertices — I re-derived both ledger computations exactly (the interface file's
line 9 and lines 11–16 are algebraically correct):
- Hidden site v, degree d in K: total angle in K+ = dπ − Σ_{e ∋ v}(π − β_e) = **Σ_{e ∋ v} β_e**.
- Boundary site v, degree d in K: real angles = (d−1)π − Σ_{interior e∋v}(π−β_e) − γ_{f,b1} − γ_{f,b2};
  adding the two virtual base angles π/2 − γ_{A,b1}, π/2 − γ_{A,b2} and the owner angle α_v, and using
  γ_{f,b}+γ_{A,b} = π − β_b, gives Σ_{incident edges} β_e + α_v = **2π** by the definition
  α_v = 2π − Σ_incident β_e.
So the boundary-site case is an identity *given the definition of α_v*, exactly as the file says; the
hidden-site case is the single ledger input **Σ_{e∋v} β_e = 2π** (§6-O1(a)).
2.3 Development exists. With oriented charts, edge-length compatibility (F1),(F2) and total angle 2π
at every interior vertex, the glued object is a genuine flat Riemannian disk (no cone points), the
underlying space is a disk hence simply connected, so the developing map f: K+ → R² exists, is
continuous on the closed disk, locally orientation-preserving and isometric, and is a *local
homeomorphism at every interior point including the vertices* (total angle 2π; this is the "local
nonfolding" the file invokes). The anchors are boundary corners with interior angle
π − (θ_u+θ_v)/2 ∈ (0,π) (§3). No step here needs a circumcenter to lie inside a triangle: in the
realization the sites are triangle *vertices*, and O_f is never a point of K+.

## 3. Q2 — injectivity from the convex unit-cyclic boundary: rigorous, with one orientation step

3.1 Boundary data. The boundary of K+ is the anchor cycle. Its edges have lengths L_v = 2 sin(θ_v/2)
(F3 + the file's θ_v definition) and its interior angle at A_e is the sum of the three incident triangle
angles δ_{u,A} + 2γ_{A,e} + δ_{v,A}. By the **assumed** closure identity (C1252, §6-O1(b)) this equals
π − (θ_u+θ_v)/2, hence the signed exterior turn at A_e is τ_e = (θ_u+θ_v)/2 ∈ (0,π) when the boundary is
traversed with the interior of K+ on the left (the orientation is fixed by the oriented charts and the
disk's orientation — this must be said, see §6-O3).
3.2 C1251 applies. `CYCLIC-POLYGON-CLOSURE.md` is exactly the needed statement: a closed oriented polygon
whose edges have lengths 2 sin(θ_i/2), whose *signed* exterior turns are (θ_i+θ_{i+1})/2 ∈ (0,π), and with
Σθ_i = 2π, has all vertices on one unit circle in the prescribed cyclic order, and the proof
(the model-chord induction E_i = z(e^{it_i} − e^{it_{i−1}}), then summing) also gives strict convexity and
winding number 1. All hypotheses are met by 3.1: lengths ✓ (by the θ definition), turns ✓ (assumed
closure), Σθ = 2π — which is *implied* by the closure identity via Gauss–Bonnet (Σ over anchors of
[interior angles] = (q−2)π is forced by the flat ledger; see §6-O1(c)), so imposing it separately is
harmless and conservative. Conclusion: the developed boundary curve is a simple convex polygon, winding
1 about each of its interior points and 0 about exterior points.
3.3 Degree argument. For p ∈ R² not on the image of the 1-skeleton, the map f is a map of pairs
(K+, ∂K+) → (R², R²∖{p}); deg(f,p) equals the winding number of the boundary curve about p:
1 for p inside the convex polygon, 0 outside. Every preimage of p lies in a triangle interior, and the
local degree there is +1 (orientation-preserving isometry). Hence #f^{-1}(p) = 1 inside and 0 outside.
Consequences: f is injective and surjective onto the closed polygon; there are no overlapping triangle
images.
3.4 "No unidentified distinct vertices" (the file's claim) follows from 3.3 plus local
homeomorphism, split by the type of the two vertices:
- *interior/interior.* If distinct interior vertices v ≠ w had f(v) = f(w) = q, then f maps small
  neighbourhoods V ∋ v, W ∋ w homeomorphically onto open sets containing q; their intersection is a
  nonempty open set, and subtracting the (measure-zero) image of the 1-skeleton leaves a nonempty open
  set of points p with a preimage in V and another in W, contradicting #f^{-1}(p) = 1.
- *interior/boundary.* If an interior vertex v and a boundary vertex A had f(v) = f(A) = q, then f(V)
  is an open neighbourhood of q. Since q lies on the developed boundary and the boundary is the
  boundary of the convex polygon, f(V) contains points strictly outside the polygon; those points have
  degree 0, i.e. no preimage, contradiction. (No assumption that the images of boundary sectors
  overlap is made; the open interior image escaping P is enough.)
- *boundary/boundary.* Impossible directly: the developed boundary is already an embedded simple
  convex polygon (C1251), traversed once, so its vertices are distinct; in particular all anchors have
  distinct images, and no boundary vertex coincides with another.
So all 24 vertices are distinct; no coincidence is hidden by the continuity extension.
3.5 What is *not* assumed anywhere: no circumcenter-inside-triangle, no global Delaunay/empty-circle test,
no nearest-site inequality. The only geometric inputs are triangle existence from angles (F1)–(F3) and
convexity of disks. (C1252's own proof does use nearest-halfplane and C1171 clipping facts about real
covers; in this direction its statement enters as an *equation among the abstract data*, not as a
geometric fact — see §6-O1(b).)

## 4. Q3 — complete coverage: yes, and here is the piece list

The developed image is the closed convex polygon P inscribed in the unit circle S¹, tiled by the
images of the F' triangles. Therefore D = P ⊔ (⊔_v cap_v), where cap_v is the region between the chord
A_prev A_next and the minor arc of S¹ between them (one cap per boundary site; the polygon is inscribed,
so these caps partition D∖P; θ_v < π makes each cap the minor segment). Coverage piece by piece:

4.1 Real face f (vertices = its three sites, circumradius R_f ≤ U): for x = Σλ_i v_i, λ_i ≥ 0, Σλ_i = 1,
put O_f at the origin, so |v_i| = R_f and x = Σλ_i v_i. Then
Σλ_i |x − v_i|² = Σλ_i (|x|² − 2x·v_i + |v_i|²) = |x|² − 2x·(Σλ_i v_i) + R_f² = R_f² − |x|²
(the barycentric combination x = Σλ_i v_i is what removes the cross term), i.e.
Σλ_i|x − v_i|² = R_f² − |x − O_f|² ≤ R_f², so some i has |x − v_i| ≤ R_f ≤ U. Sign-blind (variance
identity), valid for obtuse triangles: **no circumcenter-inside assumption**. ✓
4.2 Virtual triangle A_e u v: |A_e u| = |A_e v| = a_e ≤ U, base/2 = a_e sin γ_{A,e} < a_e (since
γ_{A,e} ∈ (0,π/2)). Splitting at the midpoint M, each half is covered: distance to a fixed point is
convex, so its maximum over a triangle is attained at a vertex, giving max ≤ max(|uv|/2, a_e) = a_e ≤ U
for the u-half and likewise for the v-half. ✓
4.3 Owner triangle v A_prev A_next: |vA_prev| = a_prev ≤ U, |vA_next| = a_next ≤ U and the disk is convex,
so the whole triangle ⊆ B(v,U). ✓
4.4 Cap_v: endpoints A_prev, A_next are at distance a_prev, a_next ≤ U from v, and cap_v = conv(minor arc),
so it suffices to prove the minor arc ⊆ B(v,U) (U ≤ 1; the file states the stronger U < 1). Proof: if the
arc contained the point w* of S¹ farthest from v (direction opposite to v, v ≠ 0), write the endpoints at
angular arguments φ_v + π − a and φ_v + π + b with a,b > 0, a+b = θ_v < π. Then
|A_prev − v|² = 1 + |v|² + 2|v|cos a ≤ U² ≤ 1 forces cos a ≤ −|v|/2 < 0, so a > π/2; symmetrically b > π/2;
hence θ_v = a + b > π, contradiction. So the arc avoids w*, and since cos (as a function of the argument
along an arc of length < 2π) has its only interior minimum at w*, the distance |w − v| is maximized at an
endpoint of the arc, hence ≤ U on the whole arc. Equivalently: when U ≤ 1, B(v,U) ∩ S¹ is a single arc of
angular width < π containing both anchors, hence containing the minor arc between them. Convexity then
gives cap_v ⊆ B(v,U). ✓
4.5 Completeness and centers. All four piece types use disks centered at *sites* only (never at anchors),
with the single radius U ≥ max(R_f, a_e), so the construction yields a cover of D by the q+m =
10 + 4 = 14 site-disks of radius U — the object the n14 problem asks about. Two side conditions are
implicit and should be stated: U ≤ 1 is the true requirement of 4.4 (U < 1 stated), and the sites lie
strictly inside S¹ — automatic here, since sites are interior vertices of the convex polygon inscribed in
S¹, but the cap argument reads as if it needed it.

## 5. Optional file: FLAT-DISK-STRAIGHT-OWNER-EXTENSION.md (α_v = π)

Checked because the core passed. The ear-removal argument is sound: (i) owner triangles at distinct
sites have disjoint interiors and meet at most in one anchor; (ii) removing an α=π ear makes v a boundary
vertex with total angle 2π − π = π, so the developed boundary passes straight through v; (iii) the removed
ear contributes angle 0 at each anchor (its angles are π at v and 0 at the anchors), so the anchors'
interior angles are unchanged and the closure identity is inherited; (iv) suppressing v merges the two
collinear boundary edges of lengths a_prev, a_next into one of length a_prev + a_next = L_v = 2 sin(θ_v/2),
so C1251 still applies and the same degree argument embeds the remaining disk into the same anchor
polygon; (v) coverage: retained owner triangles as before, the deleted ear covers no 2-dimensional region,
and cap_v is still covered by B(v,U) by §4.4 (its endpoints are the same anchors). Scope statement
(excludes α=0, collapsed real/virtual triangles, θ=0, zero radii) is honest. ✓

## 6. Findings — obligations, not counterexamples

**O1 (load-bearing hypotheses; must stay explicit).**
(a) Hidden-site ledger Σ_{e∋v} β_e = 2π. Geometrically this is mild (the rays from a site to its incident
face centres are in the star order and the consecutive gaps are exactly the β's), but as a statement about
abstract strict data it is an input, not a consequence of positivity/compatibility.
(b) **Per-anchor closure identity δ_{u,A} + 2γ_{A,e} + δ_{v,A} = π − (θ_u+θ_v)/2.** This is the single
minimal missing implication if any item is dropped: without it the boundary turn is not (θ_u+θ_v)/2, C1251
does not apply, the developed boundary can wind ≠ 1 and triangle overlap can occur, so the degree argument
collapses. Note it is *not* implied by the rest: Σθ = 2π + Gauss–Bonnet pins only the *sum* of the anchor
interior angles (giving Σθ = 2π as a consequence), not the identity at each anchor. The interface file
correctly lists it under "Need", but `FLAT-DISK-REALIZATION.md`'s summary "C1252 gives anchorangles"
should be read as "the strict branch assumes the C1252 identity". Hygiene point: C1252's proof is a
*necessity* theorem for actual covers (it uses C1171 clipping |w| < sqrt(1−ρ²) and nearest-halfplane
ordering); deriving the identity from it while *constructing* the cover would be circular. The composite
files are consistent because the identity is listed as an input — that listing is what must never be
dropped.
(c) Σθ_v = 2π: redundant given (b) (flat ledger + Gauss–Bonnet), so listing it is conservative, and its
presence must not be read as supplying (b).
**O2 (positivity list).** 0 < γ_{f,e} with Σ_{e⊂∂f} γ_{f,e} = π per real face; γ_{A,e} ∈ (0,π/2);
0 < α_v (≤ π in the extension); 0 < L_v < 2; 0 < a_e, R_f ≤ U. Each is used exactly once (triangle
existence, virtual base angles, owner triangle, θ_v < π for the minor-segment cap, coverage radii).
**O3 (orientation/signed turn).** C1251 requires the *signed* exterior turn to equal
+(θ_i+θ_{i+1})/2 ∈ (0,π); its "Conversely" paragraph warns that from unsigned triangle angles one must
first establish the actual signed turn. In the sufficiency direction the sign is not an extra
hypothesis — it is *derived* from the oriented charts: K+ carries the orientation induced by its
triangles, the boundary is traversed with the interior on the left, and each anchor's interior angle
π − (θ_u+θ_v)/2 ∈ (0,π) then has positive signed turn (θ_u+θ_v)/2, with Σ over anchors of these turns
= 2π by the flat ledger/Gauss–Bonnet. Obligation: write that two-line bridge explicitly. Unsigned
magnitude data alone does not determine the sign, so the bridge must name the orientation convention;
with all signed turns positive and summing to 2π, no winding-2 branch is compatible with this data.
**O4 (cap lemma).** The one-clause "endpoint argument (U<1, intersecting arc length<π)" is correct but
needs the §4.4 proof (or the equivalent single-arc statement) to be checkable; with U ≤ 1 the argument
still works, and sites-inside-D should be stated.
**O5 (scope).** The realization file's sentence "Chords and pockets inside K do not affect this
construction" is right; note only that they also cannot be used to derive (b).

## 7. Explicit consistency calibration (exact algebra, one example)

q = 3, m = 0 (K = a single triangle), all three β_e = β ∈ (π/2, 2π/3), all a_e = a, R_f = R. Then
α_v = 2π − 2β ∈ (0,π), δ = (π−α_v)/2 = β − π/2, L_v = 2a sin β, θ_v = 2 asin(L_v/2). Impose the closure
identity at each anchor: 2δ + 2γ_A = π − (θ+θ)/2. With Σθ = 2π forced (equivalently by Gauss–Bonnet),
θ = 2π/3 and hence γ_A = 2π/3 − β ∈ (0, π/6), γ_{f,e} = π − β − γ_A = π/3, and
a = (√3/2)/sin β ∈ (√3/2, 1), L_v = √3, R = a sin(2π/3−β)/sin(π/3). Checks, all exact:
site ledger γ_f + 2(π/2 − γ_A) + α_v = 2π; closure 2γ_A + 2δ = π/3 = π − (θ+θ)/2; γ_A ∈ (0,π/2);
α_v ∈ (0,π); U = a < 1; the realized anchor triangle is the equilateral triangle inscribed in S¹ with
arcs 2π/3 (so D = P ⊔ 3 caps, sites at radius R inside, each cap covered by its owner site). Limit
β → π/2⁺: α_v → π, δ → 0, γ_A → π/6, R → 1/2, a → √3/2 — i.e. the straight-owner extension applied to
this family lands exactly on the classical optimal 3-disk cover (sites at the edge midpoints of the
inscribed equilateral triangle, radius √3/2), which cross-checks the extension file's picture. This is
exact algebra, used only as a hypothesis-list calibration (non-emptiness, mutual consistency, and the
α=π boundary case); it is not evidence for the general theorem, which rests on §2–§4.

## 8. What this audit does and does not establish

- Establishes (conditional): strict data satisfying §6-O1/O2 ⟹ the 36 triangles glue into a flat disk,
  develop injectively onto a convex unit-cyclic polygon, and the resulting 14 site-disks of radius U cover
  D — with no circumcenter-inside-triangle and no nearest-site/empty-circle input.
- Does not establish: the reverse direction (actual cover ⟹ the strict constraints; Voronoi extraction),
  which is where nearest-site facts belong; any degenerate case (α=0, collapsed real or virtual triangles,
  θ=0, zero radii, β ∈ {0,π}); any global lower bound, and nothing about the candidate's optimality.
- Not done on purpose (per task): no claim registration, no `claim_review`, no numeric runs; the lead
  inspects first.

## 9. Next minimal obligation (one)

Make §6-O1(b) explicit and self-contained in the sufficiency direction: state the per-anchor closure
identity as an assumed strict-branch equation (with the note that C1252 proves it only in the necessity
direction), together with O1(a), O2, O3. With that, C1254/C1257 is a complete conditional sufficiency
theorem; without it, the realization's boundary step has no input.
