# q11 anchor/chord domain — necessary linear deficit constraints from the pocket/chord structure

Auditor: dirichlet-cut-audit-cc2. Task: derive *necessary* linear angular inequalities for the q11
anchor-deficit domain from the actual owner/chord geometry, express them as subset-sum constraints in
`d = L − θ`, and evaluate their effect on the 110-vertex q11 outer domain. Analytic only: no numeric jobs,
no claims. Sources read: `lead/Q11-DOUBLE-CHORD-EXCLUSION.md`, `lead/Q11-DOUBLE-EAR-EXCLUSION.md`,
`lead/OWNER-COUNT-UNIFICATION.md` (C1171), `lead/Q11-POCKET-FACTORIZATION.md`,
`lead/EMPTY-CIRCLE-STRENGTHENING.md`, `lead/ANCHOR-SIMPLEX-DOMAIN.md`, `lead/ANGULAR-DOMAIN-REPORT`-method
(`members/dirichlet-cut-audit-cc2/ANGULAR-DOMAIN-REPORT.md`).

## 0. Result (the formula the lead asked for, 0-based)

Fix the threshold U (the project's value), r ≤ U. Label the q = 11 owners 0,1,…,10 in the cyclic order of
their owned boundary arcs J_0,…,J_10, so J_j and J_{j+1 mod 11} are adjacent; write
  θ_j := |J_j| ∈ [0, L],  L := 2 asin U,  Σ_{j=0}^{10} θ_j = 2π,  d_j := L − θ_j ∈ [0, L],
  Δ_11 := Σ_j d_j = 11L − 2π,  Δ_10 := 10L − 2π = Δ_11 − L.
**For every ring chord joining owners i−1 and i+1 (indices mod 11; i is the "middle label"),**
  **(CC1)**   θ_{i−1} + θ_i + θ_{i+1} ≤ 2 asin(2U) =: B,
equivalently, in deficits,
  **(CC1')**  d_{i−1} + d_i + d_{i+1} ≥ G := 3L − 2 asin(2U) = 6 asin U − 2 asin(2U) > 0.
At the project's U these constants are (display only, midpoints of the certified rational enclosures
produced by `q11_polytope_independent.py`; the exact rationals are in `q11-polytope-independent.json`
and in the lead's kernel — do not rely on digits printed anywhere else): U = 0.33173203427623414,
asin U ≈ 0.3381389841, L ≈ 0.6762779683, asin(2U) ≈ 0.7254391317, B ≈ 1.4508782634, G ≈ 0.5779556414,
Δ_11 ≈ 1.1558723440, Δ_10 = Δ_11 − L ≈ 0.4795943757; so G < L, Δ_10 < G, and 2L < B.
**Vertex effect on the q11 outer domain** D_11 = {0 ≤ d_j ≤ L, Σd_j = Δ_11} (whose vertices are the 110
configurations with one coordinate L, one coordinate Δ_10, nine 0): since Δ_10 < G < L, a vertex satisfies
(CC1') iff its L-coordinate lies in the triple {i−1, i, i+1}. Hence
  - one chord: 30 of the 110 vertices survive (the L-entry is one of the triple's three labels, the Δ_10
    entry is any of the other ten), **80 are cut**;
  - two chords (middles i and i+2, the only two-chord shape by C1177; triples share the label i+1):
    only the 10 vertices with the L-entry at the shared label survive, **100 are cut**;
  - no chord (85 classes): no such constraint; the domain stays 110 vertices.
**Full vertex counts of the reduced polytopes** (not just the surviving old vertices — the cuts also
create vertices on the cut hyperplanes), computed independently in §11 by two exact algorithms:
D_11 has 110 vertices and 550 edges; the one-chord polytope has **54 vertices and 270 edges**; the
two-chord polytope has **24 vertices and 132 edges**. At one chord the 54 = 30 kept + 24 edge crossings;
at two chords the second cut leaves 18 of the 54 and adds 6 crossings ⟹ 24.
All-ring faces give **no additional** constraint: every all-ring face is a consecutive triple
{i−1, i, i+1} and its inequality is exactly (CC1) (proof in §5). First-neighbour owner pairs give only
θ_i + θ_{i+1} ≤ 2 asin(2U), which is **vacuous** because 2L < B (§5). The two-chord combination yields
d_{i+1} ≥ 2π − 4 asin(2U) − 10 asin U > 0 at the shared label (same constant as the C1177 double-ear
margin), but this is a *derived consequence*, redundant once both (CC1') cuts are imposed (§6) — it is
not an extra constraint and not an extra trim of the polytope.

## 1. Setup and which interface is used

C1171 supplies, for any normalized cover at radius r ≤ U: distinct sites, positive-length owned arcs J_j
that partition S¹ cyclically with disjoint interiors, and — crucially for this derivation — for every face
f of the chosen dual disk a **common witness** p_f with |p_f − c_s| ≤ r for every site label s ∈ f
(the relaxed witness interface; no exact Voronoi vertex and no empty-circle equality is needed). Each
owned arc satisfies θ_j ≤ L (its owner's disk covers it; C1171 §1) and ring-ring dual edges occur only
between first or second neighbours (C1171 §4). Ring *chords* are exactly the second-neighbour ring edges
i−1, i+1; C1177 shows there are at most two, and if two their middle labels differ by 2.

## 2. The containment lemma and the triple inequality

**Lemma (K-container).** Let the owners a, b have a common face witness p (a ∈ f, b ∈ f, |p − c_s| ≤ r for
s ∈ f). Then J_a ∪ J_b ⊆ K := S¹ ∩ B(p, 2r), and K is a connected arc of angular length ≤ B = 2 asin(2r).
Proof: for x ∈ J_a, |x − c_a| ≤ r (the owner's own disk covers its arc) and |c_a − p| ≤ r, so
|x − p| ≤ 2r; likewise for b. The set S¹ ∩ B(p, 2r) is a single arc: for centre distance ρ it is
{|φ − φ_p| ≤ α} with cos α = (1 + ρ² − 4r²)/(2ρ) (and for ρ = 0 it is S¹ if 2r ≥ 1, else empty), and its
length is maximized at ρ = sqrt(1 − 4r²), giving 2 arccos(sqrt(1 − 4r²)) = 2 asin(2r) < π since 2r ≤ 2U < 1.
∎
**Cyclic-order step.** K is a connected arc containing J_a ∪ J_b with a ≠ b, so it contains all owned arcs
lying between J_a and J_b along one of the two cyclic directions (the arcs fill S¹ and K is an angular
interval; arcs partially inside only help). **Count step.** In an arc of angular length ≤ B there can be at
most **3** whole owned arcs: were 4 or more contained, their total measure would be ≤ B while the
remaining at most 7 arcs have measure ≤ L each, giving
  2π ≤ B + 7L = 2 asin(2r) + 14 asin r,
which is impossible because 2 asin(2ρ) + 14 asin ρ < 2π at ρ = U (equivalently asin(2ρ) + 7 asin ρ < π,
the "3.11" inequality of C1171 §4 / C1177 §7) and the left side increases in ρ.
**Conclusion.** For a chord i−1, i+1 the two directions between the endpoint arcs contain 3 arcs (the
short triple {i−1, i, i+1}) and 10 arcs (everything else) respectively. By the count step the long
direction cannot be the contained one, so J_{i−1} ∪ J_i ∪ J_{i+1} ⊆ K and, the three arcs having disjoint
interiors,
  θ_{i−1} + θ_i + θ_{i+1} ≤ |K| ≤ 2 asin(2r) ≤ 2 asin(2U) = B.
∎ (CC1)

Two checks of the derivation, since the lead asked for them explicitly:
- **The middle site is not required to meet p.** If the chord {i−1,i+1} borders a *populated* pocket, the
  incident face is {i−1, i+1, h} with h hidden; the witness p is that face's witness, so
  |p − c_{i−1}|, |p − c_{i+1}| ≤ r and the lemma applies verbatim. J_i enters only through the cyclic-order
  and counting steps, never through a distance to p. So (CC1) holds for empty *and* populated pockets.
- **K is a container of owned arcs, not an identification with a cell arc or a chord disk.** Nothing here
  claims that S¹ ∩ B(p, 2r) equals any owned arc, that J_i is maximal, or that the three arcs are the
  actual cell arcs; only the inclusion and the measure comparison are used.
- **No maximality assumption.** The remaining arcs are bounded by θ ≤ L, never by equality; the argument
  is therefore valid with zero arcs (θ_j = 0), which matters because every vertex of D_11 has one.

## 3. Deficit form and the two scalar conditions the vertex counts need

(CC1) with θ_j = L − d_j is (CC1'): d_{i−1} + d_i + d_{i+1} ≥ 3L − B =: G. Non-vacuity needs G > 0, i.e.
  (I1)  2 asin(2U) < 6 asin U  ⟺  asin(2U) < 3 asin U.
(I1) has an exact elementary criterion: since 3 asin U < π/2 for U < 1/2, applying the increasing sine
and the triple-angle identity gives
  asin(2U) < 3 asin U  ⟺  sin(asin(2U)) = 2U < sin(3 asin U) = 3U − 4U³  ⟺  U² < 1/4  ⟺  U < 1/2.
So (I1) needs no interval work at all: it holds for every threshold below 1/2 (project U ≈ 0.3317), and
fails only above. (Display magnitudes: asin(2U) ≈ 0.7254 < 3 asin U ≈ 1.0144 — display only.)
The vertex counts of §0 use
  (I2)  Δ_10 < G  ⟺  10L − 2π < 3L − 2 asin(2U)  ⟺  7L + B < 2π  ⟺  asin(2U) + 7 asin U < π,
which is *exactly* the scalar inequality C1171 §4 / C1177 §7 already use (their certified "≤ 3.11 < π"),
so no new constant is introduced; and it is now certified a second time, independently, by
`q11_polytope_independent.py` from its own asin/π enclosures (§11). Also
useful, and automatic: G < L ⟺ 2 asin(2U) > 2L ⟺ 2U > sin(2 asin U) = 2U sqrt(1 − U²) ⟺ sqrt(1 − U²) < 1.
The triviality of pair constraints needs 2L < B (⟺ asin(2U) > 2 asin U).

## 4. Cutting the q11 outer domain vertices

D_11 = {0 ≤ d_j ≤ L, Σ_j d_j = Δ_11} is the clipped simplex with 110 vertices: exactly one coordinate
equals L, exactly one equals Δ_11 − L = Δ_10 ∈ (0, L), the other nine are 0 (vertex criterion; k = 1 since
Δ_11 = 11L − 2π ∈ (L, 2L) — the domain fact recorded in
`members/dirichlet-cut-audit-cc2/ANGULAR-DOMAIN-REPORT.md` §2). Add the half-space of (CC1') for a chord
with middle i. At a vertex, the triple sum d_{i−1} + d_i + d_{i+1} is one of 0, L, Δ_10, L + Δ_10. Since
G < L and Δ_10 < G (§3), the constraint holds **iff** the L-coordinate lies in {i−1, i, i+1}:
  - L-entry in the triple: sum ≥ L > G ✓ (30 vertices: 3 choices for the L label × 10 remaining choices
    for the Δ_10 label);
  - Δ_10-entry in the triple, L-entry outside: sum = Δ_10 < G ✗ (cut);
  - neither: sum = 0 < G ✗ (cut).
So **80 of the 110 vertices are cut by one chord constraint**. The 30 survivors are exactly the vertices
whose zero arc (the d = L entry) sits at one of the triple's three labels — the smallest nonzero deficit
Δ_10 may sit anywhere, inside or outside the triple (3 × 10 choices; 3 × 2 = 6 of them have Δ_10 inside,
the other 24 have both remaining triple entries maximal). Among the cut vertices are in particular the
"three consecutive maximal arcs" ones (L-entry and Δ_10-entry both outside the triple, triple sum 3L ≈ 2.029
> B ≈ 1.451), and additionally every vertex whose only nonzero triple entry is Δ_10 (sum Δ_10 < G).
(Vertex structure of D_11 used here: one coordinate L, one Δ_10 ∈ (0,L), nine 0 — which rests on the
certified 9L < 2π < 10L at the fixed U, see `ANGULAR-DOMAIN-REPORT.md` §2–§3.)
Two chords at middles i, i+2 have triples T_1 = {i−1, i, i+1}, T_2 = {i+1, i+2, i+3} meeting in the single
label i+1. A vertex satisfies both iff its L-entry lies in T_1 ∩ T_2 = {i+1}: if the L-entry is elsewhere
in T_1 then T_2's sum is at most Δ_10 < G, and symmetrically; so **10 vertices survive, 100 are cut**.
Consequently the q11 outer domain to use per catalogue class is
  D_11(K) = D_11 ∩ { d_{i−1} + d_i + d_{i+1} ≥ G : middle labels i of the chords of K },
which is still a superset of the deficit vectors of all covers of type K — the necessary condition is the
half-space, so it is safe for lower bounds. Exact vertex enumeration of D_11(K) is *not* done here
(no numeric work): its vertices are the surviving old vertices plus the finitely many intersections of the
cut hyperplanes with edges of the current polytope; any vertex-based flow bound (§8) must evaluate the
augmented set, not only the survivors.

## 5. All-ring faces and first-neighbour pairs: no additional constraint

**All-ring faces give exactly (CC1).** Ring-ring dual edges are only first- or second-neighbour (C1171 §4).
A triangular face all of whose vertices are ring labels has all three pairs adjacent, so all three cyclic
distances are ≤ 2; in C_11 the only such triples are consecutive triples {i−1, i, i+1} (for
{i−2, i, i+2} the pair i−2, i+2 has distance 4; for {i−1, i+1, j} one needs j adjacent to both i−1 and
i+1, i.e. j = i). Such a face contains the chord i−1, i+1, so its three-arc inequality is (CC1), and the
converse applies without the face (populated pockets). Hence the "all-ring face angle sum" family adds
nothing beyond the per-chord family; the per-chord form is strictly more applicable.
**First-neighbour pairs are vacuous.** For any dual edge between owners a, b, the same lemma gives
θ_a + θ_b ≤ 2 asin(2U) = B, but θ_a + θ_b ≤ 2L < B at U, so no information. (This is why the *triple*,
not the pair, is the correct unit: 3L > B while 2L < B.)

## 6. The two-chord combination: a *derived, redundant* bound on the shared deficit

For middles i, i+2 the two inequalities (CC1') sum to
  d_{i−1} + d_i + 2 d_{i+1} + d_{i+2} + d_{i+3} ≥ 2G,
and since Σ_j d_j = Δ_11 with all d ≥ 0 the weighted sum equals (Σ_{the five} d) + d_{i+1} ≤ Δ_11 + d_{i+1},
so d_{i+1} ≥ 2G − Δ_11 = 2π − 4 asin(2U) − 10 asin U > 0 (display ≈ 4.4e−5 at U).
This constant is exactly the C1177 double-ear margin (2π − 2B − 5L with 2B = 4 asin(2U), 5L = 10 asin U),
so its positivity is the same certified inequality; the exact rational lower bound already in
`q11-double-ear-pruning.json` may be reused. **Status (corrected):** this is not an independent
constraint. It is the sum of two already-imposed cuts plus Σd = Δ_11 and d ≥ 0, hence *redundant* once
both (CC1') half-spaces are in the system; it neither cuts vertices nor trims the polytope beyond what the
two cuts already do. It is worth recording only as the explanation of why two chords are possible at all
(a hedge, not a contradiction): two chords sharing a label give six arcs with only five deficits, and the
shared deficit is counted twice — precisely the "shared owned arcs would be double-counted" caveat in
`Q11-DOUBLE-EAR-EXCLUSION.md`.

## 7. What this does not claim

(CC1)/(CC1') are **necessary conditions only**: they exclude parts of the deficit polytope, not
configurations, and no cover or catalogue class is excluded here. No maximality of any owner arc is
assumed; zero arcs are allowed; the argument uses only the relaxed common-witness interface of C1171, so
it holds for the necessary relaxation as well as for actual covers, and it needs no symmetry assumption.
The numeric values quoted in §0 are display-only midpoints of certified enclosures; the certified forms
are the rational enclosures in `q11-polytope-independent.json` and the scalar inequalities of §3. Flow
bounds are not evaluated here (no dual arithmetic); the polytope vertex enumeration *is* done, in §11,
because the lead requested it, but it is a polytope fact, not a cover bound.

## 8. How the constraints enter the vertex-based flow bound

With F(d) = Σ_j g_j·A_j(d) the balanced-flow numerator of the dual (see
`members/dirichlet-cut-audit-cc2/ANGULAR-DOMAIN-REPORT.md` for the concavity and Taylor routes), the
constraints (CC1') are **linear in d**, so:
- the concavity route (F concave when all g_j·A_j ≥ 0) still gives min over the *reduced* polytope at a
  vertex of D_11(K) — the surviving 30 (or 10) old vertices plus the new cut-face vertices;
- the Taylor/vertex route is unchanged in form: the quadratic lower bound R(d) is concave in d globally,
  so min_{D_11(K)} R is attained at a vertex of D_11(K), again the augmented vertex set;
- the practical gain is the deletion of 80 (one chord) or 100 (two chords) of the 110 old vertices before
  any bound work; and the reduced polytopes themselves are now enumerated exactly (§11): 54 vertices /
  270 edges (one chord) and 24 vertices / 132 edges (two chords), with the full rational-coefficient
  vertex lists in `q11-polytope-independent.json`. Both vertex-based routes (concavity, Taylor) must
  evaluate that vertex set, not only the surviving old vertices.

## 9. Precision list

**P1.** Adopt the 0-based convention of §0 verbatim: owners labelled by their owned-arc cyclic order,
θ_j ∈ [0, L], L = 2 asin U, d_j = L − θ_j, Δ_11 = 11L − 2π; a chord joining owners i−1 and i+1 has middle
label i and gives θ_{i−1} + θ_i + θ_{i+1} ≤ 2 asin(2U), i.e. d_{i−1} + d_i + d_{i+1} ≥ 3L − 2 asin(2U).
**P2.** State that the constraint applies to populated pockets too (only the dual edge and its incident
face witness are used) and that it is monotone in r, so stating it at the threshold U is valid for all
r ≤ U.
**P3.** Keep the two scalar inequalities separate and note their different status: (I1) asin(2U) < 3asin U
(non-vacuity) is *elementary* — it is equivalent to U < 1/2 (proof: asin is increasing on the range and
2U < sin(3 asin U) = 3U − 4U³ ⟺ U < 1/2); (I2) asin(2U) + 7asin U < π (the vertex-count comparison
Δ_10 < G and the ≥4-arc counting step) is transcendental and is certified twice now: in the lead kernel and
independently in `q11_polytope_independent.py` from its own asin/π enclosures (chain "7L + B < 2π"). (I2)
is what makes the counts 30/10 rather than larger.
**P4.** Do not use all-ring faces as a separate family (§5); do not use first-neighbour pairs (§5); do not
present the two-chord bound as an extra constraint — it is redundant after both cuts (§6).
**P5.** When a vertex-based bound is run on D_11(K), include the cut-face vertices, not only the surviving
old ones (§8); the exact vertex sets are in `q11-polytope-independent.json` (§11).

## 10. Next minimal obligation (one)

Nothing analytic is left for this interface: (I1) is equivalent to U < 1/2, and (I2)
asin(2U) + 7asin U < π at the fixed U = 0.33173203427623414 is now certified both in the lead kernel and
independently here (§11, chain "7L + B < 2π", from own asin/π enclosures). The next step is downstream:
run the existing dual on the reduced q11 domains — vertex sets 54 (one chord) and 24 (two chords) from
`q11-polytope-independent.json`, 110 for the 85 no-chord classes — and keep the lead's index bridge (§11)
when translating to production gap coordinates.

## 11. Index bridge and independent enumeration (lead-requested)

**Index bridge (do not copy the formula unshifted).** This report labels owners by their owned arcs, so a
chord joining owners i−1 and i+1 has *owner* middle label i and the triple is {i−1, i, i+1}. In the
production convention (A_i = anchor of the edge between owners i and i+1, gap j belongs to owner j+1) the
same chord has middle *gap* index i and the constraint reads
  **d̃_{i−2} + d̃_{i−1} + d̃_i ≥ 3L − 2 asin(2U)**,  d̃_j := L − θ̃_j with θ̃_j the gap of owner j+1,
i.e. the triple is the *gap* triple {i−2, i−1, i}: one index lower throughout. My §0 formula is the
owner-indexed one and is the correct source; it must be shifted by −1 when written in gap coordinates.

**Independent verification.** `q11_polytope_independent.py` (own implementation, no lead imports) and its
output `q11-polytope-independent.json`:
 - constants recomputed here: own Machin-arctan π enclosures and own positive-term asin series with
   geometric tails give rational enclosures of L, B, 2π; all 11 chains used by the argument verify,
   including "7L + B < 2π" (I2) and "Delta < 2L" (the reason two simultaneously active L-caps are
   infeasible), with **no undecided sign**;
 - every polytope coefficient is an exact Q³ triple in (L, B, 2π); vertex coordinates are rational
   combinations of the three symbols;
 - **two independent algorithms agree exactly** on the vertex sets: (A) complete basis enumeration over
   independent 10-subsets of the three constraint families at each canonical case (616 / 2486 / 8151
   systems solved exactly), (B) recursive hyperplane cutting with rank-based adjacency, where each new
   vertex is obtained by solving the active system;
 - counts: **110 (no chord), 54 (middle [1]), 24 (middles [1,3])** vertices — agreeing with the lead's
   kernel; edges 550 / 270 / 132; cut breakdown 30 + 24 = 54, then 18 + 6 = 24;
 - coverage audit: every vertex feasible and of full active rank 11; active-constraint counts
   {10: 110}, {10: 54}, {10: 18 and 11: 6} (the two-chord polytope is *not* simple: the six vertices on
   both cut hyperplanes have degree 14); degree sums equal 2E; vertex-constraint incidence identity
   holds; and the D_11 edge set from the rank test is *identical* to the hand-derived combinatorial edge
   list V(k,j)~V(k,j′) / V(k,j)~V(j,k) (550 edges both ways) — an independent check of the adjacency
   machinery;
 - one trap recorded in the script: the crossing of a cut with an edge must be obtained by *solving* the
   rational active system. The crossing point is a rational combination of (L, B, 2π), but the
   interpolation scalar along the edge is a ratio of two module elements and is generically irrational,
   so edge-interpolation would silently produce wrong points.
