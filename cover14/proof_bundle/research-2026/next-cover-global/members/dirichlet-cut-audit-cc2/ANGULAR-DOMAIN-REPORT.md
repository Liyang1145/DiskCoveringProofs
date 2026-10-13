# Analytic audit — ANCHOR-SIMPLEX-DOMAIN.md (anchor arc domain + Taylor/vertex lower bound)

Auditor: dirichlet-cut-audit-cc2. Scope as given: geometry → domain, and the Taylor/quadratic-to-vertex
implication. No claims, no review events, no numeric jobs; arithmetic kernels (the q10/391 certificate and
fraction replay) not audited. Audited: `lead/ANCHOR-SIMPLEX-DOMAIN.md` (18 lines), with the already
audited `FIXED-ANCHOR-CONVEX-REDUCTION.md` dual (`members/dirichlet-cut-audit-cc2/CONVEX-REPORT.md`) for
the flow/norm bookkeeping. Also applied the requested one-line correction to `CONVEX-REPORT.md` §1.5
(see §9).

## 0. Verdict

**Both claimed implications hold: the arc-domain description is correct (with one hypothesis that must be
certified), and the "Taylor quadratic is concave on the entire domain, so its minimum sits at a vertex"
step is correct as written — it needs no concavity of the true numerator F.** One presentation item needs
pinning: the displayed anchor-angle formula t_j = jL − Σ_{i<j} d_i is consistent only with 0-based arc
indexing; with the natural 1..q indexing the wrap identity t_q = 2π fails by d_q (§4). Also corrected below:
the NSD sign condition on the Hessian is *sufficient, not necessary* (§5); the Taylor penalty Hessian is
−‖g_j‖∇t_j∇t_jᵀ, not −2‖g_j‖∇t_j∇t_jᵀ (§6); at U = sin(π/9) the q10 domain is still the full 9-simplex with
zero arcs only at its 10 vertices (§8); and the arc cap θ ≤ L is the *essential* side d ≥ 0, while the
redundant q10 side is d ≤ L (§7). The inequality 9L < 2π < 10L is already asserted exactly in the integer
and Fraction certificates at the fixed U = 0.33173203427623414, so it is an established input here, not an
open obligation; 0.3477467934 is a radius lower bound obtained for anchors restricted using that same U,
not a second threshold (§3). Everything else checked: full Hessian structure, vertex criterion and counts
(10 and 110 recovered, unified as q·C(q−1,k)), cap redundancy/activeness, endpoint and zero-arc cases.

## 1. The arc bound θ_i ≤ L = 2 asin U (derivation supplied; hypothesis is the normalized owner structure)

For a disk of radius U < 1 with centre at distance ρ from the origin, the intersection with the unit circle
S¹ is {|φ − φ_c| ≤ α} with cos α = (1 + ρ² − U²)/(2ρ), so its arc length is 2α. The function
(1 + ρ² − U²)/(2ρ) is minimized at ρ = sqrt(1 − U²) with minimum sqrt(1 − U²), so
  max arc length = 2 arccos(sqrt(1 − U²)) = 2 arcsin U = L  (centre at distance sqrt(1 − U²)),
and L < π since U < 1. For ρ = 0 the intersection is empty (all circle points are at distance 1 > U), so
the bound holds for every ρ ≥ 0. This proves the file's "a radius U disk intersects S¹ in an arc of length
at most L", including the extremal case. Monotonicity in r then gives the file's "remains true after
normalizing afresh at U": a cover at radius r ≤ U has θ_i ≤ 2 arcsin r ≤ L.
Why the arcs are owner arcs of disks that cover them: take the nearest-site (Voronoi) assignment of ∂D to
the sites. If w lies in the arc owned by v and is covered by some disk B(c_s, r), then
|w − c_v| ≤ |w − c_s| ≤ r, so the whole arc lies in B(c_v, r) ∩ S¹ and has length ≤ L. So the *domain*
part of the note needs only "r ≤ U" plus the nearest-site assignment; the catalogue/normalization input
(C1168/C1171/C1172) is needed only to know which combinatorial type and how many arcs — not for the arc
inequality itself. Good separation; worth stating in the file.

## 2. Domain at q = 10 and q = 11 — verified, with the unifying vertex criterion

Definitions: θ_0..θ_{q−1} ≥ 0 the owner arcs in cyclic order, Σθ_i = 2π; L = 2 asin U; d_i = L − θ_i;
Δ_q = Σd_i = qL − 2π. The constraint set is exactly
  D_q = {d ∈ R^q : d_i ≥ 0, d_i ≤ L, Σd_i = Δ_q}
(since θ_i ≥ 0 ⟺ d_i ≤ L and θ_i ≤ L ⟺ d_i ≥ 0), a (q−1)-dimensional polytope.
Vertex criterion (standard): a vertex of a box intersected with a hyperplane has at most one coordinate
strictly between its box bounds. Hence if Δ_q ∈ (kL, (k+1)L), every vertex has exactly k coordinates equal
to L, one equal to Δ_q − kL ∈ (0,L), and the rest 0; the count is C(q,k)(q−k) = q·C(q−1,k):
 - q = 10, Δ_10 ∈ (0,L) (k = 0): 10·C(9,0) = **10 vertices** — the full 9-simplex Δ_10·e_i. Verified.
 - q = 11, Δ_11 ∈ (L,2L) (k = 1): 11·C(10,1) = **110 vertices**, each with one coordinate L, one equal to
   Δ_11 − L = Δ_10, nine 0. Verified, and the file's "110 ordered vertex choices" is right.
The file's two domains are therefore both instances of one criterion; recording the formula makes the
counts checkable and shows what happens at other U (k = 1 at q10 beyond sin(π/9) would give 90 vertices).
q10 consequences, all verified: Δ_10 = 10L − 2π < L ⟺ 9L < 2π, so the side d_i ≤ L is *redundant*
(d_i ≤ Σd = Δ_10 < L) — that side is the nonnegativity θ_i ≥ 0, **not** the arc cap; the arc cap
θ_i ≤ L (equivalently d_i ≥ 0) is essential and is what bounds the simplex. Hence the domain is the full
9-simplex, every arc satisfies θ_i ≥ L − Δ_10 = 2π − 9L > 0, and **no zero arc occurs** — so the file's "NO
zero gap anchor degeneracies in q10" is correct, given the certified inequality at the fixed
U = 0.33173203427623414 (§3). q11: zero arcs are allowed and in fact occur at *every* vertex (the
coordinate set to L gives θ = 0), the other non-zero coordinate gives θ = 2L − Δ_11 = 2π − 9L ∈ (0,L), and
the remaining nine arcs equal L. The file's "zero gaps allowed here" is right, with the refinement that
they are vertex configurations, not merely face-interior ones.
Outer-domain direction: D_q is a superset of the arc vectors of all normalized covers, which is the
correct direction for a lower bound (a minimum over a larger set is still a valid lower bound). The file's
"candidate boxes may further restrict, nothing else needed" is right.

## 3. The inequality 9L < 2π < 10L — already certified at the fixed U; status clarified

9L < 2π ⟺ L < 2π/9 ⟺ sin(L/2) < sin(π/9) ⟺ U < sin(π/9) = 0.342020…, and
2π < 10L ⟺ U > sin(π/10) = 0.309017…, so both domain descriptions (Δ_10 ∈ (0,L); Δ_11 ∈ (L,2L)) rest on
sin(π/10) < U < sin(π/9). At the fixed threshold U = 0.33173203427623414 this is asserted exactly in both
the integer and the Fraction certificates, so it is an **established input** for everything below, not an
open obligation. Correction of an earlier reading in this report: 0.3477467934 is a *radius lower bound*
obtained for anchors restricted using that same fixed U (via 2 asin U), not a second threshold U; it does
not put the domain hypothesis in doubt. The hypothetical remark is kept only for orientation: if a
*different, larger* threshold U' ≥ sin(π/9) were ever used, then 9L' < 2π would fail, q10's domain would
become a clipped polytope with k = 1 (90 vertices) and zero arcs would no longer be excluded; and a bound
computed over the 10-vertex simplex {d ≥ 0, Σd = Δ_10} would remain *valid* there (a strict superset,
containing points with negative arcs) while no longer being the domain. By-product sanity check from the
same two inequalities: any cover needs qL ≥ 2π, i.e. U ≥ sin(π/q) (0.30902 at q = 10), consistent with
known values.

## 4. Indexing and gauge — one off-by-one to pin

With θ_0..θ_{q−1} the arcs in cyclic order from the gauge anchor and t_j the anchor angles, the identity
t_{j+1} − t_j = L − d_j = θ_j gives t_j = jL − Σ_{i<j} d_i for j = 0..q, hence
t_0 = 0 (gauge A_0 = (1,0)) and t_q = qL − Σ_{i=0}^{q−1} d_i = qL − Δ_q = 2π, i.e. A_q = A_0 as required.
This is exactly the file's formula — but only with the arcs indexed 0..q−1 (equivalently, with the sum
running over the first j arcs of the order that starts at the gauge anchor). With the natural 1..q
indexing the same display gives t_q = qL − (Δ_q − d_q) = 2π + d_q ≠ 2π, so the index convention must be
written down rather than left to "consistently". Two related checks: the map d ↦ t is affine with
∂t_j/∂d_i = −1 for i < j and 0 otherwise (lower-triangular, invertible), so vertices map to vertices and
the "apply directly in anchor-angle coordinates" remark is valid; and the gauge A_0 = (1,0) fixes the
rotation, so the domain parameterizes anchor configurations modulo the global rotation, which is the same
gauge the flow's numerator L_z(A) = F(d) must be built in (per CONVEX-REPORT §5.4). Rotating a cover into
this gauge is harmless because the covering problem is rotation invariant.

## 5. Full Hessian of the numerator (checked; no block/mixed-direction gap)

With A_j(d) = (cos t_j, sin t_j), g_j fixed and φ_j(d) = g_j·A_j(d) = g_j·(cos t_j, sin t_j):
  ∂φ_j/∂d = φ_j'(t_j) ∇t_j,   ∇²φ_j = φ_j''(t_j) ∇t_j ∇t_jᵀ = −φ_j(d) ∇t_j ∇t_jᵀ,
because ∂²/∂t² [g·(cos t, sin t)] = −g·(cos t, sin t) = −φ_j and t_j is affine in d. So
  ∇²F(d) = −Σ_j φ_j(d) ∇t_j ∇t_jᵀ.
The condition "φ_j(d) ≥ 0 for every j" makes every rank-one term NSD, hence makes the whole Hessian NSD —
so it is a **sufficient** condition, and the file's use of it ("if each term remains nonnegative throughout
Q … thus F is concave on Q") is the correct use. It is **not necessary**, and the report should not say
"iff": (i) the j = 0 term is identically zero because t_0 ≡ 0, so ∇t_0 = 0 and its rank-one term vanishes
regardless of the sign of φ_0 (the rank-one gradients are zero exactly for j = 0 and nonzero for j ≥ 1);
(ii) more generally the Hessian is a sum of rank-one matrices and such a sum can be NSD through
cancellation even when some coefficients are negative. What is *not* affected: whenever the sufficient
condition holds, the sum is NSD as a whole, so the conclusion controls all directions including mixed ones
and there is no per-block trade-off — the file's parenthetical about "separate positive blocks are not
being combined" is correct. Each ∇t_j for j ≥ 1 is a nonzero {0,−1} vector, so those terms are genuinely
rank one and the Hessian is in general a full matrix. Consequences verified: F is concave on any convex
d-polytope Q on which the sufficient condition holds, so F(d) ≥ min over the vertices of Q (a concave
function attains its minimum at an extreme point), and dividing by the certified upper bound on Σ‖z_e‖
gives a lower bound valid for all anchors in Q using vertex evaluations only. If the sign condition fails,
the Taylor route of §6 applies instead (it does not need it). The sign condition itself must be certified
where used — an interval dot bound is enough: for each j the range of t_j over Q is an interval (t_j is
affine and d ranges over a box/simplex), so an interval bound on g_j·A_j follows.

## 6. The Taylor/vertex implication (checked in detail; correct as stated)

Per term, globally in t: φ_j''(t) = −φ_j(t) and |φ_j(t)| = |g_j·A_j(t)| ≤ ‖g_j‖, so
  φ_j''(t) ≥ −‖g_j‖   for all real t   (no sign or concavity hypothesis needed).
Taylor with the oriented integral remainder gives, for any t,
  φ_j(t) = φ_j(t_0) + φ_j'(t_0)(t − t_0) + ∫_{t_0}^{t} (t − s) φ_j''(s) ds,
and (t − s) ds ≥ 0 along the oriented path in both cases t > t_0 and t < t_0, while
∫_{t_0}^{t}(t − s) ds = (t_0 − t)²/2. Hence
  φ_j(t_j(d)) ≥ φ_j(t_j(d_0)) + φ_j'(t_j(d_0))(t_j(d) − t_j(d_0)) − ½‖g_j‖(t_j(d) − t_j(d_0))².
Summing over j and using ∇_d t_j constant:
  F(d) ≥ F(d_0) + ∇F(d_0)·(d − d_0) − ½ Σ_j ‖g_j‖ (t_j(d) − t_j(d_0))² =: R(d).
R is concave on the *entire* d-space: each penalty term is a negative multiple (weight ‖g_j‖ ≥ 0) of the
square of an affine function of d, whose Hessian is −‖g_j‖∇t_j∇t_jᵀ (the ½ prefactor cancels the factor 2
from differentiating the square — corrected from an earlier −2‖g_j‖∇t_j∇t_jᵀ in this report), i.e. NSD;
adding the affine terms preserves concavity. Therefore min_{d ∈ Q} R(d) = min_{v ∈ vertices Q} R(v), and
since F ≥ R pointwise,
  F(d) ≥ min_{v ∈ vertices Q} R(v)   for every d ∈ Q,
with no concavity assumption on F. This is exactly the file's claim, and the two structural points that
make it work are worth keeping explicit: the weight ‖g_j‖ is nonnegative (so the penalty is concave, not
convex), and the penalty is a function of the affine image t_j, so vertices suffice. What a certificate
must supply: a lower bound on F(d_0), interval enclosures of ∇F(d_0) (equivalently of φ_j'(t_j(d_0)) and
the exact integer ∇t_j), upper bounds on ‖g_j‖, and exact/interval t_j(v) at the finitely many vertices
(exact rationals in L and Δ_q = qL − 2π, with L = 2 asin U transcendental — interval arithmetic in U
suffices). The file's "exact/interval tangent coefficients and norm upper bounds are mandatory" is right.
Optional sharpening (not needed, not claimed): keep the penalty only on the j's with large deviation.
Applicability in t-coordinates is fine because d ↦ t is an affine bijection (§4), so the vertex set
transfers.

## 7. Cap necessity (both readings) — resolved

(a) Inside the domain, the arc cap θ_i ≤ L is precisely the box constraint d_i ≥ 0 — the **essential**
side: it is what cuts the hyperplane Σd = Δ_q down to the simplex, and it is the geometric content of §1
(a radius-U disk meets S¹ in an arc of length at most L). The *other* box side d_i ≤ L (equivalently
θ_i ≥ 0, arcs nonnegative) is the one that is redundant at q10, because Δ_10 < L forces d_i ≤ Σd = Δ_10 < L;
at q11 (Δ_11 > L) that side is active and produces the clipped simplex with its 110 vertices — the file's
asymmetry is correct. (Corrected: this report earlier attached "redundant at q10" to the wrong side.)
(b) The exterior circular caps of D (the regions outside the anchor polygon) never enter this domain: they
belong to the coverage argument (owner disks + the single-arc lemma), already audited in
`DEGREE-COVER-REPORT.md` §4 and §7. The domain note neither needs nor claims anything about them; its
"cap" is only the arc-length cap. Both readings are consistent, and the note should say which "cap" it
means to avoid a reader importing the coverage-side requirement into the anchor domain.

## 8. Endpoint and zero-arc cases (checked)

- Zero arcs at q10: excluded at the certified threshold (θ_i ≥ 2π − 9L > 0). At the endpoint 9L = 2π
  (Δ_10 = L) the domain is still the **full 9-simplex** {d ≥ 0, Σd = L} — the box side d ≤ L remains
  redundant since Σd = L forces d_i ≤ L — with the same 10 vertices d = L·e_i; the zero arcs occur exactly
  at those 10 vertices (one zero arc, nine arcs of length L, 9L = 2π), not throughout the domain, and the
  domain does *not* collapse to 10 points. (Corrected.) So the strict inequality at the fixed threshold is
  exactly what excludes zero arcs everywhere else.
- Zero arcs at q11: present at every vertex (the coordinate equal to L gives θ = 0) and on faces; allowed
  by the domain, and compatible with the weak-order/collapse interface of `DEGREE-COVER-REPORT.md` §7
  (zero increments; contracting zero runs gives the convex anchor polygon with one winding).
- Maximal arcs θ_i = L: attained, with the extremal geometry centre at distance sqrt(1 − U²) (§1); the cap
  coverage of such an arc holds with equality in the closed disks, and since L < π the single-arc lemma's
  hypothesis (arc < π) holds with room to spare.
- U endpoint at sin(π/10): 10L = 2π, Δ_10 = 0, the domain is the single point d = 0 (all arcs equal L);
  for U below that the domain is empty, i.e. no q10 cover exists — a by-product necessary bound
  U ≥ sin(π/q) (§3).
- Degenerate dimension: q < 3 or Δ_q outside [0, (q−1)L] makes D_q empty; not claimed by the note and not
  needed here.

## 9. Requested correction applied to CONVEX-REPORT.md

§1.5 and P6 now read: the inherited "38" is **28 β variables + 11 anchor log-radii − 1 global scale = 38**
(earlier q11 bookkeeping), explicitly *not* 28 centre coordinates, and not mixed with the q10 instance
(whose anchor family contributes q − 1 = 9 arc parameters). No other change to that report.

## 10. Precision list

**P1.** Record that 9L < 2π < 10L ⟺ sin(π/10) < U < sin(π/9) is already asserted exactly (integer and
Fraction certificates) at the fixed threshold U = 0.33173203427623414, so the domain descriptions rest on a
closed input, and keep the distinction that 0.3477467934 is a radius lower bound under anchors restricted
by that same U, not a second threshold (§3). Consequences to state: q10 full simplex with no zero arcs
except at the 10 vertices when Δ_10 = L; a hypothetical larger threshold would give a clipped polytope
(90 vertices at q10) and the 10-vertex simplex would then be only a valid superset for bounds.
**P2.** Pin the index convention: arcs indexed 0..q−1, t_j = jL − Σ_{i<j}d_i (0-based), so t_{j+1} − t_j =
θ_j and t_q = 2π; otherwise an off-by-one d_q appears (§4).
**P3.** State the vertex criterion once with its count q·C(q−1,k), and derive 10 and 110 from it (§2).
**P4.** State why the *domain* part needs no C1172 (nearest-site assignment + r ≤ U suffice, §1), while the
catalogue count of arcs does.
**P5.** Say which "cap" is meant (§7a) so that the coverage-side cap condition is not imported; and keep
the two sides straight — θ ≤ L ⟺ d ≥ 0 is the essential arc cap, d ≤ L ⟺ θ ≥ 0 is the side that is
redundant at q10 and active at q11.
**P6.** Keep the concavity-route hypothesis (a *sufficient* condition, not an "iff") and the Taylor route
separated as the file already does; note that the Taylor penalty's Hessian is −‖g_j‖∇t_j∇t_jᵀ, and that the
weights are norms, hence nonnegative, which is what keeps the penalty concave (§6).

## 11. Scope

Establishes: an exact finite-dimensional outer domain for the anchor arcs at the fixed threshold
U = 0.33173203427623414 (a 9-simplex at q10, a clipped 10-simplex at q11, under the already certified
inequality), plus two rigorous reductions of the balanced-flow numerator to finitely many vertex
evaluations — one conditional on the pointwise sign condition (concavity route, sufficient condition only),
one unconditional given interval coefficients (Taylor route), neither assuming concavity of F. Does not
establish: any exclusion of a configuration by itself; any global bound; the arithmetic of the cited
q10/391 certificate or its fraction replay (not audited, and per the lead not a premise for the analytic
proof). Status as reported by the lead (not verified here): 83 whole-domain q10 exclusions replayed
independently, pending union. Nothing about degenerate/repeated anchors beyond the domain-level
description. Weakness of a fixed flow's vertex bound is acknowledged in the file and is real (the Taylor
penalty can be large), with the remedies being flow adaptation/subdivision, not more domain analysis.

## 12. Next minimal obligation (one)

Only P2 remains: pin the 0-based arc index convention with the wrap check t_q = 2π in the note. The
domain inequality P1 is already certified at the fixed threshold, so it is a citation, not an obligation.
