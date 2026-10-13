# Analytic audit — DIRICHLET-RADIUS-EXISTENCE.md and LOG-RADIUS-LAPLACIAN.md

Auditor: dirichlet-cut-audit-cc2 (route `commandcode2`). Task: analytic audit only. No new scripts,
no claim-tool entries, no edits outside this directory.

Files audited (read in full):
- `research-2026/next-cover-global/lead/DIRICHLET-RADIUS-EXISTENCE.md` (37 lines)
- `research-2026/next-cover-global/lead/LOG-RADIUS-LAPLACIAN.md` (11 lines)

Context read first: `STATUS.md`, `DEAD.md`, `CURRENT.md`. Related interface read for the modelling
identification only: `lead/FLAT-DISK-ANGLE-INTERFACE.md`. Lead's own control artefacts read (not
re-run): `lead/dirichlet_cut_control.py`, `lead/dirichlet-cut-control.json`,
`lead/dirichlet_radius_solver.py`, `lead/dirichlet-radius-solver-control.json`. `STATUS.md` line 152
registers the object as C1261 and already labels the cut enumeration "positive numerically" and the
caps/closure as unproved — consistent with what I find.

## 0. Verdict

**Necessity verified, sufficiency verified, uniqueness verified, atan2 convention correct as written,
symmetric derivative correct, coercivity signed layer identity correct term by term. 0
counterexamples found. 0 missing implications inside the theorem.** Three presentational/proof-budget
gaps and two sharpenings are listed in §9; none changes the truth of the statement. The theorem is
about the abstract fixed-angle log-radius system; the step from a covering to that system is **not**
inside these two files (it is the interface in `FLAT-DISK-ANGLE-INTERFACE.md`), and nothing about
radius caps, embedding/cyclicity or any n14/n12 optimum follows (§10).

Everything below is derived from the defining formula, not from samples. The numeric figures quoted
are the lead's own control outputs, used only as calibration (§8) — never as proof. No Thales-type
statement about arbitrary circle triples is used anywhere; where geometry enters I use only the law of
sines/cosines in the centre triangle whose two sides and included angle *are* the data.

## 1. Conventions and the exact quantity the two files solve

Data: face set F, edges internal (two distinct faces) or anchor (face + fixed anchor with radius
a_e = e^{L_e} > 0). β_e ∈ (0,π), c_e = π − β_e ∈ (0,π). Unknowns l = (l_f) ∈ R^F, R_f = e^{l_f}.

h_fg := atan2( e^{l_g} sin β_e , e^{l_f} − e^{l_g} cos β_e ).  (D1)

With R = e^{l_f}, T = e^{l_g}, D² := R² + T² − 2RT cos β_e > 0 (strict, since β_e ∈ (0,π)), and
Δ := l_f − l_g,

h_fg = atan2( T sin β_e , R − T cos β_e ) = atan2( sin β_e , e^{Δ} − cos β_e ).  (D2)

In the centre triangle with sides R, T and included angle β_e at the shared site, (D2) is exactly the
angle at the R-endpoint: cos γ = (R − T cos β_e)/D and sin γ = T sin β_e/D by the law of cosines/sines,
so γ = atan2(T sin β_e, R − T cos β_e). Hence

h_fg ∈ (0, π),  h_fg + h_gf = π − β_e = c_e,  h_fg ∈ (0, c_e),  (S1)

and the range is *open*: no finite positive (R, T) attains h_fg = 0 or h_fg = c_e. System solved:

G_f(l) := π − Σ_{e ∋ f} h_f^{(e)} = 0 for every f ∈ F.  (D3)

### atan2 audit (checked, load-bearing)
1. Branch cut: the point (x, y) = (e^{l_f} − e^{l_g} cos β_e, e^{l_g} sin β_e) has y > 0 for every
   β_e ∈ (0,π) and every finite (l_f, l_g). The atan2 argument therefore never leaves the open upper
   half-plane: h is real-analytic in (l_f, l_g, β_e) on R² × (0,π), with no jump and no atan2(0,0)
   anywhere. The only degeneracies of the formula are β_e → 0, π (branch point) and a_e or R_f → 0, ∞
   — exactly the endpoints the file excludes in its last section.
2. The second atan2 argument can be negative (e.g. β_e < π/2 and e^{l_g} cos β_e > e^{l_f}), so
   h_fg > π/2 is legitimate and correctly produced. A plain arctan returns the wrong value there.
   This is the branch/argument-order failure mode that was found and fixed in the earlier
   root-cc2/innernorm-envelope audit; the current formula is on the correct side of it.
3. The convention is genuinely load-bearing, because it puts the *face's own* radius in the x-slot and
   the *other* radius in the y-slot. The swapped convention would give h_gf, and the face system
   would read Σ_e (c_e − h_f^{(e)}) = π, a different system (equivalent only after re-arranging into
   Σ_e c_e = 2π, i.e. generically not the same equations). Cross-checks of (D1): identical to
   `FLAT-DISK-ANGLE-INTERFACE.md` (γ_fe = atan2(T sin β, R_f − T cos β), Σ of 3 edges = π,
   γ_fe + γ_ge = π − β_e) and to the lead's kernel `dirichlet_radius_solver.py`, where
   t = exp(lg − lf), hf = arctan2(t·sin β, 1 − t·cos β) — multiplying both arguments of (D2) by
   R > 0 reproduces it. So both files, the interface file and the implementation use the same h.
   (S1) also proves the doc's structural pair "h_fg ∈ (0,c_e), h_fg + h_gf = c_e".

## 2. Symmetric derivative — verified exactly

Put u = T sin β_e, v = R − T cos β_e, u² + v² = D². Then ∂/∂R atan2(u,v) = (v·0 − u·1)/D² = −u/D²,
so with ∂R/∂l_f = R and ∂T/∂l_g = T:

∂h_fg/∂l_f = − R T sin β_e / D² ,  ∂h_fg/∂l_g = + R T sin β_e / D² .  (S2)

Since D² = R T (R/T + T/R − 2 cos β_e) = 2 R T (cosh Δ − cos β_e),

R T sin β_e / D² = sin β_e / [ 2 (cosh Δ − cos β_e) ] =: w_e > 0  (S3)

(cosh Δ ≥ 1 > cos β_e, sin β_e > 0). So ∂h_fg/∂l_f = −w_e, ∂h_fg/∂l_g = +w_e: the doc's line
`dh/dl_g = -dh/dl_f = w_e` is exact, with the stated w_e. Calibration: β_e = π/2, l_f = l_g gives
h = π/4 and w_e = 1/2; h_fg = atan(T/R) there, and R∂_R = −1/2, T∂_T = +1/2 — matches.

Exchange identity (needed for the potential and for Jacobian symmetry): (D2) for h_gf is
atan2(sin β_e, e^{−Δ} − cos β_e), the same function with Δ → −Δ, and cosh is even, so
**∂h_fg/∂l_g = ∂h_gf/∂l_f = w_e**. Hence the Jacobian of D3 is symmetric:

(DG)_{ff} = Σ_{e ∋ f} w_e ,  (DG)_{fg} = −w_e  (internal e),  (DG)_{ff} ⊇ anchor terms + w_e.  (S4)

Dirichlet form: zᵀDG z = Σ_{internal e} w_e (z_f − z_g)² + Σ_{anchor e} w_e z_f². This is ≥ 0, and
= 0 forces z_f = z_g across every edge and z_f = 0 at every anchor-incident face, hence z ≡ 0 by
connectivity + existence of an anchor edge. So DG ≻ 0 for every l ∈ R^F. Both hypotheses are used:
without anchor edges z ≡ const is a null direction (DG·1 = 0) and the statement fails. The doc lists
both hypotheses in its Data paragraph; the one-liner "hence symmetric positive definite" in the
sufficiency section relies on them, and `LOG-RADIUS-LAPLACIAN.md` states them explicitly and
correctly, including the same quadratic form and the same w_e — the two files agree.

## 3. Explicit potential (existence, not just closedness)

Define φ_e(d) := −∫_0^d h_e(s) ds with h_e(s) = atan2(sin β_e, e^{s} − cos β_e) (i.e. (D2) with
Δ = s), and

E(l) := π Σ_f l_f + Σ_{internal e} [ −c_e l_g + φ_e(l_f − l_g) ]
                   + Σ_{anchor e} [ −c_e L_e + φ_e(l_f − L_e) ] .

For an internal edge with other end g: ∂/∂l_f = φ_e'(Δ) = −h_e(Δ) = −h_fg and
∂/∂l_g = −c_e − φ_e'(Δ) = −c_e + h_e(Δ) = −h_gf, using (S1). For an anchor edge: ∂/∂l_f = −h_f^{(e)}.
Therefore ∇E = G exactly, E ∈ C², Hessian(E) = DG ≻ 0, so E is strictly convex on the convex set
R^F. (Exhibiting E independently re-derives the exchange identity of §2, since Hessians are
symmetric.) This is the cleanest form of the doc's "one can choose an internal-edge energy"; the doc's
phrase "it is the gradient of a C2 strictly convex energy E" is verified, not assumed.

## 4. Bounded difference from the positively homogeneous P — verified in both directions

From h_e(s) = atan2(sin β_e, e^{s} − cos β_e):
- s → +∞: h_e(s) = sin β_e e^{−s} (1 + O(e^{−s})), so ∫_0^∞ h_e < ∞ and φ_e has a finite limit
  φ_e(+∞) with φ_e(s) − φ_e(+∞) = ∫_s^∞ h_e = O(e^{−s}).
- s → −∞: c_e − h_e(s) = O(e^{s}) (the triangle degenerates; the distance of
  (x,y) = (e^s − cos β_e, sin β_e) from the ray at angle c_e is O(e^s)), so
  φ_e(s) + c_e s = ∫_s^0 [h_e − c_e] dt + const → finite limit, remainder O(e^s).

Consequently, with d = l_f − l_g: for d ≥ 0, Φ_e + c_e min(l_f,l_g) = Φ_e + c_e l_g = φ_e(d) is
bounded; for d ≤ 0 it equals c_e d + φ_e(d), also bounded (continuous on d ≤ 0 with a finite limit at
−∞). So |Φ_e + c_e min(l_f,l_g)| ≤ K(β_e), exactly as claimed — the bound depends on β_e only.
Anchor edge: Φ_e + c_e min(l_f,L_e) is bounded by K(β_e,L_e), and
|min(l_f,L_e) − min(l_f,0)| ≤ |L_e|, so Φ_e + c_e min(l_f,0) is bounded by K(β_e) + c_e|L_e|, finite
for a_e ∈ (0,∞). Hence |E(l) − P(l)| ≤ C(β, a) < ∞ for

P(l) = π Σ_f l_f − Σ_{internal e} c_e min(l_f,l_g) − Σ_{anchor e} c_e min(l_f,0).  (S5)

Sign/limit sanity (recorded because it fixes the sign structure): for l ≡ +t, P = t(π|F| − I(F));
for l ≡ −t, P = t(I(F) + B(F) − π|F|). Both must be ≥ 0 — i.e. the two cut families are the two
asymptotic directions, which is exactly how the two integrals below split.

## 5. Signed layer identity — verified term by term

Use x = ∫_0^∞ 1[x>t] dt − ∫_0^∞ 1[x<−t] dt. Apply it to each term of (S5):
- π Σ_f l_f  ↦  +∫_0^∞ π|S_t^+| dt − ∫_0^∞ π|S_t^-| dt,  S_t^± := {f : ±l_f > t}.
- −Σ_internal c_e min(l_f,l_g): 1[min > t] = 1[both ends > t] (weight sums to I(S_t^+));
  1[min < −t] = 1[at least one end < −t] (weight sums to I(S_t^-) + the internal part, i.e. internal
  crossing edges, of B(S_t^-): both-ends-in-S_t^- edges contribute c_e here as well).
- −Σ_anchor c_e min(l_f,0): the positive layer is 1[min(l_f,0) > t] ≡ 0 for t ≥ 0 (an anchor at log 0
  never contributes a positive minimum); the negative layer is 1[min(l_f,0) < −t] = 1[l_f < −t] for
  t ≥ 0, i.e. exactly the anchor part of B(S_t^-).

Summing, and noting [internal edges with ≥ 1 end in S] ∪ [anchor edges with face in S] = I(S) + B(S):

P(l) = ∫_0^∞ [ π|S_t^+| − I(S_t^+) ] dt + ∫_0^∞ [ I(S_t^-) + B(S_t^-) − π|S_t^-| ] dt ,  (S6)

which is the doc's identity verbatim, including the convention I(∅) = B(∅) = 0 making the empty-set
integrand 0. Exact, not asymptotic: no remainder term appears because each factor of (S5) is
piecewise linear in l.

## 6. Coercivity, existence, uniqueness — verified

Let η_lo = min_{∅ ≠ S ⊆ F} ( π|S| − I(S) ), η_hi = min_{∅ ≠ S ⊆ F} ( I(S) + B(S) − π|S| ),
η = min(η_lo, η_hi) > 0 (finitely many nonempty subsets). For each t, the first integrand is 0 if
S_t^+ = ∅ and ≥ η_lo ≥ η otherwise; likewise the second with η_hi. Hence

P(l) ≥ η ( ∫_0^∞ 1[S_t^+ ≠ ∅] dt + ∫_0^∞ 1[S_t^- ≠ ∅] dt ) = η ( (max_f l_f)^+ + (max_f (−l_f))^+ ) ≥ η ‖l‖_∞ .

With §4, E(l) ≥ η‖l‖_∞ − C → +∞: E is coercive. E is C² and strictly convex; coercive + strictly
convex ⟹ a unique global minimizer exists in R^F, and there ∇E = G = 0, i.e. (D3) holds with all
l_f finite, hence all R_f = e^{l_f} > 0. Uniqueness of the critical point is strict convexity alone.
Note the *margins* η_lo, η_hi depend only on {c_e} = {π − β_e}, and C only shifts the additive
constant: **existence and uniqueness are uniform over every assignment of positive anchor radii**,
which is precisely the doc's "for EVERY assignment of positive anchor radii". The doc is also right
that this is stronger than LOG-RADIUS-LAPLACIAN's local statement ("unique critical point if exists,
subject to existence"): §4–§6 upgrade "if exists" to "exists".

## 7. Necessity and the exact status of the two cut families

Sum (D3) over S and let X := Σ over crossing edges of the half-angle at the S-end, Y := Σ over
internal edges with both ends in S of c_e = I(S):

π|S| = I(S) + X,  0 < X < B(S) whenever B(S) > 0,  and X = 0 iff S has no crossing edge.

Strictness of h (R, T finite and positive on both sides of each edge, §1) gives the strict upper bound
termwise. B(S) ≥ min_e c_e > 0 for every nonempty S: for S = F the crossing edges are exactly the
anchor edges (hypothesis: ≥ 1), and for ∅ ≠ S ⊊ F connectivity gives an edge leaving S (internal or
anchor). Hence X > 0 strictly and both inequalities of the doc hold with strict signs:

I(S) < π|S| < I(S) + B(S)  for every ∅ ≠ S ⊆ F.  (C)

Two consequences worth recording (the doc is weaker than provable here):
- The lower family is *not* implied by the upper family. Explicit witness inside the theorem's stated
  generality (parallel edges counted with multiplicity): F = {f,g}, five parallel internal edges with
  c_e = 0.9π (β_e = 0.1π), one anchor edge at f with c_1 = 0.95π. Upper cuts: π < 5.45π, π < 4.5π,
  2π < 5.45π — all hold. Lower cut for S = F: 2π > I(F) = 4.5π fails. Directly: adding the two face
  equations gives 2π = 5·0.9π + h_f^{(anchor)} > 4.5π, contradiction, so (C) correctly reports
  infeasibility. For |S| = 1 the lower cut is automatic (no self-loops ⟹ I = 0), so the lower family
  only bites from |S| ≥ 2. Both families are load-bearing, and (S6) shows they are exactly the two
  asymptotic directions of §5.
- The doc's closing hedge ("at non-strict cut equalities … positive solutions need not exist") can be
  strengthened to "no solution exists", for every positive anchor assignment: if π|S| = I(S) then
  X = 0 while B(S) > 0 forces a crossing edge with h > 0 strictly; if π|S| = I(S) + B(S) then X = B(S)
  forces every crossing half-angle to equal its c_e, impossible at finite positive radii. So (C) with
  strict signs is exactly the existence region, and its boundary is non-attained. (The "divergence"
  picture is the η = 0 case of §6, consistent.)

## 8. Calibration read from the lead's own controls (not proof, not re-run)

- `dirichlet-cut-control.json`: 16 faces, 65535 = 2^16 − 1 subsets, min lower margin π (attained at a
  singleton, where I = 0 — automatic, as in §7), min upper margin 2.9758… (mask 16384); plus 100
  exact-rational comparisons of "direct P" against the level-set layer sum with Fractions. Reading
  the script confirms the layer sum is built as (t_1 − t_0)·integrand on consecutive levels with the
  set sampled between levels, i.e. a correct implementation of (S6); my §5 derivation is the symbolic
  version of it, and the two agree. Positive margins mean the candidate's β lies strictly inside (C),
  so §6 predicts a unique positive solution for *any* positive anchor radii there.
- `dirichlet-radius-solver-control.json` / `dirichlet_radius_solver.py`: the kernel assembles
  H[f,f] += w, H[f,g] −= w with the same w_e as (S3) and hf = arctan2(t sin β, 1 − t cos β) as in §1;
  it recovers the candidate's 16 radii (max error 6.7e−16) and its scale check
  max|Σ_g ∂l_f/∂log a_g − 1| = 7.8e−16 is the numerical shadow of the invariance identity I prove in
  §9.2. This is calibration of the implementation against my §1–§2 formulas; it certifies nothing on
  the continuum, and the file does not claim it does.

## 9. Findings: gaps, and two sharpenings

No counterexample, no false step, no missing hypothesis in (C) itself. Six items, ordered by relevance:

**9.1 (presentational, necessity).** "B(S)>0 follows connectivity to the boundary" carries more weight
than the sentence suggests: it is what makes the *lower* inequality strict (X > 0 needs a crossing
edge), not only the upper one. Recommend naming both uses, and noting that for S = F the crossing edges
are precisely the anchor edges.

**9.2 (stated but unproved in the doc; provable in 3 lines).** "monotone in anchor radii by the
comparison principle". Proof: DG is a symmetric positive-definite Z-matrix (S4), hence a nonsingular
M-matrix, hence (DG)^{-1} ≥ 0 entrywise, strictly positive when the face graph is connected to an
anchor. From the kernel, ∂G_f/∂L_e = −w_e for anchor edges incident to f and 0 otherwise, so
∂l/∂L = (DG)^{-1}(−B^{(L)}) with −B^{(L)} ≥ 0; therefore every ∂l_f/∂L_e > 0. Scale invariance
(l → l + λ1, L → L + λ1 is a symmetry of G = 0, so by uniqueness l(β,L+λ1) = l(β,L) + λ1) gives
Σ_e ∂l_f/∂L_e = 1, which is exactly the control's 7.8e−16 check. Scope note: this is monotonicity of
the abstract system in the anchor parameters, not a statement about covers.

**9.3 (sharpening: analyticity and the shape of the elimination region).** G is real-analytic on the
open set {β ∈ (0,π)^E} × R^F × R^{anchors} because the atan2 argument keeps Im = e^{L_e} sin β_e > 0
(§1); DG ≻ 0 there, so by the analytic IFT l = l(β,L) is real-analytic. The elimination region is
{β : (C) holds}, an open **convex polyhedron** in β because each inequality is linear in
c_e = π − β_e (equivalently: open polytope in c). So the doc's "explicitly described open polytope of
beta" is correct; "polyhedron/convex" is the precise wording.

**9.4 (scope, degeneracy side not mentioned).** Necessity's strictness in §7 uses 0 < R_f < ∞ on both
endpoints of every edge. The file excludes zero anchor radii and β endpoints but does not say that a
degenerate configuration with a zero or unbounded face radius is outside the necessity argument. The
theorem's own claim (a *positive* solution) is unaffected; this only matters if someone tries to apply
the strict cuts to a degenerate limit of covers.

**9.5 (hypothesis bookkeeping across the two files).** "hence symmetric positive definite" in
DIRICHLET relies on the Data paragraph's connectivity + anchor assumptions, while
LOG-RADIUS-LAPLACIAN states them at the point of use. Not an error; a cross-reference would prevent
someone applying PD to an anchorless closed network (where DG·1 = 0).

**9.6 (the doc's own hedge is fine, one wording).** "the conditions are exponential in face count; a
coherent-angle flow feasibility formulation/min-cut separation can test them" — correct as a method
note, and §7's LP-style reading (demand vs. capacity-into-S, plus strict positivity of crossing
half-angles) is the reason the two families are the complete obstruction. I did not verify the
min-cut separation claim computationally and the file does not rely on it.

## 10. What this does and does not give (checked against the doc's own limits)

Confirmed correct in both files: (i) only the real-face log-radii are eliminated —
R = R(β, a) is a unique real-analytic function on the open cut region; (ii) no radius cap R_f ≤ U
follows (coercivity bounds ‖l‖_∞ only via the data constant C; the solution may exceed any prescribed
U — the doc says so: "The radius caps R_f<=U remain additional constraints, not implied by
existence"); (iii) no geometric embedding, no boundary cyclicity, no unit-disk closure (LOG's
"hard boundary cyclicity constraints" stay open); (iv) β is not eliminated; (v) no statement for
β ∈ {0,π} or zero anchor radii without a separate limit analysis; (vi) nothing here bears on any
global n14/n12 optimum, and the file asserts no such thing. The persistent disclaimer in LOG ("no
claim potential convexity in beta, no joint global cover convexity") is also correct: DG is positive
definite in l at fixed (β, a); the β-dependence of the *equation* is not convexity of any joint
functional.

**The one genuinely external interface.** DIRICHLET takes the system (D1)+(D3) as given ("in this
problem's angle convention"). The step from an actual cover's fixed-angle data to that system
(γ_fe = atan2(T sin β_e, R_f − T cos β_e), Σ over the three face edges = π, γ_fe + γ_ge = π − β_e) is
supplied by `lead/FLAT-DISK-ANGLE-INTERFACE.md` §1 and the boundary variants
(`BOUNDARY-FACET-RADIUS-PROOF.md`, `BOUNDARY-CYCLICITY-*`), not inside the audited file. That is a
documentation dependency, not a mathematical gap, but a reader must not read (C) as a statement about
covers. I verified only that these files use *the same* h and the *same* identity (S1); I did not
re-audit the covering-side extraction, which is outside this task's scope.

## 11. Combined statement I am prepared to sign as audited

For a finite connected real-face network with at least one anchor edge, β_e ∈ (0,π), 0 < a_e < ∞, and
any prescribed positive anchor radii, the system Σ_{e∋f} atan2(e^{l_g} sin β_e, e^{l_f} − e^{l_g} cos β_e)
= π (anchor sides l_g = log a_e) has a solution l ∈ R^F **iff** I(S) < π|S| < I(S)+B(S) for every
nonempty S ⊆ F; the solution is then unique, real-analytic in (β, log a), increasing in each anchor
radius with Σ_e ∂l_f/∂log a_e = 1, and the existence region is the open convex polyhedron defined by
the cuts, independent of the anchor radii. Proof level: analytic, self-contained once the angle
interface of `FLAT-DISK-ANGLE-INTERFACE.md` is granted. Beyond this, no radius cap, no embedding, no
cover-level or n14 consequence.

## 12. Next minimal obligation (not started, out of scope here)

Nothing in this theorem is left open. The only remaining bearing interface for the project is the
identification of the *covering* problem's angle/radius constraints with (D1)+(D3) plus the cap and
cyclicity rows, i.e. exactly the obligations the two files already declare as unproved
("radius caps / boundary closure still unproved global constraints" in `STATUS.md` line 152). A
subsequent audit should target the cap-plus-cyclicity joint system, not this theorem.
