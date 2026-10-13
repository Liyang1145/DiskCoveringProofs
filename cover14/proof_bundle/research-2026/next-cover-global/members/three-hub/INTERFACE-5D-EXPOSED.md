# n14 k=11: 5D hub domain + exposed-atom necessity (interface, v3)

Scope: writes only in `members/three-hub/`. Facts used: `CORE-COUNT-REDUCTION.md`
(C1142: for r ≤ U, k ∈ {10,11}), P1–P8 of `THREE-HUB-GEOMETRY.md` v2.
U = 0.33173203427623414, a = 1−2U = 0.33653593144753172 > U.

## 0. Fixes to v2 wording (Lead review)

* **Collinearity is IMPOSSIBLE, not a legal degeneracy.** P2 gives 0 ∈ *int*
  conv{h₁,h₂,h₃}. If the three hubs were collinear, their directions would take at
  most two values θ, θ+π, so the three core arcs would have at most two distinct
  centres and halfwidths < π/2 each, whence the union's complement contains an arc of
  length ≥ π − max(β_i+β_j) > 0 and cannot be covered by a third arc of the same form.
  Hence v2's phrase "hubs collinear ... keep as degeneracy" is withdrawn: collinear
  hub triples are excluded by P2 + P3, and no case analysis needs them.
* No random Nelder–Mead / grid: the earlier 4000-trial probe is withdrawn as a task
  (it gave 0.32675 < U, consistent with P8, and proves nothing; it is not repeated).

## 1. Enlarging to radius U (label cleanup)

Given a cover at r ≤ U with k = 11 active disks, enlarge every disk to radius U.
Active disks stay active, so the enlarged cover at radius U has k′ ≥ 11; by C1142
(applied at radius U) k′ ≤ 11, hence **k′ = 11 and exactly three disks are inactive**
(14 − 11), i.e. all three hubs satisfy the *strict* **|h_j| < 1−U**. The core
B(0,a), a = 1−2U, is then covered by these three inactive disks (points with |x| < a
are at distance > U from every active centre since those have norm ≥ 1−U).
So from now on: **all 14 disks have radius U; 11 are active; 3 are strictly inactive
hubs with |h_j| < 1−U and cover the closed core.** This is the canonical form of the
k11 branch (no symmetry, no contacts assumed).

## 2. Two-sided norm window for the hubs

Upper: |h_j| < 1−U (inactive at radius U). Lower: each hub has a nonempty essential
arc (P4) with halfwidth ≤ asin(U/a) < π/2; the arcs cover S(0,a) and 2Σβ_j ≥ 2π, so
at least one β_j ≥ π/3, giving for that hub
    |h_j| ≥ a·sin(π/3)·(something) — concretely: β(t) = π/3 forces
    t ∈ [t₋, t₊] with t₋ = a cos(π/3) − sqrt(U² − a²sin²(π/3)) hmm replaced below.
Exact usable form: cos β(t) = (a²+t²−U²)/(2at); β(t) ≥ π/3 ⟺ a²+t²−U² ≤ a t ⟺
    t² − a t + (a²−U²) ≤ 0,
so **t ∈ [ (a − sqrt(a²−4(a²−U²)))/2 , (a + sqrt(...))/2 ]** and in particular
t ≥ a − U (with equality only in the degenerate β = 0 case), i.e. **|h_j| ≥ a − U > 0**
for every hub of a covering triple.

## 3. Explicit 5D closed relaxation

Rotate so the hub of largest norm is h₁ = (t,0), t = |h₁| > 0; then the other two are
written (x₂,y₂), (x₃,y₃). Reflection/relabelling lets us take y₂ ≥ 0 ≥ y₃, and P2
(0 ∈ int conv) is equivalent here to: y₂ > 0 > y₃ and the two polar angles φ₂, φ₃
measured from the +x axis satisfy φ₂ ∈ (0,π), φ₃ ∈ (π, 2π) with **both cyclic gaps
< π**, i.e. φ₂ < π, φ₃ − φ₂ < π, 2π − φ₃ < π. The relaxation is the closed set

    D5 = { (t, x₂, y₂, x₃, y₃) :
            t ∈ [a−U, 1−U),
            |h_j| ≤ t,  |h_j| < 1−U      (j = 2,3),
            y₂ ≥ 0 ≥ y₃,  gaps(φ) < π,
            the three arcs of S(0,a) cover the circle }.

The last condition is the **exact endpoint/union test** on three arcs (the union of
three closed arcs covers S¹ iff no complementary gap between consecutive endpoints is
nonempty); it is *not* the pairwise "β_k+β_{k+1} ≥ g_k" form, which v2 wrongly used.
D5 is 5-dimensional (rotation used up; reflection/relabel used up) and bounded; no
dimension reduction to 3 parameters is claimed anywhere.

## 4. Exposed-atom necessity (correct argument, any number of hubs)

Let H = ⋃_{j=1}^{3} B(h_j,U) (strictly inside D since |h_j| + U < 1). Statement:
**every point of ∂H ∩ int D is covered by one of the 11 active disks.**

*Proof.* Fix x ∈ ∂H ∩ int D. Since x is a boundary point, there are points x_n → x
with x_n ∉ H; for large n also x_n ∈ D (x ∈ int D). By definition of H, x_n is not in
any hub disk, so x_n is covered by one of the 11 active disks. There are finitely many
of them, so one active disk contains infinitely many x_n, hence by closedness contains
x. ∎

Two remarks.
1. This argument uses only the definition of the boundary (existence of nearby outside
   points) and finiteness+closedness. It needs **no** outward normal, no transversality
   and no tangent-cone analysis, and therefore is **immune to 3-way corners**: a
   "triple point" where all three hub circles meet is *interior* to H whenever the
   three vectors x−h_j positively span R² (then every direction v has some
   ⟨v, x−h_j⟩ < 0), so such points are not in ∂H at all and impose no requirement.
   No equality/tangency exclusion is needed for the necessity statement itself.
2. For atoms (the *sufficient* dual direction) it is convenient, and legitimate, to
   use **strict-exclusion atoms**: place atoms only at points x with |x−h_j| > U for
   the hub they are meant to lie on the outside of, and drop equalities; this avoids
   the measure-zero triple-point case in the atom construction and cannot lose the
   demand: the exposed set minus finitely many points has the same measure, and the
   coverage demand is an integral.

## 5. Interface for the k11 exclusion (to be filled by the atomic dual)

Required demand (measure, not pointwise): ∫ over ∂D plus ∫ over ∂H (the three exposed
hub arcs E_j = ∂B(h_j,U) minus the parts inside the other two hubs), restricted to
int D; each of the 11 active disks contributes at most its boundary arc on ∂D and its
arcs on the three hub circles. Weights: exact rational circle atoms as in the n12
atomic kernel; the hub-side atoms must be filtered by **strict** exclusion from the
other two hubs (remark 2 above), and the domain is D5 (5 parameters). Expected
degeneracies inside D5: two hubs with equal norms (tie for "largest norm" — handle by
closed extension, no ε), arcs tangent to each other (A_i∩A_j a point), and a hub arc
degenerating to a point (β_j → 0 gives t → a−U or t → a+U); all are interior points of
the closed relaxation, so the closed D5 covers them.

No claim registered; P1–P8 and §4 are analytic statements awaiting independent review.
