# n=13/14/15/25 structural selection (rev. 2 — corrected n25 input, corrected
# status labels, core argument restated via open core + closure)

Scope: `research-2026/next-cover-global/members/structure/` (this file only).
Object: D = closed unit disk, n equal closed disks of radius r covering D,
r_D(n) = min r, centers arbitrary in R², repeats/tangency allowed.
Old n11/n12 material is read-only here.

## 0. Corrections to rev. 1 (kept visible, not silently overwritten)

1. **n25 input was wrong.** Friedman's fetched value is R = √6 + √3, hence
   U(25) = 1/(√6+√3) = 0.239146311738…, not 0.21585. All n25 numbers below are
   recomputed; the selection no longer rests on the wrong figure. (This value is
   literature/best-known, NOT a workspace-certified bound; labelled as such.)
2. **Status labels.** n11 is **C924 (proved-interval)**, n12 is **C1141
   (proved)**. Rev. 1's "proved-exact" was wrong for both.
3. **Core argument.** The ring–core step must run on the OPEN core with a strict
   inequality and then pass to the closure; equality on the core boundary may
   not be used to delete boundary cases. Restated as (I) below.

## 1. General inequality package (uniform class exclusion)

(I) **Ring–core separation (strict on the open core, then closure).** Active
    centers have norm ≥ 1−r. Let a := 1−2U and take p with |p| < a. Then
        |p−c| ≥ |c| − |p| > (1−r) − (1−2U) = 2U − r ≥ r,
    the last step because r ≤ U (equality 2U−r = r only at r = U, and there the
    strict |p| < a still gives |p−c| > U = r). Hence no active disk covers any
    point of the open core, so every open-core point lies in some hub disk; the
    hub union is a finite union of closed disks, hence closed, so
        closed core ⊆ closed hub union.
    On the boundary |p| = a one only has |p−c| ≥ r with equality possible, so
    those points may be covered by active disks too — which is exactly why the
    closure step, and not a direct deletion, is required.

(II) **Core-count recursion.** If a > U, ∂B(0,a) is covered by m disks of
    radius U, each covering an arc of half-width ≤ asin(U/a) (maximal at the
    orthogonal position; valid because a > U), so
        m ≥ m_min := ceil(π / asin(U/a)),  hence  k ≤ n − m_min.
    If a ≤ U one hub at the origin suffices, m_min = 1 and the bound is
    vacuous: k ≤ n−1. (Recursive next level: B(0, a−2U) for a > 2U.)

(III) **No-chord inequality.** If non-adjacent active arcs overlap, the arc J
    spanned by the crossing pair obeys |J| ≤ 2·asin(2r) (the arc's chord is at
    most the diameter 4r of the covering ball B(p,2r), and 2sin(θ/2) ≤ 4r), and
    the remaining k−3 arcs each have length ≤ 2·asin(r). Therefore
        2π ≤ 2·asin(2r) + (k−3)·2·asin(r)  ⟹  π ≤ asin(2r) + (k−3)·asin(r),
    so non-adjacent active disks are disjoint whenever that last inequality is
    false, i.e. for k ≤ k_nc(r) := floor(3 + (π − asin(2r))/asin(r)).
    The k=9 instance is the verified C933 (`lead/NINE-RING-NO-CHORDS.md`); the
    k=10 instance for r < 1/3 is proved in `NO-CHORD-n14.md` (this directory).

(IV) **Arc bound.** k ≥ k_min := ceil(π / asin(r)).

(V) **Dual count.** Under (III): no three active disks share a point, so any
    common-point/Delaunay edge joins adjacent labels and no triangle has all
    three vertices active; the dual triangulation with k boundary vertices and
    m interior hubs then has T = k + 2m − 2 triangles (k=9 gives the 7+2m of
    `lead/K9-SHARP-THEOREM.md`). Whether an embedded straight-line dual exists
    is a separate obligation (see `NO-CHORD-n14.md` §4).

## 2. Per-n structure at the certified upper bound (rev. 2)

| n | U (source) | asin U | k_min | m_min | admissible k | T(k_min) | k_nc | no-chord margin at k_min |
|---|---|---|---|---|---|---|---|---|
| 11 | 0.37998385 (C924, proved-interval) | 22.333° | 9 | 1 | 9–10 | 11 | 8 | −3.46° |
| 12 | 0.36110296 (C1141, proved) | 21.168° | 9 | 1 | 9–11 | 13 | 9 | +6.76° |
| 13 | 0.34664546 (proved-interval) | 20.282° | 9 | 1 | 9–12 | 15 | 9 | +14.42° |
| **14** | **0.33173203** (proved-interval) | 19.374° | **10** | **3** | **10–11** | **16** | **10** | **+2.82°** |
| 15 | 0.31814293 (proved-interval) | 18.551° | 10 | 3 | 10–12 | 18 | 10 | +10.63° |
| 16 | 0.30821980 (proved-interval) | 17.952° | 11 | 4 | 11–12 | 19 | 10 | −1.67° |
| 25 | **0.239146311738** = 1/(√6+√3) (literature only) | 13.836° | **14** | **7** | **14–18** | 34 | **13** | **−0.77°** |

Cross-validation of (III): at U(12) it gives k_nc = 9, exactly the k=9 range for
which C933 was proved.

## 3. Verdict (rev. 2)

**n14 remains the target, and is now better separated from the field.**
* n14: admissible k ∈ {10,11} only. The core-count step is real because
  a = 1−2U = 0.33654 > U = 0.33173 ⇒ m ≥ ceil(π/asin(0.9854)) = 3 ⇒ k ≤ 11.
  The no-chord inequality reaches exactly the minimal case k=10 (margin +2.82°,
  and by `NO-CHORD-n14.md` even the clean sufficient condition r < 1/3
  suffices). The remaining k=11 case has only m = 3 hubs and is NOT removed by
  counting (3 disks cover a disk of radius a iff U/a ≥ √3/2 = 0.866;
  here U/a = 0.9854).
* n15: k ∈ {10,11,12}, no-chord on the minimum, three cases.
* n13: k ∈ {9,10,11,12}; no-chord covers only k=9, and that case is 9 rings +
  4 hubs, one hub more than the solved n12 k=9 network theorem.
* **n25 (corrected): k ∈ {14,…,18}, five cases, and the no-chord argument does
  NOT even reach its minimum (k_nc = 13 < 14). Strictly worse than in rev. 1;
  out of the front line.**
* n16: no-chord fails at its minimum (k_nc = 10 < k_min = 11).

Ranking: **n14 > n15 > n13 > n16 > n25.**

## 4. Exact gap list

1. **(III) general k.** The k=10, r<1/3 instance is now proved (companion
   file). For k ≥ 11 the inequality has the same shape but no instance is
   proved.
2. **(II) sharpness.** The m-disk covering thresholds (√3/2 for m=3,
   √2/2 for m=4) are classical but not imported here; they decide whether k=11
   stays admissible for n14.
3. **n14 k=10 classification.** Enumerate the 10-boundary + 4-hub duals
   (no ring chord, no all-ring triangle, T=16) and produce a sharp lower bound
   at r ≤ U(14): the analogue of C986, and the real cost of the n14 route.
4. **n14 k=11.** Decide by core geometry + capacity (3 hubs covering B(0,a),
   ratio 0.9854), not by counting.
5. **Lower bound side.** Old radial-family duals give ≈0.3353 (n13) / ≈0.3199
   (n14); they do not meet U(14) = 0.33173, so the interval still has to be
   closed on that side.
6. **(V)** Delaunay existence/embedding is established only for the k=9
   instance; for n14 k=10 it is a separate obligation.

No claim is registered here; the rows are structure, not proofs.
