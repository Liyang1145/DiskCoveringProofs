/-
  DSHTopologyOwnership.lean — DSH-TOPO-C2 (part A): ownership / no-bubble of the active
  boundary arcs of an ACTUAL eleven-disk cover.

  ## Object, domain, quantifiers

  `Point = EuclideanSpace ℝ (Fin 2)`; `D = unitDisk`; `Covers c r` (`Definitions.lean`);
  `MeetsCircle c r i` and `BoundaryIdx c r` (`Assembly/BoundaryCount.lean`) — the actual
  *boundary disks*, i.e. those whose closed disk meets `S¹`.  Everything below is over the
  REAL cover domain: centres `c : Fin 11 → Point` are arbitrary (repeated, outside, redundant
  and degenerate configurations all allowed), `r : ℝ` arbitrary, and the ONLY cover input is
  `Covers c r`.  No sampling, no representative points, no symmetry or generic-position
  restriction, no hypothesis about the number of boundary disks.

  ## Ownership

  `OwnsPt c i x` (point level) and `Owns c i t` / `OwnsB c r i t` (angle level on `(0,2π)`)
  say: site `i` is a NEAREST site, and every strictly smaller index is *strictly* farther.
  The strict conjunct is a tie-break, so ownership is single-valued even when two sites are
  equidistant (the degenerate case is handled, not assumed away).

  ## Statements proved here

  Unconditional in `c`, `r`:
  * `ownsPt_exists`, `ownsPt_unique`, `ownsPt_owner_unique_exists` — every point of the plane
    has EXACTLY ONE owner (`∃!`): no double ownership.
  * `ownsPt_ne_of_ne` — distinct sites never own the same point.
  * `ownsPt_iff_owns_circleAngle` — point ownership = angle ownership of `S¹`.
  * `ownsPt_meetsCircle_of_covers`, `ownsPt_dist_le_of_covers` — for an actual cover and
    `‖x‖ = 1`, the owner of `x` is a boundary disk and is within `r` of `x`.
  * `unique_ownership_points` — **the C2 headline**: for `Covers c r` and `x ∈ S¹` there is
    EXACTLY ONE `i` with `MeetsCircle c r i ∧ OwnsPt c i x ∧ dist x (c i) ≤ r`.  This is
    "each point of each active boundary arc is covered by exactly one owning boundary disk":
    the `∃!` gives no double ownership, and `dist x (c i) ≤ r` with the owner being a boundary
    disk gives no uncovered bubble/gap.
  * `ownerSet_pairwiseDisjoint`, `iUnion_ownerSet`, `iUnion_ownerSet_of_covers` — the owned
    angle sets are pairwise disjoint and their union is exactly `(0, 2π)`.
  * `ownsB_iff_ownsPt` — for a boundary disk, owning among the boundary disks is the SAME as
    owning among all eleven sites (so the boundary ledger of part B is the full ownership).
  * `ownsB_exists`, `ownsB_unique` — `∃!` owner among the boundary disks.

  Part B (`DSHTopologyOwnershipLedger.lean`) carries the measure ledger and the conditional
  exactly-nine-boundary-disk statements.

  Provenance.  This is obligation C2 of `evidence/codex-handoff/DSH-TEAM-START-HANDOFF.md`
  §2C.  The angle-level measure core was previously gated green in
  `evidence/cline-six-20260930/ownership-topology/OwnershipLedger.lean` (lead gate3, exit 0)
  for `Fin 9` under the abstract premise `NineCapCover`; that file lives in `evidence/`, is
  not importable as a module and is not the real cover domain.  Here ownership is redone for
  the real cover (`Fin 11`, `Covers`, `BoundaryIdx`) with the point-level statements, the
  boundary/all-eleven identification and the explicit degenerate branches.

  No `sorry`, no custom axiom, no `native_decide`.
-/
import Mathlib
import N11Formalization.Definitions
import N11Formalization.Geometry.ArcCovering
import N11Formalization.Assembly.BoundaryCount

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace N11Formalization.DSHTopologyOwnership

open MeasureTheory

noncomputable section

/-! ## §0  Point-level ownership: existence, uniqueness, no double ownership -/

/-- **Ownership at a point.**  Site `i` owns `x` when `i` is a nearest site and every
strictly smaller index is *strictly* farther.  The second conjunct is the tie-break that
makes the owner single-valued when two sites are equidistant. -/
def OwnsPt (c : Fin 11 → Point) (i : Fin 11) (x : Point) : Prop :=
  (∀ j : Fin 11, dist x (c i) ≤ dist x (c j)) ∧
    (∀ j : Fin 11, j < i → dist x (c i) < dist x (c j))

/-- The owning site is a nearest site among all eleven. -/
theorem ownsPt_isNearest {c : Fin 11 → Point} {i : Fin 11} {x : Point}
    (h : OwnsPt c i x) : ∀ j : Fin 11, dist x (c i) ≤ dist x (c j) := h.1

/-- **Every point has an owner.** -/
theorem ownsPt_exists (c : Fin 11 → Point) (x : Point) : ∃ i : Fin 11, OwnsPt c i x := by
  classical
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 11))
    (fun i : Fin 11 => dist x (c i)) ⟨0, Finset.mem_univ 0⟩
  set S : Finset (Fin 11) :=
    Finset.univ.filter (fun i : Fin 11 => ∀ j : Fin 11, dist x (c i) ≤ dist x (c j)) with hS
  have hSne : S.Nonempty :=
    ⟨i₀, by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      exact hi₀ j (Finset.mem_univ j)⟩
  refine ⟨S.min' hSne, (Finset.mem_filter.mp (S.min'_mem hSne)).2, ?_⟩
  intro j hj
  by_contra hcon
  rw [not_lt] at hcon
  have hjS : j ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    exact le_trans hcon ((Finset.mem_filter.mp (S.min'_mem hSne)).2 k)
  exact absurd ((Finset.isLeast_min' S hSne).2 hjS) (not_le.mpr hj)

/-- **Uniqueness of ownership**: at most one site owns a given point. -/
theorem ownsPt_unique {c : Fin 11 → Point} {x : Point} {i i' : Fin 11}
    (hi : OwnsPt c i x) (hi' : OwnsPt c i' x) : i = i' := by
  rcases lt_trichotomy i i' with h | h | h
  · exact absurd (hi'.2 i h) (not_lt.mpr (hi.1 i'))
  · exact h
  · exact absurd (hi.2 i' h) (not_lt.mpr (hi'.1 i))

/-- **Exactly one owner per point** (`∃!` form). -/
theorem ownsPt_owner_existsUnique (c : Fin 11 → Point) (x : Point) :
    ∃! i : Fin 11, OwnsPt c i x :=
  let ⟨i, hi⟩ := ownsPt_exists c x
  ⟨i, hi, fun i' hi' => ownsPt_unique hi' hi⟩

/-- **No double ownership**: two distinct sites never own the same point. -/
theorem ownsPt_ne_of_ne {c : Fin 11 → Point} {x : Point} {i j : Fin 11} (h : i ≠ j)
    (hi : OwnsPt c i x) : ¬ OwnsPt c j x :=
  fun hj => h (ownsPt_unique hi hj)

/-- The owner of a covered point is within `r` of it. -/
theorem ownsPt_dist_le_of_covers {c : Fin 11 → Point} {r : ℝ} (hcov : Covers c r) {i : Fin 11}
    {x : Point} (hx : x ∈ unitDisk) (h : OwnsPt c i x) : dist x (c i) ≤ r := by
  obtain ⟨j, hj⟩ := hcov x hx
  exact le_trans (h.1 j) hj

/-- The owner of a point of `S¹` in an actual cover is a **boundary disk**. -/
theorem ownsPt_meetsCircle_of_covers {c : Fin 11 → Point} {r : ℝ} (hcov : Covers c r)
    {i : Fin 11} {x : Point} (hx : ‖x‖ = 1) (h : OwnsPt c i x) : MeetsCircle c r i :=
  ⟨x, hx, ownsPt_dist_le_of_covers hcov (le_of_eq hx) h⟩

/-! ## §1  Angle-level ownership on `(0, 2π)` (the measurable form) -/

/-- Inner product of `circleMap t` with a point, in coordinates. -/
theorem inner_circleMap_point (t : ℝ) (c : Point) :
    inner ℝ (circleMap t) c = Real.cos t * c.ofLp 0 + Real.sin t * c.ofLp 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, Fin.sum_univ_two, circleMap_apply_zero,
    circleMap_apply_one]
  ring

/-- `sqDist c t = ‖circleMap t - c‖²`, written in `(cos t, sin t)` so that measurability is
immediate and no continuity of `circleMap` is needed. -/
def sqDist (c : Point) (t : ℝ) : ℝ :=
  (1 + ‖c‖ ^ 2) - 2 * (Real.cos t * c.ofLp 0 + Real.sin t * c.ofLp 1)

theorem sqDist_eq_dist_sq (c : Point) (t : ℝ) : sqDist c t = dist (circleMap t) c ^ 2 := by
  unfold sqDist
  rw [dist_eq_norm, norm_sub_sq_real, circleMap_norm, inner_circleMap_point]
  ring

theorem measurable_sqDist (c : Point) : Measurable (sqDist c) := by
  have h3 : Measurable fun t : ℝ =>
      (1 + ‖c‖ ^ 2) - 2 * (Real.cos t * c.ofLp 0 + Real.sin t * c.ofLp 1) :=
    (measurable_const : Measurable fun _ : ℝ => (1 + ‖c‖ ^ 2)).sub
      ((measurable_const : Measurable fun _ : ℝ => (2 : ℝ)).mul
        ((Real.measurable_cos.mul_const (c.ofLp 0)).add
          (Real.measurable_sin.mul_const (c.ofLp 1))))
  exact h3

/-- `a² ≤ b²` with `a, b ≥ 0` gives `a ≤ b`. -/
theorem sq_le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have h2 := sq_le_sq.mp h
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at h2

/-- Distance comparison is squared-distance comparison. -/
theorem dist_le_dist_iff_sq (x a b : Point) :
    dist x a ≤ dist x b ↔ dist x a ^ 2 ≤ dist x b ^ 2 := by
  constructor
  · intro h; nlinarith [dist_nonneg (x := x) (y := a)]
  · intro h; exact sq_le_of_sq_le_sq dist_nonneg dist_nonneg h

/-- Strict form of `dist_le_dist_iff_sq`. -/
theorem dist_lt_dist_iff_sq (x a b : Point) :
    dist x a < dist x b ↔ dist x a ^ 2 < dist x b ^ 2 := by
  constructor
  · intro h; nlinarith [dist_nonneg (x := x) (y := a)]
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    have h2 : dist x b ^ 2 ≤ dist x a ^ 2 := by nlinarith [dist_nonneg (x := x) (y := b)]
    linarith

/-- **Ownership at an angle**: site `i` is nearest to `circleMap t`, and every strictly
smaller index is strictly farther. -/
def Owns (c : Fin 11 → Point) (i : Fin 11) (t : ℝ) : Prop :=
  (∀ j : Fin 11, sqDist (c i) t ≤ sqDist (c j) t) ∧
    (∀ j : Fin 11, j < i → sqDist (c i) t < sqDist (c j) t)

/-- The angle set owned by site `i`, inside the fundamental interval `(0, 2π)`. -/
def ownerSet (c : Fin 11 → Point) (i : Fin 11) : Set ℝ :=
  {t : ℝ | t ∈ Set.Ioo 0 (2 * Real.pi) ∧ Owns c i t}

theorem owns_exists (c : Fin 11 → Point) (t : ℝ) : ∃ i : Fin 11, Owns c i t := by
  classical
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 11))
    (fun i : Fin 11 => sqDist (c i) t) ⟨0, Finset.mem_univ 0⟩
  set S : Finset (Fin 11) :=
    Finset.univ.filter (fun i : Fin 11 => ∀ j : Fin 11, sqDist (c i) t ≤ sqDist (c j) t)
    with hS
  have hSne : S.Nonempty :=
    ⟨i₀, by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      exact hi₀ j (Finset.mem_univ j)⟩
  refine ⟨S.min' hSne, (Finset.mem_filter.mp (S.min'_mem hSne)).2, ?_⟩
  intro j hj
  by_contra hcon
  rw [not_lt] at hcon
  have hjS : j ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    exact le_trans hcon ((Finset.mem_filter.mp (S.min'_mem hSne)).2 k)
  exact absurd ((Finset.isLeast_min' S hSne).2 hjS) (not_le.mpr hj)

theorem owns_unique {c : Fin 11 → Point} {t : ℝ} {i i' : Fin 11}
    (hi : Owns c i t) (hi' : Owns c i' t) : i = i' := by
  rcases lt_trichotomy i i' with h | h | h
  · exact absurd (hi'.2 i h) (not_lt.mpr (hi.1 i'))
  · exact h
  · exact absurd (hi.2 i' h) (not_lt.mpr (hi'.1 i))

/-- **Point ownership is angle ownership of `S¹`.** -/
theorem ownsPt_iff_owns_circleAngle (c : Fin 11 → Point) {x : Point} (hx : ‖x‖ = 1)
    (i : Fin 11) : OwnsPt c i x ↔ Owns c i (circleAngle x) := by
  have hmap : circleMap (circleAngle x) = x := circleMap_circleAngle x hx
  have key : ∀ j : Fin 11,
      (dist x (c i) ≤ dist x (c j) ↔
        sqDist (c i) (circleAngle x) ≤ sqDist (c j) (circleAngle x)) ∧
      (dist x (c i) < dist x (c j) ↔
        sqDist (c i) (circleAngle x) < sqDist (c j) (circleAngle x)) := by
    intro j
    rw [sqDist_eq_dist_sq, sqDist_eq_dist_sq, hmap]
    exact ⟨dist_le_dist_iff_sq x (c i) (c j), dist_lt_dist_iff_sq x (c i) (c j)⟩
  constructor
  · intro h
    exact ⟨fun j => (key j).1.mp (h.1 j), fun j hj => (key j).2.mp (h.2 j hj)⟩
  · intro h
    exact ⟨fun j => (key j).1.mpr (h.1 j), fun j hj => (key j).2.mpr (h.2 j hj)⟩

theorem ownerSet_pairwiseDisjoint (c : Fin 11 → Point) :
    ∀ i j : Fin 11, i ≠ j → Disjoint (ownerSet c i) (ownerSet c j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro t ht ht'
  exact hij (owns_unique ht.2 ht'.2)

theorem iUnion_ownerSet (c : Fin 11 → Point) :
    Set.iUnion (fun i : Fin 11 => ownerSet c i) = Set.Ioo 0 (2 * Real.pi) := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
    exact hi.1
  · intro ht
    obtain ⟨i, hi⟩ := owns_exists c t
    exact Set.mem_iUnion.mpr ⟨i, ht, hi⟩

theorem measurableSet_ownerSet (c : Fin 11 → Point) (i : Fin 11) :
    MeasurableSet (ownerSet c i) := by
  classical
  have hle : ∀ j : Fin 11, MeasurableSet {t : ℝ | sqDist (c i) t ≤ sqDist (c j) t} :=
    fun j => measurableSet_le (measurable_sqDist (c i)) (measurable_sqDist (c j))
  have hlt : ∀ j : Fin 11, MeasurableSet {t : ℝ | sqDist (c i) t < sqDist (c j) t} :=
    fun j => measurableSet_lt (measurable_sqDist (c i)) (measurable_sqDist (c j))
  have h1 : MeasurableSet (⋂ j : Fin 11, {t : ℝ | sqDist (c i) t ≤ sqDist (c j) t}) :=
    MeasurableSet.iInter hle
  have h2 : MeasurableSet
      (⋂ j : Fin 11, {t : ℝ | j < i → sqDist (c i) t < sqDist (c j) t}) := by
    refine MeasurableSet.iInter (fun j => ?_)
    by_cases hj : j < i
    · simpa [hj] using hlt j
    · simpa [hj] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
  have h3 : MeasurableSet (Set.Ioo (0 : ℝ) (2 * Real.pi)) := measurableSet_Ioo
  have hEq : ownerSet c i = Set.Ioo 0 (2 * Real.pi) ∩
      ((⋂ j : Fin 11, {t : ℝ | sqDist (c i) t ≤ sqDist (c j) t}) ∩
        (⋂ j : Fin 11, {t : ℝ | j < i → sqDist (c i) t < sqDist (c j) t})) := by
    ext t
    simp only [ownerSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Owns]
    try tauto
  rw [hEq]
  exact h3.inter (h1.inter h2)

/-! ## §2  Boundary-restricted ownership and the actual cover -/

/-- Ownership among the boundary disks of an actual cover, with the same least-index
tie-break (comparison on the underlying `Fin 11` index). -/
def OwnsB (c : Fin 11 → Point) (r : ℝ) (i : BoundaryIdx c r) (t : ℝ) : Prop :=
  (∀ j : BoundaryIdx c r, sqDist (c i.1) t ≤ sqDist (c j.1) t) ∧
    (∀ j : BoundaryIdx c r, j.1 < i.1 → sqDist (c i.1) t < sqDist (c j.1) t)

/-- The angle set owned by the boundary disk `i`, inside `(0, 2π)`. -/
def ownerSetB (c : Fin 11 → Point) (r : ℝ) (i : BoundaryIdx c r) : Set ℝ :=
  {t : ℝ | t ∈ Set.Ioo 0 (2 * Real.pi) ∧ OwnsB c r i t}

/-- An actual cover has at least one boundary disk. -/
theorem boundaryIdx_nonempty_of_covers {c : Fin 11 → Point} {r : ℝ} (hcov : Covers c r) :
    (Finset.univ : Finset (BoundaryIdx c r)).Nonempty := by
  obtain ⟨j, hj⟩ := hcov (circleMap 0) (le_of_eq (circleMap_norm 0))
  exact ⟨⟨j, circleMap 0, circleMap_norm 0, hj⟩, Finset.mem_univ _⟩

/-- **Every angle has an owner among the boundary disks.** -/
theorem ownsB_exists (c : Fin 11 → Point) (r : ℝ)
    (hne : (Finset.univ : Finset (BoundaryIdx c r)).Nonempty) (t : ℝ) :
    ∃ i : BoundaryIdx c r, OwnsB c r i t := by
  classical
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (BoundaryIdx c r))
    (fun i : BoundaryIdx c r => sqDist (c i.1) t) hne
  set S : Finset (BoundaryIdx c r) :=
    Finset.univ.filter (fun i => ∀ j : BoundaryIdx c r, sqDist (c i.1) t ≤ sqDist (c j.1) t)
    with hS
  have hSne : S.Nonempty :=
    ⟨i₀, by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      exact hi₀ j (Finset.mem_univ j)⟩
  have himne : (S.image Subtype.val).Nonempty := hSne.image _
  have hmS : (S.image Subtype.val).min' himne ∈ S.image Subtype.val :=
    Finset.min'_mem _ _
  obtain ⟨i, hiS, hiv⟩ := Finset.mem_image.mp hmS
  refine ⟨i, (Finset.mem_filter.mp hiS).2, ?_⟩
  intro j hj
  by_contra hcon
  rw [not_lt] at hcon
  have hjS : j ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    exact le_trans hcon ((Finset.mem_filter.mp hiS).2 k)
  have hjm : j.1 ∈ S.image Subtype.val := Finset.mem_image.mpr ⟨j, hjS, rfl⟩
  have hmin : i.1 ≤ j.1 := by
    rw [hiv]
    exact (Finset.isLeast_min' (S.image Subtype.val) himne).2 hjm
  exact absurd hmin (not_le.mpr hj)

/-- **Uniqueness of boundary ownership**: at most one boundary disk owns an angle. -/
theorem ownsB_unique {c : Fin 11 → Point} {r : ℝ} {t : ℝ} {i i' : BoundaryIdx c r}
    (hi : OwnsB c r i t) (hi' : OwnsB c r i' t) : i = i' := by
  by_contra h
  have hv : i.1 ≠ i'.1 := fun hh => h (Subtype.ext hh)
  rcases lt_trichotomy i.1 i'.1 with hlt | heq | hgt
  · exact absurd (hi'.2 i hlt) (not_lt.mpr (hi.1 i'))
  · exact hv heq
  · exact absurd (hi.2 i' hgt) (not_lt.mpr (hi'.1 i))

/-- **Exactly one boundary owner per angle** (`∃!` form). -/
theorem ownsB_owner_existsUnique (c : Fin 11 → Point) (r : ℝ)
    (hne : (Finset.univ : Finset (BoundaryIdx c r)).Nonempty) (t : ℝ) :
    ∃! i : BoundaryIdx c r, OwnsB c r i t :=
  let ⟨i, hi⟩ := ownsB_exists c r hne t
  ⟨i, hi, fun i' hi' => ownsB_unique hi' hi⟩

theorem ownerSetB_pairwiseDisjoint (c : Fin 11 → Point) (r : ℝ) :
    ∀ i j : BoundaryIdx c r, i ≠ j → Disjoint (ownerSetB c r i) (ownerSetB c r j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro t ht ht'
  exact hij (ownsB_unique ht.2 ht'.2)

/-- **No gap**: the owned angle sets of the boundary disks cover `(0, 2π)` exactly. -/
theorem iUnion_ownerSetB (c : Fin 11 → Point) (r : ℝ)
    (hne : (Finset.univ : Finset (BoundaryIdx c r)).Nonempty) :
    Set.iUnion (fun i : BoundaryIdx c r => ownerSetB c r i) = Set.Ioo 0 (2 * Real.pi) := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
    exact hi.1
  · intro ht
    obtain ⟨i, hi⟩ := ownsB_exists c r hne t
    exact Set.mem_iUnion.mpr ⟨i, ht, hi⟩

/-- **Ownership among the boundary disks is ownership among all eleven sites.**  (For a
boundary disk `i`: it owns `x ∈ S¹` in the boundary sense iff it owns `x` among all sites.
A non-boundary disk is at distance `> r` from every point of `S¹`, hence can never beat a
covering boundary disk.) -/
theorem ownsB_iff_ownsPt {c : Fin 11 → Point} {r : ℝ} (hcov : Covers c r) {x : Point}
    (hx : ‖x‖ = 1) (i : BoundaryIdx c r) :
    OwnsB c r i (circleAngle x) ↔ OwnsPt c i.1 x := by
  have key := ownsPt_iff_owns_circleAngle c hx i.1
  constructor
  · intro h
    rw [key]
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · by_cases hjb : MeetsCircle c r j
      · exact h.1 ⟨j, hjb⟩
      · obtain ⟨j₀, hj₀⟩ := hcov x (le_of_eq hx)
        have hj₀b : MeetsCircle c r j₀ := ⟨x, hx, hj₀⟩
        have hdi : dist x (c i.1) ≤ r := by
          have hs1 : sqDist (c i.1) (circleAngle x) ≤ sqDist (c j₀) (circleAngle x) :=
            h.1 ⟨j₀, hj₀b⟩
          have hs2 : dist x (c i.1) ^ 2 ≤ dist x (c j₀) ^ 2 := by
            rw [← circleMap_circleAngle x hx, ← sqDist_eq_dist_sq, ← sqDist_eq_dist_sq]
            exact hs1
          exact le_trans ((dist_le_dist_iff_sq x (c i.1) (c j₀)).mpr hs2) hj₀
        have hjr : r < dist x (c j) := by
          by_contra hle
          rw [not_lt] at hle
          exact hjb ⟨x, hx, hle⟩
        have hle : dist x (c i.1) ≤ dist x (c j) := le_trans hdi hjr.le
        rw [sqDist_eq_dist_sq, sqDist_eq_dist_sq, circleMap_circleAngle x hx]
        exact (dist_le_dist_iff_sq x (c i.1) (c j)).mp hle
    · by_cases hjb : MeetsCircle c r j
      · exact h.2 ⟨j, hjb⟩ hj
      · obtain ⟨j₀, hj₀⟩ := hcov x (le_of_eq hx)
        have hj₀b : MeetsCircle c r j₀ := ⟨x, hx, hj₀⟩
        have hdi : dist x (c i.1) ≤ r := by
          have hs1 : sqDist (c i.1) (circleAngle x) ≤ sqDist (c j₀) (circleAngle x) :=
            h.1 ⟨j₀, hj₀b⟩
          have hs2 : dist x (c i.1) ^ 2 ≤ dist x (c j₀) ^ 2 := by
            rw [← circleMap_circleAngle x hx, ← sqDist_eq_dist_sq, ← sqDist_eq_dist_sq]
            exact hs1
          exact le_trans ((dist_le_dist_iff_sq x (c i.1) (c j₀)).mpr hs2) hj₀
        have hjr : r < dist x (c j) := by
          by_contra hle
          rw [not_lt] at hle
          exact hjb ⟨x, hx, hle⟩
        have hlt : dist x (c i.1) < dist x (c j) := lt_of_le_of_lt hdi hjr
        rw [sqDist_eq_dist_sq, sqDist_eq_dist_sq, circleMap_circleAngle x hx]
        exact (dist_lt_dist_iff_sq x (c i.1) (c j)).mp hlt
  · intro h
    rw [key] at h
    exact ⟨fun j => h.1 j.1, fun j hj => h.2 j.1 hj⟩

/-- **DSH-TOPO-C2 headline (unconditional part).**  For an actual cover `Covers c r` and a
point `x` of `S¹` there is **exactly one** owning boundary disk `i`, and that disk is within
`r` of `x`.  Reading: each point of each active boundary arc `S¹ ∩ closedBall (c i) r` is
covered by exactly one owning boundary disk — no double ownership, and no point of `S¹` is
left without an owner (no uncovered bubble/gap). -/
theorem unique_ownership_points {c : Fin 11 → Point} {r : ℝ} (hcov : Covers c r) :
    ∀ x : Point, ‖x‖ = 1 →
      ∃! i : Fin 11, MeetsCircle c r i ∧ OwnsPt c i x ∧ dist x (c i) ≤ r := by
  intro x hx
  obtain ⟨i, hi⟩ := ownsPt_exists c x
  have hb : MeetsCircle c r i := ownsPt_meetsCircle_of_covers hcov hx hi
  have hd : dist x (c i) ≤ r := ownsPt_dist_le_of_covers hcov (le_of_eq hx) hi
  exact ⟨i, ⟨hb, hi, hd⟩, fun i' hi' => ownsPt_unique hi'.2.1 hi⟩

/-- **Every point of `S¹` is owned and covered** (the "no bubble" reading: no point of the
circle is left uncovered or unowned). -/
theorem exists_owner_covering {c : Fin 11 → Point} {r : ℝ} (hcov : Covers c r) {x : Point}
    (hx : ‖x‖ = 1) : ∃ i : Fin 11, MeetsCircle c r i ∧ OwnsPt c i x ∧ dist x (c i) ≤ r :=
  let ⟨i, hi, _⟩ := unique_ownership_points hcov x hx
  ⟨i, hi⟩

end

end N11Formalization.DSHTopologyOwnership
