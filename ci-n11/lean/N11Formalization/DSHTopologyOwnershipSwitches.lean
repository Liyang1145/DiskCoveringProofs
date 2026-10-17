/-
  DSHTopologyOwnershipSwitches.lean — DSH-TOPO-C2 (part C): the switch structure of the
  ownership partition — every change of owner is a two-site nearest tie.

  ## Content (unconditional in `c`; no cover hypothesis needed)

  `TieAt c t`: two distinct sites are equidistant from `circleMap t`.
  `TieMin c t`: two distinct sites are equidistant AND at the minimum distance — a genuine
  ownership tie.

  * `continuous_sqDist`; `TieAt`, `TieMin`, `tieMin_imp_tieAt`.
  * `owns_strict_of_not_tieMin`: at a non-tie angle the owner is the UNIQUE strict minimiser.
  * `owns_of_no_tieMin_near`: the owner `i` owns a whole `ε`-neighbourhood of every non-tie
    angle it owns (ε-δ from continuity of the finitely many squared-distance gaps).
  * `ownerAngle` (the owning site as a function), `ownerAngle_eq_of_owns`.
  * `ownerAngle_local_const`, `ownerAngle_locallyConstant_tiefree`: the owner is constant on a
    neighbourhood of every non-tie angle, and locally constant on the tie-free part of the
    chart.
  * `ownerAngle_eq_of_no_tieMin_Icc`: on an interval containing no tie the owner is constant.
  * `exists_tieMin_between`: **if two different sites own two angles `t ≤ s`, then `[t, s]`
    contains a genuine two-site nearest tie.**  So ownership switches happen exactly at ties.

  No `sorry`, no custom axiom, no `native_decide`.
-/
import Mathlib
import N11Formalization.DSHTopologyOwnership

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace N11Formalization.DSHTopologyOwnershipSwitches

open MeasureTheory
open N11Formalization
open N11Formalization.DSHTopologyOwnership

noncomputable section

/-! ## §7  Ties -/

theorem continuous_sqDist (c : Point) : Continuous (sqDist c) := by
  have h : Continuous fun t : ℝ =>
      (1 + ‖c‖ ^ 2) - 2 * (Real.cos t * c.ofLp 0 + Real.sin t * c.ofLp 1) :=
    continuous_const.sub (continuous_const.mul
      ((Real.continuous_cos.mul continuous_const).add
        (Real.continuous_sin.mul continuous_const)))
  exact h

/-- **Weak tie**: two distinct sites are equidistant from `circleMap t`. -/
def TieAt (c : Fin 11 → Point) (t : ℝ) : Prop :=
  ∃ i j : Fin 11, i ≠ j ∧ sqDist (c i) t = sqDist (c j) t

/-- **Ownership tie**: two distinct sites are equidistant AND at the minimal distance.  This is
the tie at which a change of owner can occur. -/
def TieMin (c : Fin 11 → Point) (t : ℝ) : Prop :=
  ∃ i j : Fin 11, i ≠ j ∧ sqDist (c i) t = sqDist (c j) t ∧
    ∀ k : Fin 11, sqDist (c i) t ≤ sqDist (c k) t

theorem tieMin_imp_tieAt {c : Fin 11 → Point} {t : ℝ} (h : TieMin c t) : TieAt c t :=
  let ⟨i, j, hij, heq, _⟩ := h
  ⟨i, j, hij, heq⟩

/-- At a non-tie angle the owner is the unique STRICT minimiser. -/
theorem owns_strict_of_not_tieMin {c : Fin 11 → Point} {i : Fin 11} {t : ℝ}
    (hi : Owns c i t) (ht : ¬ TieMin c t) :
    ∀ j : Fin 11, j ≠ i → sqDist (c i) t < sqDist (c j) t := by
  intro j hj
  rcases lt_trichotomy (sqDist (c i) t) (sqDist (c j) t) with h | h | h
  · exact h
  · exact absurd ⟨i, j, Ne.symm hj, h, fun k => hi.1 k⟩ ht
  · exact absurd (lt_of_lt_of_le h (hi.1 j)) (lt_irrefl _)

/-- **The owner is locally constant away from ties.**  If site `i` owns `t` and `t` is not a
tie, then `i` owns every angle in a neighbourhood of `t`. -/
theorem owns_of_no_tieMin_near {c : Fin 11 → Point} {t : ℝ} {i : Fin 11} (hi : Owns c i t)
    (ht : ¬ TieMin c t) : ∃ ε > 0, ∀ s : ℝ, |s - t| < ε → Owns c i s := by
  classical
  have hnear : ∀ j : Fin 11, j ≠ i → ∃ δ > 0, ∀ s : ℝ, |s - t| < δ →
      0 < sqDist (c j) s - sqDist (c i) s := by
    intro j hj
    have hgap : 0 < sqDist (c j) t - sqDist (c i) t :=
      sub_pos.mpr (owns_strict_of_not_tieMin hi ht j hj)
    have hcont : ContinuousAt (fun s : ℝ => sqDist (c j) s - sqDist (c i) s) t :=
      ((continuous_sqDist (c j)).sub (continuous_sqDist (c i))).continuousAt
    obtain ⟨δ, hδ0, hδ⟩ :=
      (Metric.continuousAt_iff.mp hcont) (sqDist (c j) t - sqDist (c i) t) hgap
    refine ⟨δ, hδ0, fun s hs => ?_⟩
    have hs' : dist s t < δ := by rwa [Real.dist_eq]
    have h2 := hδ hs'
    rw [Real.dist_eq] at h2
    have h3 := (abs_lt.mp h2).1
    linarith
  choose δ hδ using hnear
  set g : Fin 11 → ℝ := fun j => if h : j = i then 1 else δ j h with hg
  have hne : (Finset.univ : Finset (Fin 11)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  set ε : ℝ := (Finset.univ : Finset (Fin 11)).inf' hne g with hεdef
  have hεle : ∀ j : Fin 11, ε ≤ g j := by
    intro j
    rw [hεdef]
    exact Finset.inf'_le g (Finset.mem_univ j)
  have hεpos : 0 < ε := by
    rw [hεdef]
    refine (Finset.lt_inf'_iff hne).mpr ?_
    intro j _
    rw [hg]
    simp only
    by_cases hj : j = i
    · simp [dif_pos hj]
    · rw [dif_neg hj]; exact (hδ j hj).1
  refine ⟨ε, hεpos, fun s hs => ?_⟩
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · rw [hji]
    · have h1 : |s - t| < g j := lt_of_lt_of_le hs (hεle j)
      rw [hg] at h1; simp only at h1; rw [dif_neg hji] at h1
      have h2 := (hδ j hji).2 s h1
      linarith
  · intro j hj
    have hji : j ≠ i := fun hh => absurd (hh ▸ hj) (lt_irrefl i)
    have h1 : |s - t| < g j := lt_of_lt_of_le hs (hεle j)
    rw [hg] at h1; simp only at h1; rw [dif_neg hji] at h1
    have h2 := (hδ j hji).2 s h1
    linarith

/-! ## §8  The owner as a function, and its constancy off the ties -/

/-- The owning site at an angle (well defined by `owns_exists` + `owns_unique`). -/
noncomputable def ownerAngle (c : Fin 11 → Point) (t : ℝ) : Fin 11 :=
  Classical.choose (owns_exists c t)

theorem owns_ownerAngle (c : Fin 11 → Point) (t : ℝ) : Owns c (ownerAngle c t) t :=
  Classical.choose_spec (owns_exists c t)

theorem ownerAngle_eq_of_owns {c : Fin 11 → Point} {t : ℝ} {i : Fin 11} (h : Owns c i t) :
    ownerAngle c t = i :=
  owns_unique (owns_ownerAngle c t) h

/-- The owner is constant on a neighbourhood of every non-tie angle. -/
theorem ownerAngle_local_const {c : Fin 11 → Point} {t : ℝ} (ht : ¬ TieMin c t) :
    ∃ ε > 0, ∀ s : ℝ, |s - t| < ε → ownerAngle c s = ownerAngle c t := by
  obtain ⟨ε, hε0, hε⟩ := owns_of_no_tieMin_near (owns_ownerAngle c t) ht
  exact ⟨ε, hε0, fun s hs => ownerAngle_eq_of_owns (hε s hs)⟩

/-- The owner function is locally constant on the tie-free part of the chart. -/
theorem ownerAngle_locallyConstant_tiefree (c : Fin 11 → Point) :
    IsLocallyConstant (fun x : {t : ℝ // ¬ TieMin c t} => ownerAngle c x.1) := by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨ε, hε0, hε⟩ := ownerAngle_local_const (c := c) (t := x.1) x.2
  change ∀ᶠ y in nhds x, (fun x : {t : ℝ // ¬ TieMin c t} => ownerAngle c x.1) y ∈ s
  rw [Metric.eventually_nhds_iff]
  refine ⟨ε, hε0, fun y hy => ?_⟩
  have h1 : |y.1 - x.1| < ε := by
    have h2 : dist y.1 x.1 < ε := by simpa only [Subtype.dist_eq] using hy
    rwa [Real.dist_eq] at h2
  show ownerAngle c y.1 ∈ s
  rw [hε y.1 h1]
  exact hx

/-- **Owner constant on a tie-free interval.**  If no angle of `[a,b]` is a tie, then the owner
is constant on `[a,b]`.  (Open-cover argument: the owner's constancy balls on `[a,b]` split into
the two open disjoint families "owner ≠ owner a" and "owner = owner a", and `[a,b]` is
preconnected, so it must lie in one family; the second, since it contains `a`.) -/
theorem ownerAngle_eq_of_no_tieMin_Icc {c : Fin 11 → Point} {a b t : ℝ}
    (hno : ∀ u ∈ Set.Icc a b, ¬ TieMin c u) (ha : a ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc a b) : ownerAngle c t = ownerAngle c a := by
  classical
  have hex : ∀ x ∈ Set.Icc a b, ∃ ε > 0, ∀ y : ℝ, |y - x| < ε →
      ownerAngle c y = ownerAngle c x :=
    fun x hx => ownerAngle_local_const (c := c) (t := x) (hno x hx)
  choose ε hε using hex
  set ε' : ℝ → ℝ := fun x => if h : x ∈ Set.Icc a b then ε x h else 1 with hε'def
  have hε'pos : ∀ x ∈ Set.Icc a b, 0 < ε' x := by
    intro x hx
    rw [hε'def]; simp only; rw [dif_pos hx]
    exact (hε x hx).1
  have hε'eq : ∀ x ∈ Set.Icc a b, ∀ y : ℝ, |y - x| < ε' x →
      ownerAngle c y = ownerAngle c x := by
    intro x hx y hy
    rw [hε'def] at hy; simp only at hy; rw [dif_pos hx] at hy
    exact (hε x hx).2 y hy
  set U : Set ℝ := ⋃ x : ℝ,
    ⋃ (_ : x ∈ Set.Icc a b ∧ ownerAngle c x ≠ ownerAngle c a), Metric.ball x (ε' x)
    with hUdef
  set V : Set ℝ := ⋃ x : ℝ,
    ⋃ (_ : x ∈ Set.Icc a b ∧ ownerAngle c x = ownerAngle c a), Metric.ball x (ε' x)
    with hVdef
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact isOpen_iUnion fun x => isOpen_iUnion fun _ => Metric.isOpen_ball
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact isOpen_iUnion fun x => isOpen_iUnion fun _ => Metric.isOpen_ball
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    rw [hUdef] at hzU
    rw [hVdef] at hzV
    obtain ⟨x, hxU⟩ := Set.mem_iUnion.mp hzU
    obtain ⟨hxP, hxz⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨y, hyV⟩ := Set.mem_iUnion.mp hzV
    obtain ⟨hyP, hyz⟩ := Set.mem_iUnion.mp hyV
    have h1 : ownerAngle c z = ownerAngle c x :=
      hε'eq x hxP.1 z (by
        have h := Metric.mem_ball.mp hxz
        rwa [Real.dist_eq] at h)
    have h2 : ownerAngle c z = ownerAngle c y :=
      hε'eq y hyP.1 z (by
        have h := Metric.mem_ball.mp hyz
        rwa [Real.dist_eq] at h)
    have h3 : ownerAngle c x = ownerAngle c a := by rw [← h1, h2, hyP.2]
    exact hxP.2 h3
  have hsub : Set.Icc a b ⊆ U ∪ V := by
    intro x hx
    have hxmem : x ∈ Metric.ball x (ε' x) := Metric.mem_ball_self (hε'pos x hx)
    by_cases hcase : ownerAngle c x = ownerAngle c a
    · refine Set.mem_union_right _ ?_
      rw [hVdef]
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨⟨hx, hcase⟩, hxmem⟩⟩
    · refine Set.mem_union_left _ ?_
      rw [hUdef]
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨⟨hx, hcase⟩, hxmem⟩⟩
  have haV : a ∈ V := by
    rw [hVdef]
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
      ⟨⟨ha, rfl⟩, Metric.mem_ball_self (hε'pos a ha)⟩⟩
  rcases (isPreconnected_Icc (a := a) (b := b)).subset_or_subset hUopen hVopen hdisj hsub with
    hsubU | hsubV
  · exact (Set.disjoint_left.mp hdisj (hsubU ha) haV).elim
  · obtain ⟨x, hxV⟩ := Set.mem_iUnion.mp (by rw [hVdef] at hsubV; exact hsubV ht)
    obtain ⟨hxP, hxt⟩ := Set.mem_iUnion.mp hxV
    rw [hε'eq x hxP.1 t (by
      have h := Metric.mem_ball.mp hxt
      rwa [Real.dist_eq] at h), hxP.2]

/-- **Switches occur only at two-site nearest ties.**  If two DIFFERENT sites own two angles
`t ≤ s`, then `[t, s]` contains a genuine ownership tie. -/
theorem exists_tieMin_between {c : Fin 11 → Point} {t s : ℝ} {i i' : Fin 11}
    (hi : Owns c i t) (hi' : Owns c i' s) (hne : i ≠ i') (hts : t ≤ s) :
    ∃ u ∈ Set.Icc t s, TieMin c u := by
  by_contra h
  have hno : ∀ u ∈ Set.Icc t s, ¬ TieMin c u := fun u hu htu => h ⟨u, hu, htu⟩
  have hconst : ownerAngle c s = ownerAngle c t :=
    ownerAngle_eq_of_no_tieMin_Icc (c := c) (a := t) (b := s) (t := s) hno
      ⟨le_rfl, hts⟩ ⟨hts, le_rfl⟩
  rw [ownerAngle_eq_of_owns hi', ownerAngle_eq_of_owns hi] at hconst
  exact hne hconst.symm

/-! ## §9  Verbatim types and trusted base (evidence pack) -/

#check @N11Formalization.DSHTopologyOwnershipSwitches.continuous_sqDist
#check @N11Formalization.DSHTopologyOwnershipSwitches.TieAt
#check @N11Formalization.DSHTopologyOwnershipSwitches.TieMin
#check @N11Formalization.DSHTopologyOwnershipSwitches.tieMin_imp_tieAt
#check @N11Formalization.DSHTopologyOwnershipSwitches.owns_strict_of_not_tieMin
#check @N11Formalization.DSHTopologyOwnershipSwitches.owns_of_no_tieMin_near
#check @N11Formalization.DSHTopologyOwnershipSwitches.ownerAngle
#check @N11Formalization.DSHTopologyOwnershipSwitches.ownerAngle_eq_of_owns
#check @N11Formalization.DSHTopologyOwnershipSwitches.ownerAngle_local_const
#check @N11Formalization.DSHTopologyOwnershipSwitches.ownerAngle_locallyConstant_tiefree
#check @N11Formalization.DSHTopologyOwnershipSwitches.ownerAngle_eq_of_no_tieMin_Icc
#check @N11Formalization.DSHTopologyOwnershipSwitches.exists_tieMin_between

#print axioms N11Formalization.DSHTopologyOwnershipSwitches.owns_strict_of_not_tieMin
#print axioms N11Formalization.DSHTopologyOwnershipSwitches.owns_of_no_tieMin_near
#print axioms N11Formalization.DSHTopologyOwnershipSwitches.ownerAngle_local_const
#print axioms N11Formalization.DSHTopologyOwnershipSwitches.ownerAngle_locallyConstant_tiefree
#print axioms N11Formalization.DSHTopologyOwnershipSwitches.ownerAngle_eq_of_no_tieMin_Icc
#print axioms N11Formalization.DSHTopologyOwnershipSwitches.exists_tieMin_between

end

end N11Formalization.DSHTopologyOwnershipSwitches