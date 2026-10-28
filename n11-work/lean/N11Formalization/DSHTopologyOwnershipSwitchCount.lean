/-
  DSHTopologyOwnershipSwitchCount.lean — DSH-TOPO-C2 (part E): switch points of the ownership
  partition are two-site nearest ties, and the tie set is finite modulo `2π`.

  ## Content (unconditional in `c`; no cover hypothesis)

  * `LocallyConstAt c t` : the owner is constant on a two-sided neighbourhood of `t`.
  * `SwitchAt c t` : `t` is a switch point, i.e. NOT a point of local constancy of the owner.
  * `switchAt_imp_tieMin` : **every switch point is a genuine two-site nearest tie**
    (contrapositive of part C's `ownerAngle_local_const`).  So the ownership switches form a
    subset of the tie set — there is no switch that is not a two-site nearest tie.
  * `tiePairSet_subset_cosets` (part D) + `exists_tieMin_cosets` : for pairwise distinct
    centres the whole tie set is contained in a finite union of `2π`-cosets, indexed by the
    `C(11,2) = 55` site pairs, two cosets each — at most `110` residue classes modulo `2π`.
    Hence the switch set is DISCRETE: no accumulation point modulo `2π`.

  ## Explicit gap (not proved here)

  The COUNT "exactly nine distinct two-site switches" is NOT proved in this file.  What is
  missing is the circle-component lemma, stated precisely:

    for a finite `T ⊆ ℝ` (viewed on the circle `S¹ ≅ AddCircle (2π)`), the complement of `T`
    has exactly `T.card` connected components, and a locally constant function on the circle is
    constant on each component.

  Combined with `switchAt_imp_tieMin`, part C's interval constancy and part B's
  `ownership_ledger_actual` (at the explicit premise `Fintype.card (BoundaryIdx c r) = 9`:
  nine NONEMPTY owned sets), that lemma gives: the number of switch points is at least nine,
  i.e. nine distinct two-site switches.  The missing lemma is a topological statement about
  `AddCircle`/`S¹` minus a finite set, independent of the n=11 geometry; it is registered as a
  gap claim, not smuggled in.

  No `sorry`, no custom axiom, no `native_decide`.
-/
import Mathlib
import N11Formalization.DSHTopologyOwnershipSwitches
import N11Formalization.DSHTopologyOwnershipTieSet

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace N11Formalization.DSHTopologyOwnershipSwitchCount

open N11Formalization
open N11Formalization.DSHTopologyOwnership
open N11Formalization.DSHTopologyOwnershipSwitches
open N11Formalization.DSHTopologyOwnershipTieSet

noncomputable section

/-! ## §12  Switch points -/

/-- The owner is constant on a two-sided neighbourhood of `t`. -/
def LocallyConstAt (c : Fin 11 → Point) (t : ℝ) : Prop :=
  ∃ ε > 0, ∀ u v : ℝ, t - ε < u → u < t → t < v → v < t + ε →
    ownerAngle c u = ownerAngle c v

/-- `t` is a **switch point** of the ownership partition: the owner is not locally constant
there. -/
def SwitchAt (c : Fin 11 → Point) (t : ℝ) : Prop := ¬ LocallyConstAt c t

/-- Every non-tie angle is a point of local constancy of the owner. -/
theorem locallyConstAt_of_not_tieMin {c : Fin 11 → Point} {t : ℝ} (ht : ¬ TieMin c t) :
    LocallyConstAt c t := by
  obtain ⟨ε, hε0, hε⟩ := ownerAngle_local_const (c := c) (t := t) ht
  refine ⟨ε, hε0, fun u v hu1 hu2 hv1 hv2 => ?_⟩
  have hu : |u - t| < ε := by
    rw [abs_lt]; exact ⟨by linarith, by linarith⟩
  have hv : |v - t| < ε := by
    rw [abs_lt]; exact ⟨by linarith, by linarith⟩
  rw [hε u hu, hε v hv]

/-- **Every ownership switch is a two-site nearest tie.** -/
theorem switchAt_imp_tieMin {c : Fin 11 → Point} {t : ℝ} (h : SwitchAt c t) : TieMin c t := by
  by_contra ht
  exact h (locallyConstAt_of_not_tieMin ht)

/-- Set form: the switch set is contained in the genuine tie set. -/
theorem switchSet_subset_tieSet (c : Fin 11 → Point) :
    {t : ℝ | SwitchAt c t} ⊆ {t : ℝ | TieMin c t} :=
  fun _ h => switchAt_imp_tieMin h

/-! ## §13  Finiteness of the tie set modulo `2π` -/

/-- **The whole tie set lies in a finite union of `2π`-cosets** (two per site pair, hence at
most `110` residue classes).  Requires pairwise distinct centres; the coincident-centre
degenerate branch is `tiePairSet_eq_univ_of_coincident` (all angles are ties). -/
theorem exists_tieMin_cosets (c : Fin 11 → Point)
    (hcent : ∀ i j : Fin 11, i ≠ j → c i ≠ c j) :
    ∃ Φ : (Fin 11 × Fin 11) → ℝ × ℝ,
      ∀ t : ℝ, TieMin c t → ∃ p : Fin 11 × Fin 11, p.1 ≠ p.2 ∧ ∃ k : ℤ,
        t = 2 * (k : ℝ) * Real.pi + (Φ p).1 + (Φ p).2 ∨
        t = 2 * (k : ℝ) * Real.pi + (Φ p).1 - (Φ p).2 := by
  classical
  have hpair : ∀ p : Fin 11 × Fin 11, p.1 ≠ p.2 → ∃ φ δ : ℝ,
      tiePairSet c p.1 p.2 ⊆
        {t : ℝ | ∃ k : ℤ, t = 2 * (k : ℝ) * Real.pi + φ + δ ∨
          t = 2 * (k : ℝ) * Real.pi + φ - δ} :=
    fun p hp => tiePairSet_subset_cosets (hcent p.1 p.2 hp)
  set Φ : (Fin 11 × Fin 11) → ℝ × ℝ := fun p =>
    if hp : p.1 ≠ p.2 then
      (Classical.choose (hpair p hp),
        Classical.choose (Classical.choose_spec (hpair p hp)))
    else (0, 0) with hΦ
  refine ⟨Φ, ?_⟩
  intro t ht
  obtain ⟨i, j, hij, heq, -⟩ := ht
  have hp : (i, j).1 ≠ (i, j).2 := hij
  have hval : Φ (i, j) = (Classical.choose (hpair (i, j) hp),
      Classical.choose (Classical.choose_spec (hpair (i, j) hp))) := by
    rw [hΦ]
    exact dif_pos hp
  refine ⟨(i, j), hij, ?_⟩
  have htie : t ∈ tiePairSet c i j := heq
  simpa [hval] using
    (Classical.choose_spec (Classical.choose_spec (hpair (i, j) hp))) htie

/-! ## §14  Verbatim types and trusted base (evidence pack) -/

/-! ## §14  `2π`-periodicity: the switch structure lives on the circle

These are the ingredients that let the COUNT be settled on the interval `[0, 2π]` — identifying
the owner at `0` with the owner at `2π` — instead of needing a connectivity theorem for
`S¹ ≅ AddCircle (2π)`. -/

theorem sqDist_add_two_pi (c : Point) (t : ℝ) : sqDist c (t + 2 * Real.pi) = sqDist c t := by
  unfold sqDist
  rw [show t + 2 * Real.pi = t + (1 : ℤ) * (2 * Real.pi) by norm_num,
    Real.cos_add_int_mul_two_pi t 1, Real.sin_add_int_mul_two_pi t 1]

theorem owns_add_two_pi {c : Fin 11 → Point} {i : Fin 11} {t : ℝ} (h : Owns c i t) :
    Owns c i (t + 2 * Real.pi) := by
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · rw [sqDist_add_two_pi, sqDist_add_two_pi]; exact h.1 j
  · rw [sqDist_add_two_pi, sqDist_add_two_pi]; exact h.2 j hj

/-- **The owner is `2π`-periodic**: the chart parameter descends to the circle. -/
theorem ownerAngle_add_two_pi (c : Fin 11 → Point) (t : ℝ) :
    ownerAngle c (t + 2 * Real.pi) = ownerAngle c t :=
  ownerAngle_eq_of_owns (owns_add_two_pi (owns_ownerAngle c t))

/-- Switch points are `2π`-periodic. -/
theorem switchAt_add_two_pi {c : Fin 11 → Point} {t : ℝ} :
    SwitchAt c (t + 2 * Real.pi) ↔ SwitchAt c t := by
  have hlc : LocallyConstAt c (t + 2 * Real.pi) ↔ LocallyConstAt c t := by
    constructor
    · -- from constancy around `t + 2π`, derive it around `t`: shift the test points up
      rintro ⟨ε, hε0, hε⟩
      refine ⟨ε, hε0, fun u v hu1 hu2 hv1 hv2 => ?_⟩
      have h1 : ownerAngle c (u + 2 * Real.pi) = ownerAngle c (v + 2 * Real.pi) :=
        hε (u + 2 * Real.pi) (v + 2 * Real.pi)
          (by linarith) (by linarith) (by linarith) (by linarith)
      rw [ownerAngle_add_two_pi, ownerAngle_add_two_pi] at h1
      exact h1
    · -- from constancy around `t`, derive it around `t + 2π`: shift the test points down
      rintro ⟨ε, hε0, hε⟩
      refine ⟨ε, hε0, fun u v hu1 hu2 hv1 hv2 => ?_⟩
      have h1 : ownerAngle c (u - 2 * Real.pi) = ownerAngle c (v - 2 * Real.pi) :=
        hε (u - 2 * Real.pi) (v - 2 * Real.pi)
          (by linarith) (by linarith) (by linarith) (by linarith)
      rw [← ownerAngle_add_two_pi c (u - 2 * Real.pi), sub_add_cancel,
        ← ownerAngle_add_two_pi c (v - 2 * Real.pi), sub_add_cancel] at h1
      exact h1
  exact not_congr hlc

/-! ## §15  Verbatim types and trusted base (evidence pack) -/

#check @N11Formalization.DSHTopologyOwnershipSwitchCount.LocallyConstAt
#check @N11Formalization.DSHTopologyOwnershipSwitchCount.SwitchAt
#check @N11Formalization.DSHTopologyOwnershipSwitchCount.locallyConstAt_of_not_tieMin
#check @N11Formalization.DSHTopologyOwnershipSwitchCount.switchAt_imp_tieMin
#check @N11Formalization.DSHTopologyOwnershipSwitchCount.switchSet_subset_tieSet
#check @N11Formalization.DSHTopologyOwnershipSwitchCount.exists_tieMin_cosets
#check @N11Formalization.DSHTopologyOwnershipSwitchCount.sqDist_add_two_pi
#check @N11Formalization.DSHTopologyOwnershipSwitchCount.owns_add_two_pi
#check @N11Formalization.DSHTopologyOwnershipSwitchCount.ownerAngle_add_two_pi
#check @N11Formalization.DSHTopologyOwnershipSwitchCount.switchAt_add_two_pi

#print axioms N11Formalization.DSHTopologyOwnershipSwitchCount.locallyConstAt_of_not_tieMin
#print axioms N11Formalization.DSHTopologyOwnershipSwitchCount.switchAt_imp_tieMin
#print axioms N11Formalization.DSHTopologyOwnershipSwitchCount.switchSet_subset_tieSet
#print axioms N11Formalization.DSHTopologyOwnershipSwitchCount.exists_tieMin_cosets
#print axioms N11Formalization.DSHTopologyOwnershipSwitchCount.sqDist_add_two_pi
#print axioms N11Formalization.DSHTopologyOwnershipSwitchCount.owns_add_two_pi
#print axioms N11Formalization.DSHTopologyOwnershipSwitchCount.ownerAngle_add_two_pi
#print axioms N11Formalization.DSHTopologyOwnershipSwitchCount.switchAt_add_two_pi

end

end N11Formalization.DSHTopologyOwnershipSwitchCount