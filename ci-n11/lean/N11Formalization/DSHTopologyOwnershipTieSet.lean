/-
  DSHTopologyOwnershipTieSet.lean — DSH-TOPO-C2 (part D): the tie set of a site pair is
  contained in at most two `2π`-cosets, so ownership switches are discrete.

  ## Content (unconditional in `c`; no cover hypothesis)

  For two sites with DISTINCT centres, the equation `sqDist (c i) t = sqDist (c j) t` is
  `A cos t + B sin t = D` with `(A,B) ≠ 0`; writing `A cos t + B sin t = R cos (t - φ)` with
  `R = sqrt (A²+B²) > 0`, every solution lies in one of the two cosets
  `φ ± arccos (D/R) + 2πℤ`.  Hence each site pair contributes at most two residue classes
  modulo `2π`; combined with part C (ownership can only switch at a tie) the ownership
  switches are discrete.

  For COINCIDENT centres the tie set is all of `ℝ` (`tiePairSet_eq_univ_of_coincident`) — the
  explicit degenerate branch, consistent with part B's coincident-centre exclusion.

  No `sorry`, no custom axiom, no `native_decide`.
-/
import Mathlib
import N11Formalization.DSHTopologyOwnershipSwitches

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace N11Formalization.DSHTopologyOwnershipTieSet

open N11Formalization
open N11Formalization.DSHTopologyOwnership
open N11Formalization.DSHTopologyOwnershipSwitches

noncomputable section

/-! ## §10  The tie set of a site pair -/

/-- Points are determined by their two coordinates. -/
theorem eq_of_ofLp_eq {u v : Point} (h0 : u.ofLp 0 = v.ofLp 0) (h1 : u.ofLp 1 = v.ofLp 1) :
    u = v := by
  refine PiLp.ext fun k => ?_
  fin_cases k
  · exact h0
  · exact h1

/-- The chart angles at which sites `i` and `j` are equidistant from `circleMap t`. -/
def tiePairSet (c : Fin 11 → Point) (i j : Fin 11) : Set ℝ :=
  {t : ℝ | sqDist (c i) t = sqDist (c j) t}

/-- The squared-distance difference is an affine function of `(cos t, sin t)`. -/
theorem sqDist_sub_eq (c : Fin 11 → Point) (i j : Fin 11) (t : ℝ) :
    sqDist (c i) t - sqDist (c j) t =
      (‖c i‖ ^ 2 - ‖c j‖ ^ 2) - 2 * ((c i).ofLp 0 - (c j).ofLp 0) * Real.cos t
        - 2 * ((c i).ofLp 1 - (c j).ofLp 1) * Real.sin t := by
  unfold sqDist
  ring

/-- Coincident centres: every angle is a tie (the explicit degenerate branch). -/
theorem tiePairSet_eq_univ_of_coincident {c : Fin 11 → Point} {i j : Fin 11} (h : c i = c j) :
    tiePairSet c i j = Set.univ := by
  ext t
  simp [tiePairSet, h]

/-- **At most two cosets per site pair.**  If the two centres are distinct, then every angle at
which the two sites are equidistant lies in one of the two `2π`-cosets `φ ± δ + 2πℤ`. -/
theorem tiePairSet_subset_cosets {c : Fin 11 → Point} {i j : Fin 11} (hcent : c i ≠ c j) :
    ∃ φ δ : ℝ, tiePairSet c i j ⊆
      {t : ℝ | ∃ k : ℤ, t = 2 * (k : ℝ) * Real.pi + φ + δ ∨
        t = 2 * (k : ℝ) * Real.pi + φ - δ} := by
  set A : ℝ := (c i).ofLp 0 - (c j).ofLp 0 with hA
  set B : ℝ := (c i).ofLp 1 - (c j).ofLp 1 with hB
  set D : ℝ := (‖c i‖ ^ 2 - ‖c j‖ ^ 2) / 2 with hD
  have hsum : 0 < A ^ 2 + B ^ 2 := by
    rcases eq_or_ne A 0 with hA0 | hA0
    · rcases eq_or_ne B 0 with hB0 | hB0
      · exfalso
        refine hcent (eq_of_ofLp_eq ?_ ?_)
        · rw [hA] at hA0; linarith
        · rw [hB] at hB0; linarith
      · nlinarith [sq_pos_of_ne_zero hB0]
    · nlinarith [sq_pos_of_ne_zero hA0]
  set R : ℝ := Real.sqrt (A ^ 2 + B ^ 2) with hR
  have hRpos : 0 < R := by
    rw [hR]
    exact Real.sqrt_pos.mpr hsum
  set z : ℂ := ⟨A / R, B / R⟩ with hz
  have hznorm : ‖z‖ = 1 := by
    have h1 : Complex.normSq z = 1 := by
      have h2 : Complex.normSq z = (A / R) ^ 2 + (B / R) ^ 2 := by
        simp [Complex.normSq_apply, hz, sq]
      rw [h2, div_pow, div_pow, ← add_div, hR, Real.sq_sqrt hsum.le,
        div_self (ne_of_gt hsum)]
    have h3 : ‖z‖ ^ 2 = 1 := by rw [Complex.sq_norm, h1]
    nlinarith [norm_nonneg z]
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hznorm
    norm_num at hznorm
  set φ : ℝ := Complex.arg z with hφ
  have hcosφ : Real.cos φ = A / R := by
    have h := Complex.cos_arg hzne
    rw [hznorm, div_one] at h
    simpa [hφ, hz] using h
  have hsinφ : Real.sin φ = B / R := by
    have h := Complex.sin_arg z
    rw [hznorm, div_one] at h
    simpa [hφ, hz] using h
  have hRmul : ∀ x : ℝ, R * (x / R) = x := fun x => by
    rw [div_eq_mul_inv, ← mul_assoc, mul_comm R x, mul_assoc, mul_inv_cancel₀ (ne_of_gt hRpos),
      mul_one]
  refine ⟨φ, Real.arccos (D / R), ?_⟩
  intro t ht
  have ht' : sqDist (c i) t = sqDist (c j) t := ht
  have hD' : A * Real.cos t + B * Real.sin t = D := by
    have h0 : sqDist (c i) t - sqDist (c j) t = 0 := by linarith
    rw [sqDist_sub_eq] at h0
    rw [hA, hB, hD]
    linarith
  have hmain : R * Real.cos (t - φ) = D := by
    have hcs : Real.cos (t - φ) = (Real.cos t * A + Real.sin t * B) / R := by
      rw [Real.cos_sub, hcosφ, hsinφ]
      ring_nf
    rw [hcs, hRmul]
    linarith [hD']
  have hcosval : Real.cos (t - φ) = D / R := by
    rw [eq_div_iff (ne_of_gt hRpos)]
    linarith
  have hDR1 : -1 ≤ D / R := by
    rw [← hcosval]
    exact Real.neg_one_le_cos _
  have hDR2 : D / R ≤ 1 := by
    rw [← hcosval]
    exact Real.cos_le_one _
  have hcos_eq : Real.cos (t - φ) = Real.cos (Real.arccos (D / R)) := by
    rw [Real.cos_arccos hDR1 hDR2, hcosval]
  obtain ⟨k, hk | hk⟩ :=
    (Real.cos_eq_cos_iff (x := Real.arccos (D / R)) (y := t - φ)).mp hcos_eq.symm
  · exact ⟨k, Or.inl (by linarith)⟩
  · exact ⟨k, Or.inr (by linarith)⟩

/-! ## §11  At most two points per turn (the bisector count) -/

/-- Two points of the same `2π`-coset inside `[0, 2π)` coincide. -/
theorem coset_eq_of_mem_Ico {X a b : ℝ} {k l : ℤ}
    (ha : a = 2 * (k : ℝ) * Real.pi + X) (hb : b = 2 * (l : ℝ) * Real.pi + X)
    (hia : a ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) (hib : b ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) :
    a = b := by
  have h2π : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hdiff : (k : ℝ) - (l : ℝ) = (a - b) / (2 * Real.pi) := by
    rw [eq_div_iff (ne_of_gt h2π)]
    linarith
  have hb1 : -1 < (k : ℝ) - (l : ℝ) := by
    rw [hdiff, lt_div_iff₀ h2π]
    nlinarith [hia.1, hib.2]
  have hb2 : (k : ℝ) - (l : ℝ) < 1 := by
    rw [hdiff, div_lt_iff₀ h2π]
    nlinarith [hia.2, hib.1]
  have hkl : k = l := by
    have h1 : k - l < 1 := by
      have h1' : ((k - l : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; exact hb2
      exact_mod_cast h1'
    have h2 : -1 < k - l := by
      have h2' : ((-1 : ℤ) : ℝ) < ((k - l : ℤ) : ℝ) := by push_cast; exact hb1
      exact_mod_cast h2'
    omega
  subst hkl
  linarith

/-- **The bisector meets one turn in at most two points.**  For two sites with distinct centres,
among any three angles of `[0, 2π)` at which the two sites are equidistant, two coincide.  (The
bisector of `i,j` is a line, and a line meets the unit circle in at most two points.) -/
theorem tiePairSet_at_most_two {c : Fin 11 → Point} {i j : Fin 11} (hcent : c i ≠ c j)
    {t₁ t₂ t₃ : ℝ} (h₁ : t₁ ∈ tiePairSet c i j) (h₂ : t₂ ∈ tiePairSet c i j)
    (h₃ : t₃ ∈ tiePairSet c i j)
    (ha : t₁ ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) (hb : t₂ ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (hc : t₃ ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) :
    t₁ = t₂ ∨ t₁ = t₃ ∨ t₂ = t₃ := by
  obtain ⟨φ, δ, hsub⟩ := tiePairSet_subset_cosets hcent
  obtain ⟨k₁, hk₁⟩ := hsub h₁
  obtain ⟨k₂, hk₂⟩ := hsub h₂
  obtain ⟨k₃, hk₃⟩ := hsub h₃
  have hk₁' : t₁ = 2 * (k₁ : ℝ) * Real.pi + (φ + δ) ∨
      t₁ = 2 * (k₁ : ℝ) * Real.pi + (φ - δ) := by
    rcases hk₁ with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hk₂' : t₂ = 2 * (k₂ : ℝ) * Real.pi + (φ + δ) ∨
      t₂ = 2 * (k₂ : ℝ) * Real.pi + (φ - δ) := by
    rcases hk₂ with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hk₃' : t₃ = 2 * (k₃ : ℝ) * Real.pi + (φ + δ) ∨
      t₃ = 2 * (k₃ : ℝ) * Real.pi + (φ - δ) := by
    rcases hk₃ with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hk₁' with h₁' | h₁' <;> rcases hk₂' with h₂' | h₂' <;> rcases hk₃' with h₃' | h₃'
  · exact Or.inl (coset_eq_of_mem_Ico (X := φ + δ) h₁' h₂' ha hb)            -- A A A
  · exact Or.inl (coset_eq_of_mem_Ico (X := φ + δ) h₁' h₂' ha hb)            -- A A B
  · exact Or.inr (Or.inl (coset_eq_of_mem_Ico (X := φ + δ) h₁' h₃' ha hc))   -- A B A
  · exact Or.inr (Or.inr (coset_eq_of_mem_Ico (X := φ - δ) h₂' h₃' hb hc))   -- A B B
  · exact Or.inr (Or.inr (coset_eq_of_mem_Ico (X := φ + δ) h₂' h₃' hb hc))   -- B A A
  · exact Or.inr (Or.inl (coset_eq_of_mem_Ico (X := φ - δ) h₁' h₃' ha hc))   -- B A B
  · exact Or.inl (coset_eq_of_mem_Ico (X := φ - δ) h₁' h₂' ha hb)            -- B B A
  · exact Or.inl (coset_eq_of_mem_Ico (X := φ - δ) h₁' h₂' ha hb)            -- B B B

/-! ## §12  Verbatim types and trusted base (evidence pack) -/

#check @N11Formalization.DSHTopologyOwnershipTieSet.eq_of_ofLp_eq
#check @N11Formalization.DSHTopologyOwnershipTieSet.tiePairSet
#check @N11Formalization.DSHTopologyOwnershipTieSet.sqDist_sub_eq
#check @N11Formalization.DSHTopologyOwnershipTieSet.tiePairSet_eq_univ_of_coincident
#check @N11Formalization.DSHTopologyOwnershipTieSet.tiePairSet_subset_cosets
#check @N11Formalization.DSHTopologyOwnershipTieSet.coset_eq_of_mem_Ico
#check @N11Formalization.DSHTopologyOwnershipTieSet.tiePairSet_at_most_two

#print axioms N11Formalization.DSHTopologyOwnershipTieSet.eq_of_ofLp_eq
#print axioms N11Formalization.DSHTopologyOwnershipTieSet.sqDist_sub_eq
#print axioms N11Formalization.DSHTopologyOwnershipTieSet.tiePairSet_eq_univ_of_coincident
#print axioms N11Formalization.DSHTopologyOwnershipTieSet.tiePairSet_subset_cosets
#print axioms N11Formalization.DSHTopologyOwnershipTieSet.coset_eq_of_mem_Ico
#print axioms N11Formalization.DSHTopologyOwnershipTieSet.tiePairSet_at_most_two

end

end N11Formalization.DSHTopologyOwnershipTieSet