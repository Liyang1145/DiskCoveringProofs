/-
  c921-lpdual: M1 layer (d) -- LP weak duality over recorded data -- as a standalone lemma,
  plus the rest of M1 (layers (a)-(c)) folded into ONE named proposition `M1Affine`.
  Consumer: `C921Sem.LeafSemBound` / `leafOracleLower_of_floorData`.
-/
import N11Formalization.C921Sem

open Finset
open N11Formalization.LeafAgg N11Formalization.G3LeafChecker N11Formalization.G3ArcConstants
open N11Formalization.C921Sem

namespace C921LpDual

/-- LP weak duality step (pure algebra). With `λ ≥ 0`, `A y ≤ b` rowwise, `y` in the closed
simplex, and reduced costs `r_q = c_q + (Aᵀλ)_q ≥ rmin` for every `q`:
`c·y ≥ −λᵀb + rmin`. -/
theorem lp_weak_dual {m : ℕ} (A : Fin m → Fin 8 → ℚ) (bV : Fin m → ℚ)
    (lam : Fin m → ℚ) (c : Fin 8 → ℝ) (rmin : ℝ)
    (hlam : ∀ j, 0 ≤ lam j)
    (hr : ∀ q, rmin ≤ c q + ∑ j, (lam j : ℝ) * (A j q : ℝ))
    {y : Fin 8 → ℝ} (hy : InLeafDom A bV y) (hyS : InSimplex y) :
    -(∑ j, (lam j : ℝ) * (bV j : ℝ)) + rmin ≤ ∑ q, c q * y q := by
  obtain ⟨hy0, hy1⟩ := hyS
  -- Σ_q r_q y_q ≥ rmin
  have h1 : rmin ≤ ∑ q, (c q + ∑ j, (lam j : ℝ) * (A j q : ℝ)) * y q := by
    calc rmin = ∑ q, rmin * y q := by rw [← Finset.mul_sum, hy1, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hr q) (hy0 q)
  -- Σ_j λ_j (A_j·y) ≤ λᵀb
  have h2 : ∑ j, (lam j : ℝ) * (∑ q, (A j q : ℝ) * y q) ≤ ∑ j, (lam j : ℝ) * (bV j : ℝ) :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hy j) (by exact_mod_cast hlam j)
  have hsplit : ∑ q, (c q + ∑ j, (lam j : ℝ) * (A j q : ℝ)) * y q
      = ∑ q, c q * y q + ∑ j, (lam j : ℝ) * (∑ q, (A j q : ℝ) * y q) := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring
  linarith

/-- **M1 rest, named (layers (a)-(c), UNPAID).**  On the leaf domain ∩ simplex the oracle
energy dominates the affine field `f0 + c·y`, where `f0 = Σ_i (qc_i·L + qd_i)` is the
recorded line sum and `c` the recorded (β/γ-mixed) linear coefficient vector.  Content:
SOC weak duality `V2 ≥ E_α`, whole-cell cos-minorants, β/γ mixing. -/
def M1Affine (V2 : (Fin 8 → ℝ) → ℝ) {n m : ℕ} (L : ℝ) (qc qd : Fin n → ℚ)
    (c : Fin 8 → ℝ) (A : Fin m → Fin 8 → ℚ) (bV : Fin m → ℚ) : Prop :=
  ∀ y : Fin 8 → ℝ, InLeafDom A bV y → InSimplex y →
    (∑ i, ((qc i : ℝ) * L + (qd i : ℝ))) + ∑ q, c q * y q ≤ V2 y

/-- Bridge: `M1Affine` + dual-feasible multipliers + recorded `lamBR ≥ λᵀb`,
`rminR ≤ min_q r_q` ⇒ `LeafSemBound` (the exact premise of `leafOracleLower_of_*`). -/
theorem leafSemBound_of_dual
    {V2 : (Fin 8 → ℝ) → ℝ} {n m : ℕ} {L : ℝ} {qc qd : Fin n → ℚ} {lamBR rminR : ℚ}
    {A : Fin m → Fin 8 → ℚ} {bV : Fin m → ℚ} (c : Fin 8 → ℝ) (lam : Fin m → ℚ)
    (hM1 : M1Affine V2 L qc qd c A bV)
    (hlam : ∀ j, 0 ≤ lam j)
    (hr : ∀ q, (rminR : ℝ) ≤ c q + ∑ j, (lam j : ℝ) * (A j q : ℝ))
    (hlamB : ∑ j, lam j * bV j ≤ lamBR) :
    LeafSemBound V2 L qc qd lamBR rminR A bV := by
  intro y hy hyS
  have hlp := lp_weak_dual A bV lam c rminR hlam hr hy hyS
  have hB : (∑ j, (lam j : ℝ) * (bV j : ℝ)) ≤ (lamBR : ℝ) := by exact_mod_cast hlamB
  have hM := hM1 y hy hyS
  unfold energyLower
  linarith

/-- Fully instantiated consumer form (floor-data checker, rooted arc, `thresh²`). -/
theorem leafOracleLower_of_floorData_dual
    {V2 : (Fin 8 → ℝ) → ℝ} {n m : ℕ} {b : Fin n → Bool} {qc qd : Fin n → ℚ}
    {lamBq rminq : ℚ} {A : Fin m → Fin 8 → ℚ} {bV : Fin m → ℚ}
    (c : Fin 8 → ℝ) (lam : Fin m → ℚ)
    (h : leafCheck (fun i => ⌊qc i * (scaleD : ℚ)⌋) (fun i => ⌊qd i * (scaleD : ℚ)⌋) b
            arcLlo arcLhi scaleD ⌈lamBq * (scaleD : ℚ)⌉ ⌊rminq * (scaleD : ℚ)⌋ threshSq
          = true)
    (hM1 : M1Affine V2 (2 * Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ)) qc qd c A bV)
    (hlam : ∀ j, 0 ≤ lam j)
    (hr : ∀ q, (rminq : ℝ) ≤ c q + ∑ j, (lam j : ℝ) * (A j q : ℝ))
    (hlamB : ∑ j, lam j * bV j ≤ lamBq)
    {y : Fin 8 → ℝ} (hy : InLeafDom A bV y) (hyS : InSimplex y) :
    V2 y > ((thresh : ℚ) : ℝ) ^ 2 :=
  leafOracleLower_of_floorData h (leafSemBound_of_dual c lam hM1 hlam hr hlamB) hy hyS

end C921LpDual
