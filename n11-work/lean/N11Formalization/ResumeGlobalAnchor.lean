import Mathlib

/-!
# ResumeGlobal: canonical anchor-angle map on the source Fin 9 width domain.
Source (FIXED-SWITCH-SOC-REDUCTION §4, EXACT-ORACLE-INDEX-MAP):
  θ_i = i·L − D·Σ_{j<i} y_j,  L = 2·asin(19/50),  D = 9L − 2π,
  widths Δ_i = θ_{i+1} − θ_i = L − D·y_i.
Mathlib-only (no import of the unbuilt ResumeGlobalDomain); simplex premises are explicit.
Generic in L, D except where D = 9L − 2π is stated.
-/

namespace N11Formalization.ResumeGlobal
open Finset

/-- Anchor angle θ_i for i = 0..9 (θ_9 = θ_0 + 2π when D = 9L − 2π). -/
def anchorAngle (L D : ℝ) (y : Fin 9 → ℝ) (i : ℕ) : ℝ :=
  (i : ℝ) * L - D * ∑ j ∈ (Finset.univ.filter fun j : Fin 9 => (j : ℕ) < i), y j

/-- Width of the owned interval i (i : Fin 9). -/
def width (L D : ℝ) (y : Fin 9 → ℝ) (i : Fin 9) : ℝ := L - D * y i

theorem filter_succ (i : Fin 9) :
    (Finset.univ.filter fun j : Fin 9 => (j : ℕ) < (i : ℕ) + 1)
      = insert i (Finset.univ.filter fun j : Fin 9 => (j : ℕ) < i) := by
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h; rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext h)
  · rintro (rfl | h) <;> omega

/-- Consecutive anchors differ by the width: θ_{i+1} − θ_i = L − D·y_i. -/
theorem anchor_succ_sub (L D : ℝ) (y : Fin 9 → ℝ) (i : Fin 9) :
    anchorAngle L D y ((i : ℕ) + 1) - anchorAngle L D y i = width L D y i := by
  unfold anchorAngle width
  rw [filter_succ, Finset.sum_insert (by simp)]
  push_cast; ring

theorem anchor_zero (L D : ℝ) (y : Fin 9 → ℝ) : anchorAngle L D y 0 = 0 := by
  simp [anchorAngle]

/-- Closure: θ_9 − θ_0 = 9L − D·Σy; with Σy = 1 and D = 9L − 2π this is 2π. -/
theorem anchor_nine (L D : ℝ) (y : Fin 9 → ℝ) (hy1 : ∑ q, y q = 1)
    (hD : D = 9 * L - 2 * Real.pi) : anchorAngle L D y 9 = 2 * Real.pi := by
  unfold anchorAngle
  have : (Finset.univ.filter fun j : Fin 9 => (j : ℕ) < 9) = Finset.univ := by
    ext j; simp
  rw [this, hy1, hD]; push_cast; ring

/-- Widths sum to 2π on the source domain. -/
theorem width_sum (L D : ℝ) (y : Fin 9 → ℝ) (hy1 : ∑ q, y q = 1)
    (hD : D = 9 * L - 2 * Real.pi) : ∑ i, width L D y i = 2 * Real.pi := by
  unfold width
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hy1, hD]; simp

/-- Width box: for y in the closed 9-simplex and D ≥ 0, m = L − D ≤ Δ_i ≤ L
(m = 2π − 8L when D = 9L − 2π). This is exactly the source polytope P. -/
theorem width_mem_box (L D : ℝ) (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hy1 : ∑ q, y q = 1) (hD0 : 0 ≤ D) (i : Fin 9) :
    L - D ≤ width L D y i ∧ width L D y i ≤ L := by
  have hle : y i ≤ 1 := by
    rw [← hy1]
    exact Finset.single_le_sum (fun q _ => hy0 q) (Finset.mem_univ i)
  unfold width
  constructor <;> nlinarith [hy0 i]

/-- Converse (surjectivity onto P): every width list Δ ∈ [L−D, L]^9 with ΣΔ = 2π,
D = 9L − 2π > 0, comes from a simplex point y_i = (L − Δ_i)/D. No hidden symmetry. -/
theorem width_surj (L D : ℝ) (Δ : Fin 9 → ℝ) (hDpos : 0 < D)
    (hD : D = 9 * L - 2 * Real.pi) (hΔ : ∀ i, Δ i ≤ L) (hsum : ∑ i, Δ i = 2 * Real.pi) :
    ∃ y : Fin 9 → ℝ, (∀ q, 0 ≤ y q) ∧ ∑ q, y q = 1 ∧ ∀ i, width L D y i = Δ i := by
  refine ⟨fun i => (L - Δ i) / D, fun q => div_nonneg (by linarith [hΔ q]) hDpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum]; simp
    rw [div_eq_one_iff_eq hDpos.ne', hD]
  · intro i; unfold width; field_simp; ring

end N11Formalization.ResumeGlobal

#print axioms N11Formalization.ResumeGlobal.anchor_succ_sub
#print axioms N11Formalization.ResumeGlobal.anchor_nine
#print axioms N11Formalization.ResumeGlobal.width_sum
#print axioms N11Formalization.ResumeGlobal.width_mem_box
#print axioms N11Formalization.ResumeGlobal.width_surj
