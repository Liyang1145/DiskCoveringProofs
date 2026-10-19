import Mathlib

/-!
# ResumeGlobal: source-correct width domain (Fin 9, Σ = 1) and the Fin 8 chart.
Source: nine widths Δ_i = L − D·y_i, y ≥ 0, Σ_{i<9} y_i = 1 (so ΣΔ = 9L − D = 2π).
The rooted `C921Sem.InSimplex` (Fin 8, Σ = 1) is 7-dimensional: WRONG domain.
Correct 8-dim chart: Fin 8, y ≥ 0, Σ ≤ 1, with y_8 := 1 − Σ.
-/

namespace N11Formalization.ResumeGlobal
open Finset

def InSimplex9 (y : Fin 9 → ℝ) : Prop := (∀ q, 0 ≤ y q) ∧ ∑ q, y q = 1

def InChart8 (z : Fin 8 → ℝ) : Prop := (∀ q, 0 ≤ z q) ∧ ∑ q, z q ≤ 1

/-- Extend a chart point by the last coordinate `1 − Σ`. -/
noncomputable def extend (z : Fin 8 → ℝ) : Fin 9 → ℝ :=
  Fin.lastCases (1 - ∑ q, z q) z

theorem extend_mem {z : Fin 8 → ℝ} (h : InChart8 z) : InSimplex9 (extend z) := by
  refine ⟨fun q => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) q
    · rw [extend, Fin.lastCases_last]; linarith [h.2]
    · rw [extend, Fin.lastCases_castSucc]; exact h.1 i
  · rw [Fin.sum_univ_castSucc]
    simp only [extend, Fin.lastCases_last, Fin.lastCases_castSucc]
    ring

theorem init_mem {y : Fin 9 → ℝ} (h : InSimplex9 y) : InChart8 (fun i => y i.castSucc) := by
  refine ⟨fun q => h.1 _, ?_⟩
  have := h.2; rw [Fin.sum_univ_castSucc] at this; linarith [h.1 (Fin.last 8)]

theorem extend_init {y : Fin 9 → ℝ} (h : InSimplex9 y) :
    extend (fun i => y i.castSucc) = y := by
  funext q
  refine Fin.lastCases ?_ (fun i => ?_) q
  · have := h.2; rw [Fin.sum_univ_castSucc] at this
    rw [extend, Fin.lastCases_last]; linarith
  · rw [extend, Fin.lastCases_castSucc]

/-- Witness: the uniform source point 1/9 is legal. -/
theorem uniform_mem : InSimplex9 (fun _ => (1 : ℝ) / 9) :=
  ⟨fun _ => by norm_num, by simp⟩

/-- Discriminating control: the uniform point's Fin 8 restriction has Σ = 8/9 ≠ 1,
so it is NOT in the rooted `Fin 8, Σ = 1` domain. -/
theorem uniform_restrict_sum : ∑ _i : Fin 8, (1 : ℝ) / 9 = 8 / 9 := by simp; norm_num

end N11Formalization.ResumeGlobal

#print axioms N11Formalization.ResumeGlobal.extend_init
#print axioms N11Formalization.ResumeGlobal.uniform_mem
