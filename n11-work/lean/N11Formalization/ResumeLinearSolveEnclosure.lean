import N11Formalization.ResumeLinearSolveInterval
import N11Formalization.ResumeIntervalMatrix

namespace N11Formalization.ResumeLinearSolveEnclosure
open RatInterval ResumeIntervalMatrix ResumeLinearSolve

/-- Computed outward box for C(b-Ay), with exact rational proposed centre y. -/
def residualBox {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (AB : Fin n → Fin n → RatInterval) (bB : Fin n → RatInterval)
    (y : Fin n → ℚ) (i : Fin n) : RatInterval :=
  isum (fun j => (ofRat (C i j)).mul
    ((bB j).sub (isum (fun k => (AB j k).mul (ofRat (y k))))))

theorem residual_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℚ) (AB : Fin n → Fin n → RatInterval)
    (bB : Fin n → RatInterval) (b : Fin n → ℝ) (y : Fin n → ℚ)
    (hA : ∀ i j, Mem (AB i j) (A i j)) (hb : ∀ i, Mem (bB i) (b i)) :
    ∀ i, Mem (residualBox C AB bB y i)
      ((C.map (Rat.cast : ℚ → ℝ)).mulVec (b-A.mulVec (fun k => (y k : ℝ))) i) := by
  intro i
  exact isum_mem _ _ (fun j => mul_mem (ofRat_mem _) (sub_mem (hb j)
    (isum_mem _ _ (fun k => mul_mem (hA j k) (ofRat_mem _)))))

theorem norm_le_of_box {n : ℕ} (B : Fin n → RatInterval) (v : Fin n → ℝ)
    (hB : ∀ i, Mem (B i) (v i)) (e : ℝ) (he : 0 ≤ e)
    (hmag : ∀ i, max |((B i).lo : ℝ)| |((B i).hi : ℝ)| ≤ e) : ‖v‖ ≤ e := by
  rw [pi_norm_le_iff_of_nonneg he]
  intro i
  rw [Real.norm_eq_abs]
  exact le_trans (abs_le_max_abs (hB i).1 (hB i).2) (hmag i)

/-- Entrywise enclosure of the EXACT solution. Both the residual norm and
contraction bound refer to the actual matrix, not to a floating midpoint. -/
theorem solution_coordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℚ) (AB : Fin n → Fin n → RatInterval)
    (bB : Fin n → RatInterval) (b x : Fin n → ℝ) (y : Fin n → ℚ)
    (q e : ℝ) (hq : q < 1) (he : 0 ≤ e)
    (hres : ∀ v, ‖v-(C.map (Rat.cast : ℚ → ℝ)).mulVec (A.mulVec v)‖ ≤ q*‖v‖)
    (hA : ∀ i j, Mem (AB i j) (A i j)) (hb : ∀ i, Mem (bB i) (b i))
    (hm : ∀ i, max |((residualBox C AB bB y i).lo : ℝ)|
      |((residualBox C AB bB y i).hi : ℝ)| ≤ e)
    (hx : A.mulVec x=b) (i : Fin n) :
    (y i : ℝ)-e/(1-q) ≤ x i ∧ x i ≤ (y i : ℝ)+e/(1-q) := by
  have hn := norm_le_of_box _ _ (residual_mem A C AB bB b y hA hb) e he hm
  have herror := solution_error_bound A (C.map (Rat.cast : ℚ → ℝ)) q hq hres b x
    (fun k => (y k : ℝ)) hx
  have hbound : ‖x-(fun k => (y k : ℝ))‖ ≤ e/(1-q) :=
    le_trans herror (div_le_div_of_nonneg_right hn (by linarith))
  have hi := le_trans (norm_le_pi_norm (x-(fun k => (y k : ℝ))) i) hbound
  rw [Real.norm_eq_abs] at hi
  have hh := abs_le.mp hi
  simp only [Pi.sub_apply] at hh
  constructor <;> linarith [hh.1, hh.2]

#print axioms residual_mem
#print axioms solution_coordinates
end N11Formalization.ResumeLinearSolveEnclosure
