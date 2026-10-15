import N11Formalization.ResumeLinearSolveRefine

namespace N11Formalization.ResumeLinearSolveIterate
open RatInterval ResumeLinearSolveRefine

def iterBox {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (AB : Fin n → Fin n → RatInterval) (bB : Fin n → RatInterval)
    (y : Fin n → ℚ) (err : Fin n → RatInterval) : ℕ → Fin n → RatInterval
  | 0 => err
  | k+1 => refineBox C AB bB y (iterBox C AB bB y err k)

/-- Any finite number of outward refinements preserves the actual solution error.
No monotonic shrinkage, numerical convergence or rounded-zero premise is needed. -/
theorem iter_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℚ) (AB : Fin n → Fin n → RatInterval)
    (bB : Fin n → RatInterval) (b x : Fin n → ℝ) (y : Fin n → ℚ)
    (err : Fin n → RatInterval) (hA : ∀ i j, Mem (AB i j) (A i j))
    (hb : ∀ i, Mem (bB i) (b i)) (hx : A.mulVec x=b)
    (herr : ∀ i, Mem (err i) (x i-(y i : ℝ))) :
    ∀ k i, Mem (iterBox C AB bB y err k i) (x i-(y i : ℝ)) := by
  intro k
  induction k with
  | zero => exact herr
  | succ k ih => exact refine_mem A C AB bB b x y _ hA hb hx ih

#print iter_mem
#print axioms iter_mem
end N11Formalization.ResumeLinearSolveIterate
