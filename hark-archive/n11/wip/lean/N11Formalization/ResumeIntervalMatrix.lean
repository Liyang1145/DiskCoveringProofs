import N11Formalization.ResumeIntervalCoercivity

namespace N11Formalization.ResumeIntervalMatrix
open Finset Matrix RatInterval

/-- Executable interval sum with exactly the `Fin.sum_univ_succ` ordering. -/
def isum : {n : ℕ} → (Fin n → RatInterval) → RatInterval
  | 0, _ => ofRat 0
  | _+1, A => (A 0).add (isum (fun i => A i.succ))

theorem isum_mem {n : ℕ} (A : Fin n → RatInterval) (x : Fin n → ℝ)
    (hx : ∀ i, Mem (A i) (x i)) : Mem (isum A) (∑ i, x i) := by
  induction n with
  | zero => simpa [isum] using ofRat_mem (0 : ℚ)
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact add_mem (hx 0) (ih (fun i => A i.succ) (fun i => x i.succ) (fun i => hx i.succ))

/-- No midpoint multiplication: every product and sum is outward enclosed. -/
def imul {n m p : ℕ} (A : Fin n → Fin m → RatInterval)
    (B : Fin m → Fin p → RatInterval) (i : Fin n) (j : Fin p) : RatInterval :=
  isum (fun k => (A i k).mul (B k j))

theorem imul_mem {n m p : ℕ} (A : Fin n → Fin m → RatInterval)
    (B : Fin m → Fin p → RatInterval) (X : Matrix (Fin n) (Fin m) ℝ)
    (Y : Matrix (Fin m) (Fin p) ℝ)
    (hX : ∀ i j, Mem (A i j) (X i j)) (hY : ∀ i j, Mem (B i j) (Y i j)) :
    ∀ i j, Mem (imul A B i j) ((X*Y) i j) := by
  intro i j
  exact isum_mem _ _ (fun k => mul_mem (hX i k) (hY k j))

/-- A rational proposal is exact, not an approximate inverse assertion. -/
def rationalBox {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℚ) : Fin n → Fin m → RatInterval :=
  fun i j => ofRat (C i j)

def congruenceBox {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (B : Fin n → Fin n → RatInterval) :=
  imul (imul (rationalBox C.transpose) B) (rationalBox C)

theorem congruence_mem {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (B : Fin n → Fin n → RatInterval) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, Mem (B i j) (M i j)) :
    ∀ i j, Mem (congruenceBox C B i j)
      (((C.map (Rat.cast : ℚ → ℝ)).transpose * M * C.map (Rat.cast : ℚ → ℝ)) i j) := by
  apply imul_mem
  · apply imul_mem
    · intro i j; exact ofRat_mem _
    · exact hM
  · intro i j; exact ofRat_mem _

/-- Symmetry is transported algebraically, not read off symmetric intervals. -/
theorem congruence_symmetric {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℝ)
    (hs : ∀ i j, M i j = M j i) :
    ∀ i j, (C.transpose*M*C) i j = (C.transpose*M*C) j i := by
  have hm : M.transpose = M := by ext i j; exact hs j i
  have he : (C.transpose*M*C).transpose = C.transpose*M*C := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hm, Matrix.mul_assoc]
  intro i j
  exact (congrFun (congrFun he j) i)

/-- End-to-end finite consumer: input enclosures of M, exact rational C,
computed congruence intervals, and rational row inequalities suffice. -/
theorem nonneg_of_computed_congruence {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℚ) (B : Fin n → Fin n → RatInterval)
    (η : ℚ) (hη : 0 < η) (hs : ∀ i j, M i j=M j i)
    (hmem : ∀ i j, Mem (B i j) (M i j))
    (hrow : ∀ i, η+(∑ j, if j=i then 0 else (congruenceBox C B i j).abs.hi)
        ≤ (congruenceBox C B i i).lo) (x : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, M i j*x i*x j := by
  exact ResumeIntervalCoercivity.nonneg_of_intervals M (C.map (Rat.cast : ℚ → ℝ))
    (congruenceBox C B) η hη (congruence_symmetric _ _ hs) (congruence_mem C B M hmem) hrow x

#print axioms nonneg_of_computed_congruence
#print axioms isum_mem
#print axioms imul_mem
#print axioms congruence_mem
end N11Formalization.ResumeIntervalMatrix
