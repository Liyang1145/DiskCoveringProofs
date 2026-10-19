import N11Formalization.ResumeLinearSolveEnclosure

namespace N11Formalization.ResumeLinearSolveRefine
open RatInterval ResumeIntervalMatrix ResumeLinearSolveEnclosure

/-- One outward interval fixed-point refinement; not an intersection heuristic. -/
def refineBox {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (AB : Fin n → Fin n → RatInterval) (bB : Fin n → RatInterval)
    (y : Fin n → ℚ) (err : Fin n → RatInterval) (i : Fin n) : RatInterval :=
  (residualBox C AB bB y i).add
    (isum (fun j => (krawczykMat C AB i j).mul (err j)))

theorem error_fixed_point {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℝ)
    (b x y : Fin n → ℝ) (hx : A.mulVec x=b) :
    x-y = C.mulVec (b-A.mulVec y)+(x-y-C.mulVec (A.mulVec (x-y))) := by
  rw [Matrix.mulVec_sub A, hx]
  abel

theorem refine_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℚ) (AB : Fin n → Fin n → RatInterval)
    (bB : Fin n → RatInterval) (b x : Fin n → ℝ) (y : Fin n → ℚ)
    (err : Fin n → RatInterval) (hA : ∀ i j, Mem (AB i j) (A i j))
    (hb : ∀ i, Mem (bB i) (b i)) (hx : A.mulVec x=b)
    (herr : ∀ i, Mem (err i) (x i-(y i : ℝ))) :
    ∀ i, Mem (refineBox C AB bB y err i) (x i-(y i : ℝ)) := by
  let Cr : Matrix (Fin n) (Fin n) ℝ := C.map (Rat.cast : ℚ → ℝ)
  let yr : Fin n → ℝ := fun i => (y i : ℝ)
  let E : Matrix (Fin n) (Fin n) ℝ := 1-Cr*A
  have hE : ∀ i j, Mem (krawczykMat C AB i j) (E i j) := by
    intro i j
    have hh := mem_krawczykMat (Y := C) (J := AB)
      (A := ResumeLinearSolveInterval.realMatCLM A)
      (fun k l => by simpa only [ResumeLinearSolveInterval.realMatCLM_single] using hA k l) i j
    have hc : (ratMatCLM C) ((ResumeLinearSolveInterval.realMatCLM A) (Pi.single j 1)) i =
        ∑ k, (C i k : ℝ)*A k j := by
      exact (ratMatCLM_apply C ((ResumeLinearSolveInterval.realMatCLM A) (Pi.single j 1)) i).trans
        (Finset.sum_congr rfl (fun k _ => congrArg (fun z : ℝ => (C i k : ℝ)*z)
          (ResumeLinearSolveInterval.realMatCLM_single A k j)))
    convert hh using 1
    simp only [E, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
      Cr, Matrix.map_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, hc]
    simp [Pi.single_apply, eq_comm]
    exact hc.symm
  have hid : x-yr = Cr.mulVec (b-A.mulVec yr)+E.mulVec (x-yr) := by
    rw [show E=1-Cr*A from rfl, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec]
    exact error_fixed_point A Cr b x yr hx
  intro i
  have hh := add_mem (residual_mem A C AB bB b y hA hb i)
    (isum_mem _ _ (fun j => mul_mem (hE i j) (herr j)))
  change Mem (refineBox C AB bB y err i) ((x-yr) i)
  rw [hid]
  exact hh

#print axioms refine_mem
end N11Formalization.ResumeLinearSolveRefine
