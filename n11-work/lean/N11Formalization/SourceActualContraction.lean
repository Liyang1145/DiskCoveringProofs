import N11Formalization.SourceContractionProposal
import N11Formalization.ResumeLinearSolveInterval

/-! Real semantic consumer of the certified integer residual table. The SAME
actual20-node matrix, not its midpoint, satisfies ||I-C A||<=1/50<1.
The rational C is only a preconditioner proposal. All actual matrix entry
memberships, source incidence, scaling and row checks are discharged. -/
set_option autoImplicit false
namespace N11Formalization.SourceActualContraction
open N11Formalization RatInterval ResumeLocalIncidence HarmonicSourceTransport
open SourceActiveLaplacian SourceActiveFiniteSystem SourceCompactStressIntervals
open SourceContractionProposal
noncomputable section

private theorem term_bounds (e : SourceEdge) (i j : Fin 20) :
    ((if 0≤productZ e i j then loN (srcFlat e)*productZ e i j
      else hiN (srcFlat e)*productZ e i j : ℤ) : ℝ)/100000000 ≤
        SourceSignedStressAssembly.stress e*B e (nodeEquiv.symm i)*B e (nodeEquiv.symm j) ∧
    SourceSignedStressAssembly.stress e*B e (nodeEquiv.symm i)*B e (nodeEquiv.symm j) ≤
      ((if 0≤productZ e i j then hiN (srcFlat e)*productZ e i j
      else loN (srcFlat e)*productZ e i j : ℤ) : ℝ)/100000000 := by
  have hs := mem_iff.mp (compact_mem e)
  simp only [SourceCompactStressIntervals.compact,RatInterval.intv] at hs
  push_cast at hs
  have he :
      SourceSignedStressAssembly.stress e*B e (nodeEquiv.symm i)*B e (nodeEquiv.symm j)=
        SourceSignedStressAssembly.stress e*(productZ e i j : ℝ) := by
    simp only [productZ,B,Int.cast_mul]
    ring
  rw [he]
  by_cases hz : 0≤productZ e i j
  · have hr : (0 : ℝ)≤(productZ e i j : ℝ) := by exact_mod_cast hz
    simp only [if_pos hz,Int.cast_mul]
    constructor
    · simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hs.1 hr
    · simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hs.2 hr
  · have hr : (productZ e i j : ℝ)≤0 := by exact_mod_cast (not_le.mp hz).le
    simp only [if_neg hz,Int.cast_mul]
    constructor
    · simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonpos_right hs.2 hr
    · simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonpos_right hs.1 hr

/-- Current integer matrix table encloses the ACTUAL scalar free block. -/
theorem actual_matrix_bounds (i j : Fin 20) :
    (AL i j : ℝ)/100000000 ≤ matrix20 i j ∧
      matrix20 i j≤(AH i j : ℝ)/100000000 := by
  rw [(table_binding i j).1,(table_binding i j).2]
  unfold lowerSum upperSum
  push_cast
  rw [Finset.sum_div,Finset.sum_div]
  change _ ≤ ∑ e : SourceEdge,
      SourceSignedStressAssembly.stress e*B e (nodeEquiv.symm i)*B e (nodeEquiv.symm j) ∧
    (∑ e : SourceEdge,
      SourceSignedStressAssembly.stress e*B e (nodeEquiv.symm i)*B e (nodeEquiv.symm j)) ≤ _
  constructor
  · apply Finset.sum_le_sum
    intro e _
    simpa only [Int.cast_ite,Int.cast_mul] using (term_bounds e i j).1
  · apply Finset.sum_le_sum
    intro e _
    simpa only [Int.cast_ite,Int.cast_mul] using (term_bounds e i j).2

def residualEntry (i j : Fin 20) : ℝ :=
  (if i=j then 1 else 0)-∑ k : Fin 20,(C i k : ℝ)*matrix20 k j

private theorem sum_scale (i j : Fin 20) (V : Fin 20 → Fin 20 → ℤ) :
    (∑ k : Fin 20,(C i k : ℝ)*((V k j : ℝ)/100000000))=
      ((∑ k : Fin 20,CN i k*V k j : ℤ) : ℝ)/10000000000000000 := by
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  simp only [C,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  ring

theorem actual_residual_bounds (i j : Fin 20) :
    (RL i j : ℝ)/10000000000000000≤residualEntry i j ∧
      residualEntry i j≤(RH i j : ℝ)/10000000000000000 := by
  have hc (k : Fin 20) : (0 : ℝ)≤(C i k : ℝ) := by
    have h : (0 : ℝ)≤(CN i k : ℝ) := by exact_mod_cast CN_nonneg i k
    simp only [C,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
    exact div_nonneg h (by norm_num)
  have hlo := Finset.sum_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin 20))) =>
    mul_le_mul_of_nonneg_left (actual_matrix_bounds k j).1 (hc k))
  have hhi := Finset.sum_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin 20))) =>
    mul_le_mul_of_nonneg_left (actual_matrix_bounds k j).2 (hc k))
  rw [sum_scale i j AL] at hlo
  rw [sum_scale i j AH] at hhi
  have hdiag : ((if i=j then (10000000000000000 : ℤ) else 0) : ℝ)/
      10000000000000000=(if i=j then (1 : ℝ) else 0) := by
    by_cases hij : i=j <;> simp [hij]
  push_cast at hlo hhi
  simp only [RL,RH,Int.cast_sub,Int.cast_sum,Int.cast_mul,Int.cast_ite,
    Int.cast_ofNat,Int.cast_zero,sub_div,hdiag]
  unfold residualEntry
  constructor <;> linarith

theorem actual_residual_rows (i : Fin 20) :
    ∑ j : Fin 20,|residualEntry i j|≤(1 : ℝ)/50 := by
  have hr := all_rows i
  change (50 : ℤ)*(∑ j : Fin 20,max |RL i j| |RH i j|)≤10000000000000000 at hr
  have hcast : (50 : ℝ)*(∑ j : Fin 20,max |(RL i j : ℝ)| |(RH i j : ℝ)|)≤
      10000000000000000 := by exact_mod_cast hr
  have hscale :
      (∑ j : Fin 20,max |((RL i j : ℝ)/10000000000000000)|
        |((RH i j : ℝ)/10000000000000000)|)=
      (∑ j : Fin 20,max |(RL i j : ℝ)| |(RH i j : ℝ)|)/10000000000000000 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_div,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<10000000000000000),
      max_div_div_right (by norm_num : (0 : ℝ)≤10000000000000000)]
  have hm := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 20))) =>
    abs_le_max_abs (actual_residual_bounds i j).1 (actual_residual_bounds i j).2)
  rw [hscale] at hm
  have hbound :
      (∑ j : Fin 20,max |(RL i j : ℝ)| |(RH i j : ℝ)|)/
        10000000000000000≤(1 : ℝ)/50 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<10000000000000000)).mpr
    linarith
  exact hm.trans hbound

def residualCLM : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ) :=
  ContinuousLinearMap.id ℝ (Fin 20 → ℝ)-
    (ratMatCLM (fun i k => C i k)).comp (ResumeLinearSolveInterval.realMatCLM matrix20)

theorem residualCLM_entry (i j : Fin 20) :
    residualCLM (Pi.single j 1) i=residualEntry i j := by
  simp only [residualCLM,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    Pi.sub_apply]
  rw [ResumeLinearSolveInterval.realMatCLM_apply,ratMatCLM_apply]
  have hA (k : Fin 20) :
      matrix20.mulVec (Pi.single j 1) k=matrix20 k j := by
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  simp_rw [hA]
  simp [residualEntry,Pi.single_apply]

theorem residualCLM_bound : ‖residualCLM‖≤(1 : ℝ)/50 :=
  opNorm_le_rowSum residualCLM (by norm_num)
    (fun i => by simpa only [residualCLM_entry] using actual_residual_rows i)

/-- Unconditional contraction for actual20 matrix and exact rational proposal.
This is the semantic q<1 certificate, not just an integer table statement. -/
theorem actual_contraction (x : Fin 20 → ℝ) :
    ‖x-(C.map (Rat.cast : ℚ → ℝ)).mulVec (matrix20.mulVec x)‖≤
      ((1 : ℝ)/50)*‖x‖ := by
  have h := residualCLM.le_opNorm x
  have he : residualCLM x=x-(C.map (Rat.cast : ℚ → ℝ)).mulVec (matrix20.mulVec x) := by
    funext i
    simp only [residualCLM,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
      ResumeLinearSolveInterval.realMatCLM_apply,Pi.sub_apply]
    rw [ratMatCLM_apply]
    rfl
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right residualCLM_bound (norm_nonneg x))

/-- Actual H20 error bound for ANY proposed centre, with the contraction and
actual source solve paid. Only the magnitude of this ACTUAL residual remains
to be certified numerically; no midpoint solution is asserted to be exact. -/
theorem H20_error_bound (j : Fin 9) (y : Fin 20 → ℝ) :
    ‖H20 j-y‖ ≤
      ‖(C.map (Rat.cast : ℚ → ℝ)).mulVec (rhs20 j-matrix20.mulVec y)‖/
        (1-(1 : ℝ)/50) :=
  ResumeLinearSolve.solution_error_bound matrix20 (C.map (Rat.cast : ℚ → ℝ))
    (1/50) (by norm_num) actual_contraction (rhs20 j) (H20 j) y (H20_solve j)

end
end N11Formalization.SourceActualContraction
#check @N11Formalization.SourceActualContraction.actual_matrix_bounds
#check @N11Formalization.SourceActualContraction.actual_contraction
#check @N11Formalization.SourceActualContraction.H20_error_bound
#print axioms N11Formalization.SourceActualContraction.actual_contraction
