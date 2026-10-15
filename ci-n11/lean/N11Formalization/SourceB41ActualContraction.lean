import N11Formalization.SourceB41Proposal
import N11Formalization.ResumeLinearSolveInterval

/-! DRAFT awaiting gate: actual corrected source41 matrix contraction and invertibility.
Integer tables alone are not accepted as real matrix semantics. This consumer
must be compiled after the proposal is actually built. No N/G/global claim. -/
set_option autoImplicit false
namespace N11Formalization.SourceB41ActualContraction
open N11Formalization RatInterval SourceN2 SourceBPointPacket SourceB41Proposal
noncomputable section

def M : Matrix (Fin 41) (Fin 41) ℝ :=
  fun i j => srcB2 SourceExactRoot.sourceRoot i (dep j)

private theorem edge_bounds (e : Fin 45) (q : Fin 2) :
    ((PL (srcEdgeV2 e) q-PH (srcEdgeW2 e) q : ℤ) : ℝ)/100000 ≤
      srcD2 SourceExactRoot.sourceRoot e q ∧
    srcD2 SourceExactRoot.sourceRoot e q ≤
      ((PH (srcEdgeV2 e) q-PL (srcEdgeW2 e) q : ℤ) : ℝ)/100000 := by
  have hv := pointI_mem (srcEdgeV2 e) q
  have hw := pointI_mem (srcEdgeW2 e) q
  simp only [pointI,intv,mem_iff,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] at hv hw
  simp only [srcD2,Int.cast_sub,sub_div]
  exact ⟨sub_le_sub hv.1 hw.2,sub_le_sub hv.2 hw.1⟩

private theorem point_width (i : Fin 29) (q : Fin 2) :
    (PL i q : ℝ) ≤ (PH i q : ℝ) := by
  have h : PL i q ≤ PH i q := by
    fin_cases i <;> fin_cases q <;> decide
  exact_mod_cast h

private theorem assemble_entry {pL pH qL qH d : ℝ}
    {a b : Prop} [Decidable a] [Decidable b]
    (hp : pL ≤ pH) (hq : qL ≤ qH)
    (hdL : pL - qH ≤ d) (hdU : d ≤ pH - qL) :
    (if a then d else 0) + (if b then -d else 0) ∈
      Set.Icc
        ((if a then pL - qH else 0) + (if b then -(pH - qL) else 0))
        ((if a then pH - qL else 0) + (if b then -(pL - qH) else 0)) := by
  by_cases ha : a
  · by_cases hb : b
    · simp only [if_pos ha,if_pos hb]
      constructor <;> linarith [hp,hq]
    · simp only [if_pos ha,if_neg hb]
      constructor
      · simpa using hdL
      · simpa using hdU
  · by_cases hb : b
    · simp only [if_neg ha,if_pos hb]
      constructor <;> linarith [hdL,hdU]
    · simp only [if_neg ha,if_neg hb]
      exact ⟨le_rfl,le_rfl⟩

theorem actual_entry_bounds (i : Fin 41) (e : Fin 45) :
    (loEntry i e : ℝ)/100000 ≤ srcB2 SourceExactRoot.sourceRoot i e ∧
      srcB2 SourceExactRoot.sourceRoot i e ≤ (hiEntry i e : ℝ)/100000 := by
  by_cases hi : i.val = 40
  · simp [loEntry,hiEntry,srcB2,hi]
  · have he := edge_bounds e (⟨i.val%2,by omega⟩ : Fin 2)
    have hwidthV := point_width (srcEdgeV2 e) (⟨i.val%2,by omega⟩ : Fin 2)
    have hwidthW := point_width (srcEdgeW2 e) (⟨i.val%2,by omega⟩ : Fin 2)
    have ha := assemble_entry
      (a := (srcEdgeV2 e).val = 9+i.val/2)
      (b := (srcEdgeW2 e).val = 9+i.val/2)
      (pL := (PL (srcEdgeV2 e) (⟨i.val%2,by omega⟩ : Fin 2) : ℝ)/100000)
      (pH := (PH (srcEdgeV2 e) (⟨i.val%2,by omega⟩ : Fin 2) : ℝ)/100000)
      (qL := (PL (srcEdgeW2 e) (⟨i.val%2,by omega⟩ : Fin 2) : ℝ)/100000)
      (qH := (PH (srcEdgeW2 e) (⟨i.val%2,by omega⟩ : Fin 2) : ℝ)/100000)
      (d := srcD2 SourceExactRoot.sourceRoot e (⟨i.val%2,by omega⟩ : Fin 2))
      (by exact div_le_div_of_nonneg_right hwidthV (by norm_num))
      (by exact div_le_div_of_nonneg_right hwidthW (by norm_num))
      (by simpa only [Int.cast_sub,sub_div] using he.1)
      (by simpa only [Int.cast_sub,sub_div] using he.2)
    push_cast at ha
    convert ha using 1 <;>
      simp only [loEntry,hiEntry,srcB2,if_neg hi,Int.cast_ite,Int.cast_add,
        Int.cast_sub,Int.cast_neg,Int.cast_zero,add_div,sub_div,neg_div,
        zero_div,zero_add,add_zero,Set.mem_Icc] <;>
      split_ifs <;> ring

theorem actual_matrix_bounds (i j : Fin 41) :
    (ML i j : ℝ)/100000 ≤ M i j ∧ M i j ≤ (MH i j : ℝ)/100000 :=
  actual_entry_bounds i (dep j)

private theorem product_scale (i k : Fin 41) (v : ℤ) :
    ((CN i k : ℝ)/100000000)*((v : ℝ)/100000) =
      ((CN i k*v : ℤ) : ℝ)/10000000000000 := by
  push_cast
  ring

private theorem term_bounds (i k j : Fin 41) :
    ((CN i k*(if 0 ≤ CN i k then ML k j else MH k j) : ℤ) : ℝ)/
        10000000000000 ≤ (C i k : ℝ)*M k j ∧
    (C i k : ℝ)*M k j ≤
      ((CN i k*(if 0 ≤ CN i k then MH k j else ML k j) : ℤ) : ℝ)/
        10000000000000 := by
  have hm := actual_matrix_bounds k j
  have hc : (C i k : ℝ) = (CN i k : ℝ)/100000000 := by
    simp only [C,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  rw [hc]
  by_cases hn : 0 ≤ CN i k
  · simp only [if_pos hn]
    have hr : (0 : ℝ) ≤ (CN i k : ℝ)/100000000 :=
      div_nonneg (by exact_mod_cast hn) (by norm_num)
    constructor
    · rw [← product_scale]
      exact mul_le_mul_of_nonneg_left hm.1 hr
    · rw [← product_scale]
      exact mul_le_mul_of_nonneg_left hm.2 hr
  · simp only [if_neg hn]
    have hr : (CN i k : ℝ)/100000000 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (not_le.mp hn).le) (by norm_num)
    constructor
    · rw [← product_scale]
      exact mul_le_mul_of_nonpos_left hm.2 hr
    · rw [← product_scale]
      exact mul_le_mul_of_nonpos_left hm.1 hr

def residualEntry (i j : Fin 41) : ℝ :=
  (if i = j then 1 else 0)-∑ k : Fin 41,(C i k : ℝ)*M k j

theorem actual_residual_bounds (i j : Fin 41) :
    (RL i j : ℝ)/10000000000000 ≤ residualEntry i j ∧
      residualEntry i j ≤ (RH i j : ℝ)/10000000000000 := by
  have hlo := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 41))) =>
    (term_bounds i k j).1)
  have hhi := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 41))) =>
    (term_bounds i k j).2)
  rw [← Finset.sum_div,← Int.cast_sum] at hlo hhi
  simp only [RL,RH,Int.cast_sub,Int.cast_sum,Int.cast_mul,sub_div,Int.cast_ite,
    Int.cast_ofNat,Int.cast_zero]
  push_cast at hlo hhi
  unfold residualEntry
  by_cases hij : i = j
  · simp only [hij,if_true] at hlo hhi ⊢
    constructor <;> linarith [hlo,hhi]
  · simp only [hij,if_false] at hlo hhi ⊢
    constructor <;> linarith [hlo,hhi]

theorem actual_residual_cell (i j : Fin 41) :
    |residualEntry i j| ≤ (magN i j : ℝ)/10000000000000 := by
  have h := abs_le_max_abs (actual_residual_bounds i j).1 (actual_residual_bounds i j).2
  have hc : max |(RL i j : ℝ)| |(RH i j : ℝ)| ≤ (magN i j : ℝ) := by
    exact_mod_cast all_cells i j
  have hs :
      max |((RL i j : ℝ)/10000000000000)| |((RH i j : ℝ)/10000000000000)| =
        max |(RL i j : ℝ)| |(RH i j : ℝ)|/10000000000000 := by
    rw [abs_div,abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 10000000000000),
      max_div_div_right (by norm_num : (0 : ℝ) ≤ 10000000000000)]
  rw [hs] at h
  exact h.trans (div_le_div_of_nonneg_right hc (by norm_num))

theorem actual_residual_rows (i : Fin 41) :
    ∑ j : Fin 41, |residualEntry i j| ≤ (1 : ℝ)/50 := by
  have hr := all_rows i
  change (50 : ℤ)*(∑ j : Fin 41,magN i j) ≤ 10000000000000 at hr
  have hc : (50 : ℝ)*(∑ j : Fin 41,(magN i j : ℝ)) ≤ 10000000000000 := by
    exact_mod_cast hr
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 41))) =>
    actual_residual_cell i j)
  rw [← Finset.sum_div] at hs
  have hb : (∑ j : Fin 41,(magN i j : ℝ))/10000000000000 ≤ (1 : ℝ)/50 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10000000000000)).mpr
    linarith
  exact hs.trans hb

def residualCLM : (Fin 41 → ℝ) →L[ℝ] (Fin 41 → ℝ) :=
  ContinuousLinearMap.id ℝ (Fin 41 → ℝ)-
    (ratMatCLM (fun i j => C i j)).comp (ResumeLinearSolveInterval.realMatCLM M)

theorem residualCLM_entry (i j : Fin 41) :
    residualCLM (Pi.single j 1) i = residualEntry i j := by
  simp only [residualCLM,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    Pi.sub_apply]
  rw [ResumeLinearSolveInterval.realMatCLM_apply,ratMatCLM_apply]
  have hm (k : Fin 41) : M.mulVec (Pi.single j 1) k = M k j := by
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  simp_rw [hm]
  simp [residualEntry,Pi.single_apply]

theorem residualCLM_bound : ‖residualCLM‖ ≤ (1 : ℝ)/50 :=
  opNorm_le_rowSum residualCLM (by norm_num)
    (fun i => by simpa only [residualCLM_entry] using actual_residual_rows i)

theorem actual_contraction (x : Fin 41 → ℝ) :
    ‖x-(C.map (Rat.cast : ℚ → ℝ)).mulVec (M.mulVec x)‖ ≤ ((1 : ℝ)/50)*‖x‖ := by
  have h := residualCLM.le_opNorm x
  have he : residualCLM x = x-(C.map (Rat.cast : ℚ → ℝ)).mulVec (M.mulVec x) := by
    funext i
    simp only [residualCLM,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
      ResumeLinearSolveInterval.realMatCLM_apply,Pi.sub_apply]
    rw [ratMatCLM_apply]
    rfl
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right residualCLM_bound (norm_nonneg x))

theorem M_mulVec_injective : Function.Injective M.mulVec := by
  intro x y hxy
  have h := actual_contraction (x-y)
  rw [Matrix.mulVec_sub,hxy,sub_self,Matrix.mulVec_zero,sub_zero] at h
  have hz : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem M_isUnit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp M_mulVec_injective
theorem M_det_ne_zero : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp M_isUnit).ne_zero

end
end N11Formalization.SourceB41ActualContraction
#check @N11Formalization.SourceB41ActualContraction.actual_matrix_bounds
#check @N11Formalization.SourceB41ActualContraction.actual_contraction
#check @N11Formalization.SourceB41ActualContraction.M_det_ne_zero
#print axioms N11Formalization.SourceB41ActualContraction.actual_contraction
#print axioms N11Formalization.SourceB41ActualContraction.M_det_ne_zero
