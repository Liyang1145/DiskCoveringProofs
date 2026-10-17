import N11Formalization.SourceNColumnProposal
import N11Formalization.SourceNormalizedKernel
import N11Formalization.SourceNormalizedCanonical
import N11Formalization.ResumeLinearSolve

/-! Actual-N enclosure consumer. The exact solution stays M⁻¹ rhs.
Rational YN centres are proposals, used only through an actual residual bound.
No numerical inverse equality, N norm adequacy or local/global lower bound. -/
set_option autoImplicit false
namespace N11Formalization.SourceNEnclosure
open N11Formalization RatInterval SourceB41Proposal SourceB41ActualContraction
open SourceNormalizedKernel SourceNColumnProposal
noncomputable section

def centre (a : Fin 4) (i : Fin 41) : ℝ := (YN i a : ℝ)/100000000
def preconditionedRhs (i : Fin 41) (a : Fin 4) : ℝ :=
  ∑ k : Fin 41, (C i k : ℝ)*rhs a k
def actualResidual (a : Fin 4) : Fin 41 → ℝ :=
  (C.map (Rat.cast : ℚ → ℝ)).mulVec (rhs a-M.mulVec (centre a))

private theorem rhs_bounds (k : Fin 41) (a : Fin 4) :
    (-BFH k a : ℝ)/100000 ≤ rhs a k ∧ rhs a k ≤ (-BFL k a : ℝ)/100000 := by
  have h := actual_entry_bounds k (freeCol a)
  rw [← (free_binding k a).1,← (free_binding k a).2] at h
  unfold rhs
  constructor <;> linarith [h.1,h.2]

private theorem rhs_term_bounds (i k : Fin 41) (a : Fin 4) :
    ((CN i k*(if 0 ≤ CN i k then -BFH k a else -BFL k a) : ℤ) : ℝ)/
        10000000000000 ≤ (C i k : ℝ)*rhs a k ∧
    (C i k : ℝ)*rhs a k ≤
      ((CN i k*(if 0 ≤ CN i k then -BFL k a else -BFH k a) : ℤ) : ℝ)/
        10000000000000 := by
  have hb : ((-BFH k a : ℤ) : ℝ)/100000 ≤ rhs a k ∧
      rhs a k ≤ ((-BFL k a : ℤ) : ℝ)/100000 := by
    simpa only [Int.cast_neg] using rhs_bounds k a
  have hs (v : ℤ) :
      ((CN i k : ℝ)/100000000)*((v : ℝ)/100000) =
        ((CN i k*v : ℤ) : ℝ)/10000000000000 := by push_cast; ring
  have hc : (C i k : ℝ) = (CN i k : ℝ)/100000000 := by
    simp only [C,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  rw [hc]
  by_cases hn : 0 ≤ CN i k
  · have hr : (0 : ℝ) ≤ (CN i k : ℝ)/100000000 :=
      div_nonneg (by exact_mod_cast hn) (by norm_num)
    simp only [if_pos hn]
    constructor
    · rw [← hs]; exact mul_le_mul_of_nonneg_left hb.1 hr
    · rw [← hs]; exact mul_le_mul_of_nonneg_left hb.2 hr
  · have hr : (CN i k : ℝ)/100000000 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (not_le.mp hn).le) (by norm_num)
    simp only [if_neg hn]
    constructor
    · rw [← hs]; exact mul_le_mul_of_nonpos_left hb.2 hr
    · rw [← hs]; exact mul_le_mul_of_nonpos_left hb.1 hr

theorem preconditionedRhs_bounds (i : Fin 41) (a : Fin 4) :
    (CBL i a : ℝ)/10000000000000 ≤ preconditionedRhs i a ∧
      preconditionedRhs i a ≤ (CBH i a : ℝ)/10000000000000 := by
  simp only [CBL,CBH,Int.cast_sum,Finset.sum_div]
  constructor
  · exact Finset.sum_le_sum (fun k _ => (rhs_term_bounds i k a).1)
  · exact Finset.sum_le_sum (fun k _ => (rhs_term_bounds i k a).2)

theorem centre_defect (i : Fin 41) (a : Fin 4) :
    |preconditionedRhs i a-centre a i| ≤ (defectN i a : ℝ)/10000000000000 := by
  have h := preconditionedRhs_bounds i a
  have hs : centre a i = ((YN i a*100000 : ℤ) : ℝ)/10000000000000 := by
    simp only [centre,Int.cast_mul,Int.cast_ofNat]; ring
  have hlo : ((CBL i a-YN i a*100000 : ℤ) : ℝ)/10000000000000 ≤
      preconditionedRhs i a-centre a i := by
    simp only [Int.cast_sub,sub_div,← hs]; linarith [h.1]
  have hhi : preconditionedRhs i a-centre a i ≤
      ((CBH i a-YN i a*100000 : ℤ) : ℝ)/10000000000000 := by
    simp only [Int.cast_sub,sub_div,← hs]; linarith [h.2]
  have hh := abs_le_max_abs hlo hhi
  simpa only [defectN,Int.cast_max,Int.cast_abs,abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 10000000000000),
    max_div_div_right (by norm_num : (0 : ℝ) ≤ 10000000000000)] using hh

/-- Exact identity, different from the numerical residual calculation:
 C(b-My)=Cb-y+(I-CM)y. The actual M and rhs stay unchanged. -/
theorem actualResidual_identity (a : Fin 4) (i : Fin 41) :
    actualResidual a i = (preconditionedRhs i a-centre a i) +
      ∑ k : Fin 41,residualEntry i k*centre a k := by
  let E : Matrix (Fin 41) (Fin 41) ℝ := fun i k => residualEntry i k
  have hE : E = 1-(C.map (Rat.cast : ℚ → ℝ))*M := by
    ext j k
    simp only [E,residualEntry,Matrix.sub_apply,Matrix.one_apply,Matrix.mul_apply,
      Matrix.map_apply]
  have ha := congrFun (Matrix.sub_mulVec
    (1 : Matrix (Fin 41) (Fin 41) ℝ) ((C.map (Rat.cast : ℚ → ℝ))*M) (centre a)) i
  rw [← hE,Matrix.one_mulVec,← Matrix.mulVec_mulVec] at ha
  have hb := congrFun (Matrix.mulVec_sub (C.map (Rat.cast : ℚ → ℝ))
    (rhs a) (M.mulVec (centre a))) i
  change actualResidual a i =
    preconditionedRhs i a-(C.map (Rat.cast : ℚ → ℝ)).mulVec (M.mulVec (centre a)) i at hb
  change (∑ k : Fin 41,residualEntry i k*centre a k) =
    centre a i-(C.map (Rat.cast : ℚ → ℝ)).mulVec (M.mulVec (centre a)) i at ha
  rw [hb,ha]
  ring

theorem actualResidual_abs_bound (a : Fin 4) (i : Fin 41) :
    |actualResidual a i| ≤ (errorN i a : ℝ)/1000000000000000000000 := by
  have hs : (defectN i a : ℝ)/10000000000000 +
      (∑ k : Fin 41,(magN i k : ℝ)/10000000000000*|centre a k|) =
      (errorN i a : ℝ)/1000000000000000000000 := by
    simp only [errorN,Int.cast_add,Int.cast_mul,Int.cast_sum,Int.cast_abs,Int.cast_ofNat,
      centre,abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 100000000)]
    rw [add_div,Finset.sum_div]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k _
      ring
  rw [actualResidual_identity]
  apply (abs_add_le _ _).trans
  apply (add_le_add (centre_defect i a) _).trans_eq hs
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (actual_residual_cell i k) (abs_nonneg _)

theorem actualResidual_norm (a : Fin 4) : ‖actualResidual a‖ ≤ (1 : ℝ)/250 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/250)]
  intro i
  rw [Real.norm_eq_abs]
  have hn := all_errors i a
  change errorN i a ≤ 4000000000000000000 at hn
  have hc : (errorN i a : ℝ) ≤ 4000000000000000000 := by exact_mod_cast hn
  apply (actualResidual_abs_bound a i).trans
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000000000000000)).mpr
  linarith

theorem dependentColumn_error (a : Fin 4) :
    ‖dependentColumn a-centre a‖ ≤ (1 : ℝ)/245 := by
  have h := ResumeLinearSolve.solution_error_bound M
    (C.map (Rat.cast : ℚ → ℝ)) (1/50) (by norm_num) actual_contraction
    (rhs a) (dependentColumn a) (centre a) (dependentColumn_solve a)
  have hh := h.trans (div_le_div_of_nonneg_right (actualResidual_norm a)
    (by norm_num : (0 : ℝ) ≤ 1-1/50))
  norm_num at hh ⊢
  exact hh

def dependentBox (i : Fin 41) (a : Fin 4) : RatInterval :=
  intv ((YN i a : ℚ)/100000000-1/245) ((YN i a : ℚ)/100000000+1/245)

/-- All164 memberships of the actual exact M-inverse dependent columns.
The rational centres are NOT asserted equal to dependentColumn. -/
theorem dependentBox_mem (i : Fin 41) (a : Fin 4) :
    (dependentBox i a).Mem (dependentColumn a i) := by
  have h := (norm_le_pi_norm (dependentColumn a-centre a) i).trans (dependentColumn_error a)
  rw [Real.norm_eq_abs,Pi.sub_apply,abs_le] at h
  change (((YN i a : ℚ)/100000000-1/245 : ℚ) : ℝ) ≤ dependentColumn a i ∧
    dependentColumn a i ≤ (((YN i a : ℚ)/100000000+1/245 : ℚ) : ℝ)
  push_cast
  simp only [centre] at h
  constructor <;> linarith [h.1,h.2]

def NBox (e : Fin 45) (a : Fin 4) : RatInterval :=
  match columnEquiv.symm e with
  | .inl i => dependentBox i a
  | .inr b => ofRat (if b=a then 1 else 0)

/-- All180 actual N entries, retaining exact free-coordinate identity. -/
theorem NBox_mem (e : Fin 45) (a : Fin 4) : (NBox e a).Mem (N e a) := by
  unfold NBox N
  rcases columnEquiv.symm e with i | b
  · exact dependentBox_mem i a
  · by_cases hb : b=a
    · simp only [if_pos hb]; simpa using ofRat_mem (1 : ℚ)
    · simp only [if_neg hb]; simpa using ofRat_mem (0 : ℚ)

def canonicalNBox (e : ResumeNetwork.Edge) (a : Fin 4) : RatInterval :=
  if h : ∃ s : ResumeLocalIncidence.SourceEdge, ResumeLocalIncidence.edgeMap s = e then
    NBox (HarmonicSourceTransport.srcFlat (Classical.choose h)) a
  else ofRat 0

/-- ALL204 canonical51×4 actual-N memberships; zero on slack faces.
This is the numeric input shape for the adaptive chain, not its norm gate. -/
theorem canonicalNBox_mem (e : ResumeNetwork.Edge) (a : Fin 4) :
    (canonicalNBox e a).Mem (SourceNormalizedCanonical.Ncanon e a) := by
  unfold canonicalNBox SourceNormalizedCanonical.Ncanon
  split_ifs with h
  · exact NBox_mem _ _
  · simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)

end
end N11Formalization.SourceNEnclosure
#check @N11Formalization.SourceNEnclosure.actualResidual_norm
#check @N11Formalization.SourceNEnclosure.NBox_mem
#check @N11Formalization.SourceNEnclosure.canonicalNBox_mem
#print axioms N11Formalization.SourceNEnclosure.NBox_mem
#print axioms N11Formalization.SourceNEnclosure.canonicalNBox_mem
