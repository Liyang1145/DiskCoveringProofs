import N11Formalization.SourceFineNResidualPacket
import N11Formalization.SourceNEnclosure

/-! Real consumer of the combined RHS-minus-M*centre residual certificate.
SAME actual N=M^-1 rhs, same C/centre/free columns/graph. No inverse/membership/
numeric residual premise; no source root or N is replaced by a rational table. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineNEnclosure
open N11Formalization RatInterval SourceN2 SourceFineBPointPacket
open _root_.N11Formalization.SourceB41Proposal hiding loEntry hiEntry
open SourceB41ActualContraction SourceNormalizedKernel SourceNEnclosure
open SourceFineNResidualPacket
noncomputable section

private theorem edge_bounds (e : Fin 45) (q : Fin 2) :
    ((PL (srcEdgeV2 e) q-PH (srcEdgeW2 e) q : ℤ) : ℝ)/100000000 ≤
      srcD2 SourceExactRoot.sourceRoot e q ∧
    srcD2 SourceExactRoot.sourceRoot e q ≤
      ((PH (srcEdgeV2 e) q-PL (srcEdgeW2 e) q : ℤ) : ℝ)/100000000 := by
  have hv := pointI_mem (srcEdgeV2 e) q
  have hw := pointI_mem (srcEdgeW2 e) q
  simp only [pointI,intv,mem_iff,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] at hv hw
  simp only [srcD2,Int.cast_sub,sub_div]
  exact ⟨sub_le_sub hv.1 hw.2,sub_le_sub hv.2 hw.1⟩

private theorem assemble_entry {pL pH qL qH d : ℝ}
    {a b : Prop} [Decidable a] [Decidable b]
    (hp : pL≤pH) (hq : qL≤qH)
    (hdL : pL-qH≤d) (hdU : d≤pH-qL) :
    (if a then d else 0)+(if b then -d else 0) ∈
      Set.Icc ((if a then pL-qH else 0)+(if b then -(pH-qL) else 0))
        ((if a then pH-qL else 0)+(if b then -(pL-qH) else 0)) := by
  by_cases ha : a
  · by_cases hb : b
    · simp only [if_pos ha,if_pos hb]; constructor <;> linarith [hp,hq]
    · simp only [if_pos ha,if_neg hb,add_zero]; exact ⟨hdL,hdU⟩
  · by_cases hb : b
    · simp only [if_neg ha,if_pos hb]; constructor <;> linarith [hdL,hdU]
    · simp only [if_neg ha,if_neg hb]; exact ⟨le_rfl,le_rfl⟩

/-- ALL1845 finer actual B entries, retaining mass row40=1. -/
theorem actual_entry_bounds (i : Fin 41) (e : Fin 45) :
    (loEntry i e : ℝ)/100000000 ≤ srcB2 SourceExactRoot.sourceRoot i e ∧
      srcB2 SourceExactRoot.sourceRoot i e≤(hiEntry i e : ℝ)/100000000 := by
  by_cases hi : i.val=40
  · simp [loEntry,hiEntry,srcB2,hi]
  · let q : Fin 2 := ⟨i.val%2,by omega⟩
    have he := edge_bounds e q
    have hv : (PL (srcEdgeV2 e) q : ℝ)≤(PH (srcEdgeV2 e) q : ℝ) := by
      exact_mod_cast point_width (srcEdgeV2 e) q
    have hw : (PL (srcEdgeW2 e) q : ℝ)≤(PH (srcEdgeW2 e) q : ℝ) := by
      exact_mod_cast point_width (srcEdgeW2 e) q
    have ha := assemble_entry
      (a := (srcEdgeV2 e).val=9+i.val/2) (b := (srcEdgeW2 e).val=9+i.val/2)
      (pL := (PL (srcEdgeV2 e) q : ℝ)/100000000)
      (pH := (PH (srcEdgeV2 e) q : ℝ)/100000000)
      (qL := (PL (srcEdgeW2 e) q : ℝ)/100000000)
      (qH := (PH (srcEdgeW2 e) q : ℝ)/100000000)
      (d := srcD2 SourceExactRoot.sourceRoot e q)
      (div_le_div_of_nonneg_right hv (by norm_num))
      (div_le_div_of_nonneg_right hw (by norm_num))
      (by simpa only [Int.cast_sub,sub_div] using he.1)
      (by simpa only [Int.cast_sub,sub_div] using he.2)
    push_cast at ha
    convert ha using 1 <;>
      simp only [loEntry,hiEntry,srcB2,if_neg hi,Int.cast_ite,Int.cast_add,
        Int.cast_sub,Int.cast_neg,Int.cast_zero,add_div,sub_div,neg_div,
        zero_div,zero_add,add_zero,Set.mem_Icc,q] <;> split_ifs <;> ring

def force (a : Fin 4) (r : Fin 41) : ℝ :=
  ∑ e : Fin 45,srcB2 SourceExactRoot.sourceRoot r e*((QN e a : ℝ)/100000000)

/-- Binding of the full45 candidate: exact RHS and matrix product combined,
not the old independent C*rhs-centre+(I-CM)*centre estimate. -/
theorem force_identity (a : Fin 4) (r : Fin 41) :
    force a r=M.mulVec (centre a) r-rhs a r := by
  have hs := columnEquiv.sum_comp
    (fun e : Fin 45 => srcB2 SourceExactRoot.sourceRoot r e*((QN e a : ℝ)/100000000))
  unfold force
  rw [← hs,Fintype.sum_sum_type]
  simp only [columnEquiv_dep,columnEquiv_free,QN_dep,QN_free]
  simp only [Int.cast_ite,Int.cast_ofNat,Int.cast_zero,ite_div,
    div_self (by norm_num : (100000000 : ℝ)≠0),zero_div,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [Matrix.mulVec,dotProduct,M,centre,rhs,sub_neg_eq_add]

private theorem force_term_bounds (r : Fin 41) (a : Fin 4) (e : Fin 45) :
    ((QN e a*(if 0≤QN e a then loEntry r e else hiEntry r e) : ℤ) : ℝ)/
        10000000000000000 ≤
      srcB2 SourceExactRoot.sourceRoot r e*((QN e a : ℝ)/100000000) ∧
    srcB2 SourceExactRoot.sourceRoot r e*((QN e a : ℝ)/100000000) ≤
      ((QN e a*(if 0≤QN e a then hiEntry r e else loEntry r e) : ℤ) : ℝ)/
        10000000000000000 := by
  have hb := actual_entry_bounds r e
  have hscale (v : ℤ) :
      ((QN e a*v : ℤ) : ℝ)/10000000000000000=
        ((v : ℝ)/100000000)*((QN e a : ℝ)/100000000) := by push_cast; ring
  by_cases hn : 0≤QN e a
  · have hr : (0 : ℝ)≤(QN e a : ℝ)/100000000 :=
      div_nonneg (by exact_mod_cast hn) (by norm_num)
    simp only [if_pos hn]
    constructor
    · rw [hscale]; exact mul_le_mul_of_nonneg_right hb.1 hr
    · rw [hscale]; exact mul_le_mul_of_nonneg_right hb.2 hr
  · have hr : (QN e a : ℝ)/100000000≤0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (not_le.mp hn).le) (by norm_num)
    simp only [if_neg hn]
    constructor
    · rw [hscale]; exact mul_le_mul_of_nonpos_right hb.2 hr
    · rw [hscale]; exact mul_le_mul_of_nonpos_right hb.1 hr

theorem force_bounds (a : Fin 4) (r : Fin 41) :
    (FL r a : ℝ)/10000000000000000≤force a r ∧
      force a r≤(FH r a : ℝ)/10000000000000000 := by
  rw [← (force_binding r a).1,← (force_binding r a).2]
  simp only [forceLo,forceHi,Int.cast_sum,Finset.sum_div,force]
  exact ⟨Finset.sum_le_sum (fun e _ => (force_term_bounds r a e).1),
    Finset.sum_le_sum (fun e _ => (force_term_bounds r a e).2)⟩

private theorem preconditioned_term_bounds (i r : Fin 41) (a : Fin 4) :
    ((CN i r*(if 0≤CN i r then FL r a else FH r a) : ℤ) : ℝ)/
        1000000000000000000000000 ≤ (C i r : ℝ)*force a r ∧
    (C i r : ℝ)*force a r ≤
      ((CN i r*(if 0≤CN i r then FH r a else FL r a) : ℤ) : ℝ)/
        1000000000000000000000000 := by
  have hb := force_bounds a r
  have hscale (v : ℤ) :
      ((CN i r : ℝ)/100000000)*((v : ℝ)/10000000000000000)=
        ((CN i r*v : ℤ) : ℝ)/1000000000000000000000000 := by push_cast; ring
  have hc : (C i r : ℝ)=(CN i r : ℝ)/100000000 := by
    simp only [C,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  rw [hc]
  by_cases hn : 0≤CN i r
  · have hr : (0 : ℝ)≤(CN i r : ℝ)/100000000 :=
      div_nonneg (by exact_mod_cast hn) (by norm_num)
    simp only [if_pos hn]
    constructor
    · rw [← hscale]; exact mul_le_mul_of_nonneg_left hb.1 hr
    · rw [← hscale]; exact mul_le_mul_of_nonneg_left hb.2 hr
  · have hr : (CN i r : ℝ)/100000000≤0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (not_le.mp hn).le) (by norm_num)
    simp only [if_neg hn]
    constructor
    · rw [← hscale]; exact mul_le_mul_of_nonpos_left hb.2 hr
    · rw [← hscale]; exact mul_le_mul_of_nonpos_left hb.1 hr

theorem correlated_residual (a : Fin 4) (i : Fin 41) :
    actualResidual a i=-(∑ r : Fin 41,(C i r : ℝ)*force a r) := by
  change (∑ r : Fin 41,(C i r : ℝ)*(rhs a r-M.mulVec (centre a) r))=_
  have he (r : Fin 41) : rhs a r-M.mulVec (centre a) r= -force a r := by
    rw [force_identity]; ring
  simp_rw [he,mul_neg]
  rw [Finset.sum_neg_distrib]

theorem actualResidual_bounds (a : Fin 4) (i : Fin 41) :
    (EL i a : ℝ)/1000000000000000000000000≤actualResidual a i ∧
    actualResidual a i≤(EH i a : ℝ)/1000000000000000000000000 := by
  have hlo := Finset.sum_le_sum (fun r (_ : r∈(Finset.univ : Finset (Fin 41))) =>
    (preconditioned_term_bounds i r a).1)
  have hhi := Finset.sum_le_sum (fun r (_ : r∈(Finset.univ : Finset (Fin 41))) =>
    (preconditioned_term_bounds i r a).2)
  rw [correlated_residual]
  simp only [EL,EH,Int.cast_neg,Int.cast_sum,neg_div,Finset.sum_div]
  constructor <;> linarith

theorem actualResidual_norm (a : Fin 4) : ‖actualResidual a‖≤(1 : ℝ)/20000 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤1/20000)]
  intro i
  rw [Real.norm_eq_abs]
  have h := abs_le_max_abs (actualResidual_bounds a i).1 (actualResidual_bounds a i).2
  have hc : max |(EL i a : ℝ)| |(EH i a : ℝ)|≤50000000000000000000 := by
    exact_mod_cast all_residuals i a
  have hs :
      max |((EL i a : ℝ)/1000000000000000000000000)|
        |((EH i a : ℝ)/1000000000000000000000000)|≤(1 : ℝ)/20000 := by
    rw [abs_div,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<1000000000000000000000000),
      max_div_div_right (by norm_num : (0 : ℝ)≤1000000000000000000000000)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<1000000000000000000000000)).mpr
    linarith
  exact h.trans hs

theorem dependentColumn_error (a : Fin 4) :
    ‖dependentColumn a-centre a‖≤(1 : ℝ)/19600 := by
  have h := ResumeLinearSolve.solution_error_bound M (C.map (Rat.cast : ℚ → ℝ))
    (1/50) (by norm_num) actual_contraction (rhs a) (dependentColumn a) (centre a)
    (dependentColumn_solve a)
  have hh := h.trans (div_le_div_of_nonneg_right (actualResidual_norm a)
    (by norm_num : (0 : ℝ)≤1-1/50))
  norm_num at hh ⊢
  exact hh

def dependentBox (i : Fin 41) (a : Fin 4) : RatInterval :=
  intv ((SourceNColumnProposal.YN i a : ℚ)/100000000-1/19600)
    ((SourceNColumnProposal.YN i a : ℚ)/100000000+1/19600)

theorem dependentBox_mem (i : Fin 41) (a : Fin 4) :
    (dependentBox i a).Mem (dependentColumn a i) := by
  have h := (norm_le_pi_norm (dependentColumn a-centre a) i).trans (dependentColumn_error a)
  rw [Real.norm_eq_abs,Pi.sub_apply,abs_le] at h
  change (((SourceNColumnProposal.YN i a : ℚ)/100000000-1/19600 : ℚ) : ℝ)≤
      dependentColumn a i ∧ dependentColumn a i≤
        (((SourceNColumnProposal.YN i a : ℚ)/100000000+1/19600 : ℚ) : ℝ)
  push_cast
  simp only [centre] at h
  constructor <;> linarith [h.1,h.2]

def NBox (e : Fin 45) (a : Fin 4) : RatInterval :=
  match columnEquiv.symm e with
  | .inl i => dependentBox i a
  | .inr b => ofRat (if b=a then 1 else 0)

theorem NBox_mem (e : Fin 45) (a : Fin 4) : (NBox e a).Mem (N e a) := by
  unfold NBox N
  rcases columnEquiv.symm e with i | b
  · exact dependentBox_mem i a
  · by_cases hb : b=a
    · simp only [if_pos hb]; simpa using ofRat_mem (1 : ℚ)
    · simp only [if_neg hb]; simpa using ofRat_mem (0 : ℚ)

end
end N11Formalization.SourceFineNEnclosure
#check @N11Formalization.SourceFineNEnclosure.force_identity
#check @N11Formalization.SourceFineNEnclosure.correlated_residual
#check @N11Formalization.SourceFineNEnclosure.actualResidual_norm
#check @N11Formalization.SourceFineNEnclosure.dependentColumn_error
#check @N11Formalization.SourceFineNEnclosure.NBox_mem
#print axioms N11Formalization.SourceFineNEnclosure.NBox_mem
