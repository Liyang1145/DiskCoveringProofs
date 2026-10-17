import N11Formalization.SourceH20ResidualProposal

/-! Actual9-column harmonic enclosures from certified correlated stress
residuals and the paid ACTUAL contraction1/50. Rational centres are proposals,
not replacements of H20. Source incidence, anchor signs, all scales, residual
memberships and 180 finite bounds are discharged. No response/coercivity
certificate is inferred solely from these input H boxes. -/
set_option autoImplicit false
namespace N11Formalization.SourceH20CertifiedEnclosure
open N11Formalization RatInterval ResumeLocalIncidence HarmonicSourceTransport
open SourceCompactStressIntervals SourceContractionProposal SourceActualContraction
open SourceActiveLaplacian SourceActiveHarmonicSolve SourceActiveFiniteSystem
open SourceH20ResidualProposal
noncomputable section

def centre (j : Fin 9) (i : Fin 20) : ℝ := (YN i j : ℝ)/100000000

private theorem anchorN_cast (e : SourceEdge) (j : Fin 9) :
    (anchorN e j : ℝ)=anchorRow e j := by
  have h := mem_iff.mp (SourceActiveMatrixIntervals.anchorI_mem e j)
  have hlo : ((SourceActiveMatrixIntervals.anchorI e j).lo : ℝ)=(anchorN e j : ℝ) := by
    rcases e with ⟨k,s⟩ | ⟨f,t⟩
    · by_cases he : j=siteMap k <;>
        simp [SourceActiveMatrixIntervals.anchorI,anchorN,ofRat,he]
    · simp [SourceActiveMatrixIntervals.anchorI,anchorN,ofRat]
  have hhi : ((SourceActiveMatrixIntervals.anchorI e j).hi : ℝ)=(anchorN e j : ℝ) := by
    rcases e with ⟨k,s⟩ | ⟨f,t⟩
    · by_cases he : j=siteMap k <;>
        simp [SourceActiveMatrixIntervals.anchorI,anchorN,ofRat,he]
    · simp [SourceActiveMatrixIntervals.anchorI,anchorN,ofRat]
  rw [hlo,hhi] at h
  linarith

private theorem coefficientN_real (e : SourceEdge) (j : Fin 9) :
    anchorRow e j+(∑ k : Fin 20,B e (nodeEquiv.symm k)*centre j k)=
      (coefficientN e j : ℝ)/100000000 := by
  have hsum :
      (∑ k : Fin 20,B e (nodeEquiv.symm k)*centre j k)=
        ((∑ k : Fin 20,incidenceZ e (nodeEquiv.symm k)*YN k j : ℤ) : ℝ)/
          100000000 := by
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [B,centre]
    ring
  rw [hsum,← anchorN_cast e j]
  simp only [coefficientN,Int.cast_add,Int.cast_mul,Int.cast_ofNat,add_div]
  ring

private theorem projectionN_real (i : Fin 20) (e : SourceEdge) :
    (∑ k : Fin 20,(C i k : ℝ)*B e (nodeEquiv.symm k))=
      (projectionN i e : ℝ)/100000000 := by
  unfold projectionN
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  simp only [C,B,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  ring

private theorem matrix_expand (i k : Fin 20) :
    matrix20 i k=∑ e : SourceEdge,
      SourceSignedStressAssembly.stress e*B e (nodeEquiv.symm i)*B e (nodeEquiv.symm k) := rfl

private theorem rhs_expand (i : Fin 20) (j : Fin 9) :
    rhs20 j i=-(∑ e : SourceEdge,
      SourceSignedStressAssembly.stress e*B e (nodeEquiv.symm i)*anchorRow e j) := rfl

private theorem unconditioned_residual (j : Fin 9) (i : Fin 20) :
    rhs20 j i-matrix20.mulVec (centre j) i=
      -(∑ e : SourceEdge,SourceSignedStressAssembly.stress e*B e (nodeEquiv.symm i)*
        ((coefficientN e j : ℝ)/100000000)) := by
  have hmat :
      matrix20.mulVec (centre j) i=
        ∑ e : SourceEdge,SourceSignedStressAssembly.stress e*B e (nodeEquiv.symm i)*
          (∑ k : Fin 20,B e (nodeEquiv.symm k)*centre j k) := by
    simp only [Matrix.mulVec,dotProduct,matrix_expand,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [rhs_expand,hmat]
  simp_rw [← coefficientN_real,mul_add,Finset.sum_add_distrib]
  ring

def actualResidual (j : Fin 9) : Fin 20 → ℝ :=
  (C.map (Rat.cast : ℚ → ℝ)).mulVec (rhs20 j-matrix20.mulVec (centre j))

private theorem correlated_residual (j : Fin 9) (i : Fin 20) :
    actualResidual j i=
      -(∑ e : SourceEdge,SourceSignedStressAssembly.stress e*
        (multiplierN i j e : ℝ)/10000000000000000) := by
  unfold actualResidual
  simp only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.sub_apply]
  change (∑ k : Fin 20,(C i k : ℝ)*
    (rhs20 j k-matrix20.mulVec (centre j) k))=_
  simp_rw [unconditioned_residual,mul_neg,Finset.mul_sum]
  rw [Finset.sum_neg_distrib,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  have hf :
      (∑ k : Fin 20,(C i k : ℝ)*
        (SourceSignedStressAssembly.stress e*B e (nodeEquiv.symm k)*
          ((coefficientN e j : ℝ)/100000000)))=
      SourceSignedStressAssembly.stress e*((coefficientN e j : ℝ)/100000000)*
        (∑ k : Fin 20,(C i k : ℝ)*B e (nodeEquiv.symm k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hf,projectionN_real]
  simp only [multiplierN,Int.cast_mul]
  ring

private theorem residual_term_bounds (e : SourceEdge) (i : Fin 20) (j : Fin 9) :
    ((if 0 ≤ multiplierN i j e then loN (srcFlat e)*multiplierN i j e
      else hiN (srcFlat e)*multiplierN i j e : ℤ) : ℝ)/
      1000000000000000000000000 ≤
      SourceSignedStressAssembly.stress e*(multiplierN i j e : ℝ)/10000000000000000 ∧
    SourceSignedStressAssembly.stress e*(multiplierN i j e : ℝ)/10000000000000000 ≤
      ((if 0 ≤ multiplierN i j e then hiN (srcFlat e)*multiplierN i j e
        else loN (srcFlat e)*multiplierN i j e : ℤ) : ℝ)/
          1000000000000000000000000 := by
  have hs := mem_iff.mp (compact_mem e)
  simp only [SourceCompactStressIntervals.compact,intv] at hs
  push_cast at hs
  have hscale (a : ℝ) :
      (a/100000000)*((multiplierN i j e : ℝ)/10000000000000000)=
        a*(multiplierN i j e : ℝ)/1000000000000000000000000 := by ring
  by_cases hz : 0 ≤ multiplierN i j e
  · have hr : (0 : ℝ)≤(multiplierN i j e : ℝ)/10000000000000000 := by
      exact div_nonneg (by exact_mod_cast hz) (by norm_num)
    simp only [if_pos hz,Int.cast_mul]
    constructor
    · simpa only [hscale,← mul_div_assoc] using mul_le_mul_of_nonneg_right hs.1 hr
    · simpa only [hscale,← mul_div_assoc] using mul_le_mul_of_nonneg_right hs.2 hr
  · have hr : (multiplierN i j e : ℝ)/10000000000000000≤0 := by
      exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (not_le.mp hz).le) (by norm_num)
    simp only [if_neg hz,Int.cast_mul]
    constructor
    · simpa only [hscale,← mul_div_assoc] using mul_le_mul_of_nonpos_right hs.2 hr
    · simpa only [hscale,← mul_div_assoc] using mul_le_mul_of_nonpos_right hs.1 hr

theorem actualResidual_bounds (j : Fin 9) (i : Fin 20) :
    (EL i j : ℝ)/1000000000000000000000000≤actualResidual j i ∧
    actualResidual j i≤(EH i j : ℝ)/1000000000000000000000000 := by
  have hlo := Finset.sum_le_sum (fun e (_ : e∈(Finset.univ : Finset SourceEdge)) =>
    (residual_term_bounds e i j).1)
  have hhi := Finset.sum_le_sum (fun e (_ : e∈(Finset.univ : Finset SourceEdge)) =>
    (residual_term_bounds e i j).2)
  rw [correlated_residual]
  simp only [EL,EH,Int.cast_neg,Int.cast_sum,neg_div,Finset.sum_div]
  constructor <;> linarith

theorem actualResidual_norm (j : Fin 9) : ‖actualResidual j‖≤(3 : ℝ)/1000 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤3/1000)]
  intro i
  rw [Real.norm_eq_abs]
  have h := abs_le_max_abs (actualResidual_bounds j i).1 (actualResidual_bounds j i).2
  have hc :
      max |(EL i j : ℝ)| |(EH i j : ℝ)|≤3000000000000000000000 := by
    exact_mod_cast all_columns i j
  have hs :
      max |((EL i j : ℝ)/1000000000000000000000000)|
        |((EH i j : ℝ)/1000000000000000000000000)|≤(3 : ℝ)/1000 := by
    rw [abs_div,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<1000000000000000000000000),
      max_div_div_right (by norm_num : (0 : ℝ)≤1000000000000000000000000)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<1000000000000000000000000)).mpr
    linarith
  exact h.trans hs

/-- ALL9 actual columns enclosed unconditionally around rational proposals.
The current coarse boxes have radius3/980; no exact rational solution or
sourceResponse/coercivity enclosure is implied by this input statement. -/
theorem H20_error_certified (j : Fin 9) : ‖H20 j-centre j‖≤(3 : ℝ)/980 := by
  have h := (H20_error_bound j (centre j)).trans
    (div_le_div_of_nonneg_right (actualResidual_norm j)
      (by norm_num : (0 : ℝ)≤1-1/50))
  norm_num at h ⊢
  exact h

theorem H20_coordinate_certified (j : Fin 9) (i : Fin 20) :
    centre j i-(3 : ℝ)/980≤H20 j i ∧ H20 j i≤centre j i+(3 : ℝ)/980 := by
  have h := (norm_le_pi_norm (H20 j-centre j) i).trans (H20_error_certified j)
  rw [Real.norm_eq_abs,Pi.sub_apply,abs_le] at h
  constructor <;> linarith [h.1,h.2]

def HBox (i : Fin 20) (j : Fin 9) : RatInterval :=
  intv ((YN i j : ℚ)/100000000-3/980) ((YN i j : ℚ)/100000000+3/980)

theorem HBox_mem (i : Fin 20) (j : Fin 9) : (HBox i j).Mem (H20 j i) := by
  have h := H20_coordinate_certified j i
  simpa only [HBox,mem_iff,intv,centre,Rat.cast_sub,Rat.cast_add,
    Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] using h

end
end N11Formalization.SourceH20CertifiedEnclosure
#check @N11Formalization.SourceH20CertifiedEnclosure.actualResidual_norm
#check @N11Formalization.SourceH20CertifiedEnclosure.H20_error_certified
#check @N11Formalization.SourceH20CertifiedEnclosure.HBox_mem
#print axioms N11Formalization.SourceH20CertifiedEnclosure.HBox_mem
