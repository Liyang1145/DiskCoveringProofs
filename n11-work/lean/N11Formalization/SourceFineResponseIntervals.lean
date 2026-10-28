import N11Formalization.SourceFineH20CertifiedEnclosure
import N11Formalization.SourceResponseLinearIntervals

/-! Actual fine H20 and stress feed the SAME linear anchor-flux response
and tangent H0. Intersect the new response box with the accepted old box,
never widening it. Membership does not certify strict augmented coercivity. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineResponseIntervals
open N11Formalization RatInterval ResumeLocalIncidence HarmonicSourceTransport
open SourceActiveLaplacian SourceActiveHarmonicSolve SourceActiveFiniteSystem
open SourceActiveMatrixIntervals SourceFineCompactStressIntervals
open SourceFineH20CertifiedEnclosure SourceHarmonicMaximumPrinciple
open SourceResponseCertifiedIntervals SourceResponseFluxIdentity
noncomputable section

def clippedHBox (i : Fin 20) (j : Fin 9) : RatInterval :=
  SourceHarmonicSignedIntervals.clipUnit (HBox i j)

theorem clippedHBox_mem (i : Fin 20) (j : Fin 9) :
    (clippedHBox i j).Mem (H20 j i) :=
  SourceHarmonicSignedIntervals.clipUnit_mem _ _ (HBox_mem i j)
    (H20_bounds i j).1 (H20_bounds i j).2

def linearCoefficientBox (e : SourceEdge) (j : Fin 9) : RatInterval :=
  add (anchorI e j) (sumI (fun i : Fin 20 =>
    mul (incidenceI e (nodeEquiv.symm i)) (clippedHBox i j)))

theorem linearCoefficientBox_mem (e : SourceEdge) (j : Fin 9) :
    (linearCoefficientBox e j).Mem (K e j) := by
  have hs := sumI_mem (fun i : Fin 20 =>
    mul_mem (incidenceI_mem e (nodeEquiv.symm i)) (clippedHBox_mem i j))
  have he :
      (∑ i : Fin 20,B e (nodeEquiv.symm i)*H20 j i)=
        ∑ v : SrcFree,B e v*activeH v j :=
    nodeEquiv.symm.sum_comp (fun v : SrcFree => B e v*activeH v j)
  rw [he] at hs
  exact add_mem (anchorI_mem e j) hs

def fluxBox (i j : Fin 9) : RatInterval :=
  sumI (fun e : SourceEdge =>
    mul (mul (compact e) (anchorI e i)) (linearCoefficientBox e j))

theorem fluxBox_mem (i j : Fin 9) : (fluxBox i j).Mem (sourceResponse i j) := by
  rw [actual_response_anchor_flux]
  exact sumI_mem (fun e =>
    mul_mem (mul_mem (compact_mem e) (anchorI_mem e i)) (linearCoefficientBox_mem e j))

def jointResponseBox (i j : Fin 9) : RatInterval :=
  SourceResponseLinearIntervals.intersectBox
    (SourceResponseLinearIntervals.jointResponseBox i j) (fluxBox i j)

theorem jointResponseBox_mem (i j : Fin 9) :
    (jointResponseBox i j).Mem (sourceResponse i j) :=
  SourceResponseLinearIntervals.intersectBox_mem _ _ _
    (SourceResponseLinearIntervals.jointResponseBox_mem i j) (fluxBox_mem i j)

theorem response_refines_old (i j : Fin 9) :
    Contains (SourceResponseLinearIntervals.jointResponseBox i j) (jointResponseBox i j) :=
  ⟨le_max_left _ _,min_le_left _ _⟩

def offBox (i j : Fin 9) : RatInterval :=
  mul (mul (ofRat 2) (jointResponseBox i j)) (innerBox i j)

theorem offBox_mem (i j : Fin 9) :
    (offBox i j).Mem (2*sourceResponse i j*
      inner ℝ (FlashLocal.circleTangent (sourceAngle i))
        (FlashLocal.circleTangent (sourceAngle j))) :=
  mul_mem (mul_mem (ofRat_mem 2) (jointResponseBox_mem i j)) (innerBox_mem i j)

def H0Box (i j : Fin 9) : RatInterval :=
  if i=j then neg (sumI (fun k : Fin 9 => if k=i then ofRat 0 else offBox i k))
  else offBox i j

/-- ALL81 memberships of the SAME actual tangent H0, without an input-box premise. -/
theorem H0Box_mem (i j : Fin 9) :
    (H0Box i j).Mem (SourceResponseKernelConsumer.H0 i j) := by
  rw [SourceResponseKernelConsumer.H0_eq_hsrc]
  change (H0Box i j).Mem (FlashResponseHessian.hsrc sourceResponse
    (fun k => FlashLocal.circleTangent (sourceAngle k)) i j)
  by_cases hij : i=j
  · subst j
    simp only [H0Box,ite_true,FlashResponseHessian.hsrc_self]
    have hsum := sumI_mem (fun k : Fin 9 => show
        (if k=i then ofRat 0 else offBox i k).Mem
          (if k=i then 0 else 2*sourceResponse i k*
            inner ℝ (FlashLocal.circleTangent (sourceAngle i))
              (FlashLocal.circleTangent (sourceAngle k))) from by
      by_cases hk : k=i
      · simp only [hk,ite_true]
        simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)
      · simp only [if_neg hk]
        exact offBox_mem i k)
    have he :
        (∑ k : Fin 9,if k=i then 0 else 2*sourceResponse i k*
          inner ℝ (FlashLocal.circleTangent (sourceAngle i))
            (FlashLocal.circleTangent (sourceAngle k)))=
        ∑ k∈Finset.univ.erase i,2*sourceResponse i k*
          inner ℝ (FlashLocal.circleTangent (sourceAngle i))
            (FlashLocal.circleTangent (sourceAngle k)) := by
      have h0 :
          (∑ k∈Finset.univ.erase i,if k=i then 0 else 2*sourceResponse i k*
            inner ℝ (FlashLocal.circleTangent (sourceAngle i))
              (FlashLocal.circleTangent (sourceAngle k)))=
          ∑ k : Fin 9,if k=i then 0 else 2*sourceResponse i k*
            inner ℝ (FlashLocal.circleTangent (sourceAngle i))
              (FlashLocal.circleTangent (sourceAngle k)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        have hki : k=i := by simpa using hk
        simp [hki]
      rw [← h0]
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_neg (Finset.mem_erase.mp hk).1]
    rw [he] at hsum
    exact neg_mem hsum
  · simp only [H0Box,if_neg hij,FlashResponseHessian.hsrc,if_neg hij]
    exact offBox_mem i j

end
end N11Formalization.SourceFineResponseIntervals
#check @N11Formalization.SourceFineResponseIntervals.jointResponseBox_mem
#check @N11Formalization.SourceFineResponseIntervals.response_refines_old
#check @N11Formalization.SourceFineResponseIntervals.H0Box_mem
#print axioms N11Formalization.SourceFineResponseIntervals.H0Box_mem
