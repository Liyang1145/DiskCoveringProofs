import N11Formalization.SourceH20CertifiedEnclosure
import N11Formalization.SourceActiveAffineResponse

/-! Unconditional enclosure of SAME actual9x9 sourceResponse and tangent H0
from certified actual H20 boxes. No supplied H/response interval membership,
no floating matrix identity. Current coarse boxes are NOT asserted to satisfy
strict mixed-coercivity row checks; refinement/quality checks remain separate. -/
set_option autoImplicit false
namespace N11Formalization.SourceResponseCertifiedIntervals
open N11Formalization RatInterval ResumeLocalIncidence HarmonicSourceTransport
open SourceActiveLaplacian SourceActiveHarmonicSolve SourceActiveFiniteSystem
open SourceH20CertifiedEnclosure SourceH20ResidualProposal
open SourceCompactStressIntervals SourceActiveMatrixIntervals
open SourceResponseFluxIdentity SourceRadialFluxConsumer
noncomputable section

def coefficientBox (e : SourceEdge) (j : Fin 9) : RatInterval :=
  add (anchorI e j) (sumI (fun i : Fin 20 =>
    mul (incidenceI e (nodeEquiv.symm i)) (HBox i j)))

theorem coefficientBox_mem (e : SourceEdge) (j : Fin 9) :
    (coefficientBox e j).Mem (K e j) := by
  have hs := sumI_mem (fun i : Fin 20 =>
    mul_mem (incidenceI_mem e (nodeEquiv.symm i)) (HBox_mem i j))
  have he :
      (∑ i : Fin 20,B e (nodeEquiv.symm i)*H20 j i)=
        ∑ v : SrcFree,B e v*activeH v j := by
    have h := nodeEquiv.symm.sum_comp (fun v : SrcFree => B e v*activeH v j)
    exact h
  rw [he] at hs
  exact add_mem (anchorI_mem e j) hs

def responseBox (i j : Fin 9) : RatInterval :=
  sumI (fun e : SourceEdge =>
    mul (mul (compact e) (coefficientBox e i)) (coefficientBox e j))

/-- ALL81 entries of the actual response, not a C911/proposed midpoint table. -/
theorem responseBox_mem (i j : Fin 9) :
    (responseBox i j).Mem (sourceResponse i j) := by
  rw [SourceActiveAffineResponse.response_active]
  exact sumI_mem (fun e => mul_mem
    (mul_mem (compact_mem e) (coefficientBox_mem e i)) (coefficientBox_mem e j))

def anchorBox (i : Fin 9) (q : Fin 2) : RatInterval :=
  ndArcBox ndBox (FlashRootNetwork.rawOfRing i) q

theorem anchorBox_mem (i : Fin 9) (q : Fin 2) :
    (anchorBox i q).Mem (SourcePositiveHarmonicConsumer.sourceAnchors i q) :=
  ndArcBox_mem (ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball) _ _

def innerBox (i j : Fin 9) : RatInterval :=
  add (mul (anchorBox i 0) (anchorBox j 0)) (mul (anchorBox i 1) (anchorBox j 1))

theorem innerBox_mem (i j : Fin 9) :
    (innerBox i j).Mem
      (inner ℝ (FlashLocal.circleTangent (sourceAngle i))
        (FlashLocal.circleTangent (sourceAngle j))) := by
  rw [FlashResponseHessianFlux.circleTangent_inner_eq_circleMap,
    ← sourceAnchors_circle i,← sourceAnchors_circle j,PinTangentGeometry.inner_coords]
  exact add_mem (mul_mem (anchorBox_mem i 0) (anchorBox_mem j 0))
    (mul_mem (anchorBox_mem i 1) (anchorBox_mem j 1))

def offBox (i j : Fin 9) : RatInterval :=
  mul (mul (ofRat 2) (responseBox i j)) (innerBox i j)

theorem offBox_mem (i j : Fin 9) :
    (offBox i j).Mem (2*sourceResponse i j*
      inner ℝ (FlashLocal.circleTangent (sourceAngle i))
        (FlashLocal.circleTangent (sourceAngle j))) :=
  mul_mem (mul_mem (ofRat_mem 2) (responseBox_mem i j)) (innerBox_mem i j)

def H0Box (i j : Fin 9) : RatInterval :=
  if i=j then
    neg (sumI (fun k : Fin 9 => if k=i then ofRat 0 else offBox i k))
  else offBox i j

/-- ALL81 actual tangent-H0 entry memberships. Membership alone does NOT pay
strict congruence dominance, adaptive N/G bounds or mixed remainders. -/
theorem H0Box_mem (i j : Fin 9) :
    (H0Box i j).Mem (SourceResponseKernelConsumer.H0 i j) := by
  rw [SourceResponseKernelConsumer.H0_eq_hsrc]
  change (H0Box i j).Mem
    (FlashResponseHessian.hsrc sourceResponse
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
end N11Formalization.SourceResponseCertifiedIntervals
#check @N11Formalization.SourceResponseCertifiedIntervals.responseBox_mem
#check @N11Formalization.SourceResponseCertifiedIntervals.H0Box_mem
#print axioms N11Formalization.SourceResponseCertifiedIntervals.responseBox_mem
#print axioms N11Formalization.SourceResponseCertifiedIntervals.H0Box_mem
