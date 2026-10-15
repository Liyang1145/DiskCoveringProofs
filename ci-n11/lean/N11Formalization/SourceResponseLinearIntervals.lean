import N11Formalization.SourceHarmonicSignedIntervals

/-! A second, LINEAR-in-actualH enclosure of SAME actual sourceResponse:
the paid Gram=anchor-flux identity avoids products of two independently
enclosed harmonic columns. Intersect with the already-certified Gram/sign
box, then transport the actual response to actual tangent H0. All81 input
memberships and endpoint containment are paid; numerical adequacy, N/G,
strict congruence dominance and mixed/remainder certificates remain separate. -/
set_option autoImplicit false
namespace N11Formalization.SourceResponseLinearIntervals
open N11Formalization RatInterval ResumeLocalIncidence HarmonicSourceTransport
open SourceActiveLaplacian SourceActiveHarmonicSolve SourceActiveFiniteSystem
open SourceActiveMatrixIntervals SourceCompactStressIntervals
open SourceHarmonicMaximumPrinciple SourceHarmonicSignedIntervals
open SourceResponseCertifiedIntervals SourceResponseFluxIdentity
noncomputable section

def linearCoefficientBox (e : SourceEdge) (j : Fin 9) : RatInterval :=
  add (anchorI e j) (sumI (fun i : Fin 20 =>
    mul (incidenceI e (nodeEquiv.symm i)) (clippedHBox i j)))

theorem linearCoefficientBox_mem (e : SourceEdge) (j : Fin 9) :
    (linearCoefficientBox e j).Mem (K e j) := by
  have hs := sumI_mem (fun i : Fin 20 =>
    mul_mem (incidenceI_mem e (nodeEquiv.symm i)) (clippedHBox_mem i j))
  have he :
      (∑ i : Fin 20, B e (nodeEquiv.symm i) * H20 j i) =
        ∑ v : SrcFree, B e v * activeH v j :=
    nodeEquiv.symm.sum_comp (fun v : SrcFree => B e v * activeH v j)
  rw [he] at hs
  exact add_mem (anchorI_mem e j) hs

def fluxBox (i j : Fin 9) : RatInterval :=
  sumI (fun e : SourceEdge =>
    mul (mul (compact e) (anchorI e i)) (linearCoefficientBox e j))

/-- ALL81 real response entries enclosed via the actual linear anchor flux.
No hflux/hH/response identity premise is supplied. -/
theorem fluxBox_mem (i j : Fin 9) : (fluxBox i j).Mem (sourceResponse i j) := by
  rw [actual_response_anchor_flux]
  exact sumI_mem (fun e =>
    mul_mem (mul_mem (compact_mem e) (anchorI_mem e i)) (linearCoefficientBox_mem e j))

def intersectBox (I J : RatInterval) : RatInterval :=
  intv (max I.lo J.lo) (min I.hi J.hi)

theorem intersectBox_mem (I J : RatInterval) (x : ℝ)
    (hI : I.Mem x) (hJ : J.Mem x) : (intersectBox I J).Mem x := by
  change ((max I.lo J.lo : ℚ) : ℝ) ≤ x ∧ x ≤ ((min I.hi J.hi : ℚ) : ℝ)
  rw [Rat.cast_max,Rat.cast_min]
  exact ⟨max_le hI.1 hJ.1,le_min hI.2 hJ.2⟩

def jointResponseBox (i j : Fin 9) : RatInterval :=
  intersectBox (signedResponseBox i j) (fluxBox i j)

theorem jointResponseBox_mem (i j : Fin 9) :
    (jointResponseBox i j).Mem (sourceResponse i j) :=
  intersectBox_mem _ _ _ (signedResponseBox_mem i j) (fluxBox_mem i j)

theorem jointResponseBox_lo_ge (i j : Fin 9) :
    (signedResponseBox i j).lo ≤ (jointResponseBox i j).lo :=
  le_max_left _ _

theorem jointResponseBox_hi_le (i j : Fin 9) :
    (jointResponseBox i j).hi ≤ (signedResponseBox i j).hi :=
  min_le_left _ _

theorem jointResponseBox_hi_nonpos (i j : Fin 9) (hij : i ≠ j) :
    (jointResponseBox i j).hi ≤ 0 := by
  apply (jointResponseBox_hi_le i j).trans
  simp only [signedResponseBox,if_neg hij]
  exact min_le_left _ _

def linearOffBox (i j : Fin 9) : RatInterval :=
  mul (mul (ofRat 2) (jointResponseBox i j)) (innerBox i j)

theorem linearOffBox_mem (i j : Fin 9) :
    (linearOffBox i j).Mem (2 * sourceResponse i j *
      inner ℝ (FlashLocal.circleTangent (sourceAngle i))
        (FlashLocal.circleTangent (sourceAngle j))) :=
  mul_mem (mul_mem (ofRat_mem 2) (jointResponseBox_mem i j)) (innerBox_mem i j)

def linearH0Box (i j : Fin 9) : RatInterval :=
  if i = j then neg (sumI (fun k : Fin 9 => if k = i then ofRat 0 else linearOffBox i k))
  else linearOffBox i j

/-- ALL81 actual tangent-H0 input memberships; no H0-PSD or coercivity
claim follows from this enclosure. -/
theorem linearH0Box_mem (i j : Fin 9) :
    (linearH0Box i j).Mem (SourceResponseKernelConsumer.H0 i j) := by
  rw [SourceResponseKernelConsumer.H0_eq_hsrc]
  change (linearH0Box i j).Mem (FlashResponseHessian.hsrc sourceResponse
    (fun k => FlashLocal.circleTangent (sourceAngle k)) i j)
  by_cases hij : i = j
  · subst j
    simp only [linearH0Box,ite_true,FlashResponseHessian.hsrc_self]
    have hsum := sumI_mem (fun k : Fin 9 => show
        (if k = i then ofRat 0 else linearOffBox i k).Mem
          (if k = i then 0 else 2 * sourceResponse i k *
            inner ℝ (FlashLocal.circleTangent (sourceAngle i))
              (FlashLocal.circleTangent (sourceAngle k))) from by
      by_cases hk : k = i
      · simp only [hk,ite_true]
        simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)
      · simp only [if_neg hk]
        exact linearOffBox_mem i k)
    have he :
        (∑ k : Fin 9, if k = i then 0 else 2 * sourceResponse i k *
          inner ℝ (FlashLocal.circleTangent (sourceAngle i))
            (FlashLocal.circleTangent (sourceAngle k))) =
        ∑ k ∈ Finset.univ.erase i, 2 * sourceResponse i k *
          inner ℝ (FlashLocal.circleTangent (sourceAngle i))
            (FlashLocal.circleTangent (sourceAngle k)) := by
      have h0 :
          (∑ k ∈ Finset.univ.erase i, if k = i then 0 else 2 * sourceResponse i k *
            inner ℝ (FlashLocal.circleTangent (sourceAngle i))
              (FlashLocal.circleTangent (sourceAngle k))) =
          ∑ k : Fin 9, if k = i then 0 else 2 * sourceResponse i k *
            inner ℝ (FlashLocal.circleTangent (sourceAngle i))
              (FlashLocal.circleTangent (sourceAngle k)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        have hki : k = i := by simpa using hk
        simp [hki]
      rw [← h0]
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_neg (Finset.mem_erase.mp hk).1]
    rw [he] at hsum
    exact neg_mem hsum
  · simp only [linearH0Box,if_neg hij,FlashResponseHessian.hsrc,if_neg hij]
    exact linearOffBox_mem i j

end
end N11Formalization.SourceResponseLinearIntervals
#check @N11Formalization.SourceResponseLinearIntervals.fluxBox_mem
#check @N11Formalization.SourceResponseLinearIntervals.jointResponseBox_mem
#check @N11Formalization.SourceResponseLinearIntervals.linearH0Box_mem
#print axioms N11Formalization.SourceResponseLinearIntervals.fluxBox_mem
#print axioms N11Formalization.SourceResponseLinearIntervals.linearH0Box_mem
