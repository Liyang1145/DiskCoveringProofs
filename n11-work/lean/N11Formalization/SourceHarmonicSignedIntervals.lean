import N11Formalization.SourceHarmonicMaximumPrinciple
import N11Formalization.SourceResponseCertifiedIntervals

/-! Consume actual analytic signs in the existing SAME-source rational boxes.
All180 H boxes may be intersected with [0,1]; actual response off-diagonal
upper endpoints may be clipped at zero. The resulting actual36 pair-weight
lower endpoints are rational and nonnegative and bound the51-edge oracle for
ALL angular tuples. No adequacy/sharpness/nonzero endpoint claim is made. -/
set_option autoImplicit false
namespace N11Formalization.SourceHarmonicSignedIntervals
open N11Formalization RatInterval SourceActiveFiniteSystem
open SourceH20CertifiedEnclosure SourceResponseCertifiedIntervals
open SourceResponseFluxIdentity SourceHarmonicMaximumPrinciple
noncomputable section

def clipUnit (I : RatInterval) : RatInterval :=
  intv (max 0 I.lo) (min 1 I.hi)

theorem clipUnit_mem (I : RatInterval) (x : ℝ) (hx : I.Mem x)
    (h0 : 0 ≤ x) (h1 : x ≤ 1) : (clipUnit I).Mem x := by
  change ((max (0 : ℚ) I.lo : ℚ) : ℝ) ≤ x ∧
    x ≤ ((min (1 : ℚ) I.hi : ℚ) : ℝ)
  rw [Rat.cast_max,Rat.cast_min,Rat.cast_zero,Rat.cast_one]
  exact ⟨max_le h0 hx.1,le_min h1 hx.2⟩

def clippedHBox (i : Fin 20) (j : Fin 9) : RatInterval := clipUnit (HBox i j)

theorem clippedHBox_mem (i : Fin 20) (j : Fin 9) :
    (clippedHBox i j).Mem (H20 j i) :=
  clipUnit_mem _ _ (HBox_mem i j) (H20_bounds i j).1 (H20_bounds i j).2

theorem clippedHBox_lo_ge (i : Fin 20) (j : Fin 9) :
    (HBox i j).lo ≤ (clippedHBox i j).lo :=
  le_max_right _ _

theorem clippedHBox_hi_le (i : Fin 20) (j : Fin 9) :
    (clippedHBox i j).hi ≤ (HBox i j).hi :=
  min_le_right _ _

def signedResponseBox (i j : Fin 9) : RatInterval :=
  if i = j then responseBox i j
  else intv (responseBox i j).lo (min 0 (responseBox i j).hi)

theorem signedResponseBox_mem (i j : Fin 9) :
    (signedResponseBox i j).Mem (sourceResponse i j) := by
  by_cases hij : i = j
  · simp only [signedResponseBox,if_pos hij]
    exact responseBox_mem i j
  · simp only [signedResponseBox,if_neg hij]
    change ((responseBox i j).lo : ℝ) ≤ sourceResponse i j ∧
      sourceResponse i j ≤ ((min (0 : ℚ) (responseBox i j).hi : ℚ) : ℝ)
    rw [Rat.cast_min,Rat.cast_zero]
    exact ⟨(responseBox_mem i j).1,
      le_min (response_offdiag_nonpos i j hij) (responseBox_mem i j).2⟩

theorem signedResponseBox_lo_eq (i j : Fin 9) :
    (signedResponseBox i j).lo = (responseBox i j).lo := by
  by_cases hij : i = j <;> simp [signedResponseBox,hij,intv]

theorem signedResponseBox_hi_le (i j : Fin 9) :
    (signedResponseBox i j).hi ≤ (responseBox i j).hi := by
  by_cases hij : i = j
  · simp [signedResponseBox,hij]
  · simp only [signedResponseBox,if_neg hij]
    exact min_le_right _ _

def pairWeightBox (i j : Fin 9) : RatInterval := neg (signedResponseBox i j)

theorem pairWeightBox_mem (i j : Fin 9) :
    (pairWeightBox i j).Mem (-sourceResponse i j) :=
  neg_mem (signedResponseBox_mem i j)

theorem pairWeightBox_lo_nonneg (i j : Fin 9) (hij : i ≠ j) :
    0 ≤ (pairWeightBox i j).lo := by
  change 0 ≤ -(signedResponseBox i j).hi
  simp only [signedResponseBox,if_neg hij]
  exact neg_nonneg.mpr (min_le_left _ _)

theorem pairWeightBox_lo_bound (i j : Fin 9) :
    ((pairWeightBox i j).lo : ℝ) ≤ -sourceResponse i j :=
  (pairWeightBox_mem i j).1

def lowerPairEnergy (θ : Fin 9 → ℝ) : ℝ :=
  2 * ∑ i : Fin 9, ∑ j : Fin 9, if i < j then
    ((pairWeightBox i j).lo : ℝ) * (1 - Real.cos (θ i - θ j)) else 0

/-- Real consumer of the actual analytic sign and actual rational membership:
ALL36 rational nonnegative pair coefficients give a universal oracle lower
bound. Not a terminal, local coercivity or unrestricted-cover lower bound. -/
theorem lowerPairEnergy_le_oracle (θ : Fin 9 → ℝ) :
    lowerPairEnergy θ ≤ ResumeNetwork.V2 (fun j => circleMap (θ j)) := by
  apply le_trans _ (SourceActiveAffineResponse.actual_pair_le_oracle θ)
  unfold lowerPairEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    exact mul_le_mul_of_nonneg_right (pairWeightBox_lo_bound i j)
      (sub_nonneg.mpr (Real.cos_le_one _))
  · simp only [if_neg hij,le_refl]

theorem lowerPairEnergy_nonneg (θ : Fin 9 → ℝ) : 0 ≤ lowerPairEnergy θ := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    exact mul_nonneg (by exact_mod_cast pairWeightBox_lo_nonneg i j (ne_of_lt hij))
      (sub_nonneg.mpr (Real.cos_le_one _))
  · simp only [if_neg hij,le_refl]

end
end N11Formalization.SourceHarmonicSignedIntervals
#check @N11Formalization.SourceHarmonicSignedIntervals.clippedHBox_mem
#check @N11Formalization.SourceHarmonicSignedIntervals.signedResponseBox_mem
#check @N11Formalization.SourceHarmonicSignedIntervals.pairWeightBox_lo_nonneg
#check @N11Formalization.SourceHarmonicSignedIntervals.lowerPairEnergy_le_oracle
#print axioms N11Formalization.SourceHarmonicSignedIntervals.clippedHBox_mem
#print axioms N11Formalization.SourceHarmonicSignedIntervals.lowerPairEnergy_le_oracle
