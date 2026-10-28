import N11Formalization
set_option autoImplicit false
open N11Formalization
open SourceHarmonicMaximumPrinciple SourceHarmonicSignedIntervals
open SourceActiveFiniteSystem SourceH20CertifiedEnclosure SourceResponseFluxIdentity

#check @SourceHarmonicMaximumPrinciple.negative_part_product
#check @SourceHarmonicMaximumPrinciple.negative_test_zero
#check @SourceHarmonicMaximumPrinciple.negativeColumn_zero
#check @SourceHarmonicMaximumPrinciple.activeH_nonneg
#check @SourceHarmonicMaximumPrinciple.activeH_le_one
#check @SourceHarmonicMaximumPrinciple.H20_bounds
#check @SourceHarmonicMaximumPrinciple.actual_response_anchor_flux
#check @SourceHarmonicMaximumPrinciple.response_offdiag_nonpos
#check @SourceHarmonicMaximumPrinciple.actual_positive_pair_oracle
#check @SourceHarmonicSignedIntervals.clippedHBox_mem
#check @SourceHarmonicSignedIntervals.clippedHBox_lo_ge
#check @SourceHarmonicSignedIntervals.clippedHBox_hi_le
#check @SourceHarmonicSignedIntervals.signedResponseBox_mem
#check @SourceHarmonicSignedIntervals.signedResponseBox_hi_le
#check @SourceHarmonicSignedIntervals.pairWeightBox_mem
#check @SourceHarmonicSignedIntervals.pairWeightBox_lo_nonneg
#check @SourceHarmonicSignedIntervals.lowerPairEnergy_nonneg
#check @SourceHarmonicSignedIntervals.lowerPairEnergy_le_oracle
#check @SourceResponseLinearIntervals.linearCoefficientBox_mem
#check @SourceResponseLinearIntervals.fluxBox_mem
#check @SourceResponseLinearIntervals.jointResponseBox_mem
#check @SourceResponseLinearIntervals.jointResponseBox_lo_ge
#check @SourceResponseLinearIntervals.jointResponseBox_hi_le
#check @SourceResponseLinearIntervals.jointResponseBox_hi_nonpos
#check @SourceResponseLinearIntervals.linearH0Box_mem

#print SourceActiveHarmonicSolve.activeH
#print SourceActiveFiniteSystem.H20
#print SourceHarmonicSignedIntervals.signedResponseBox
#print SourceHarmonicSignedIntervals.pairWeightBox
#print SourceHarmonicSignedIntervals.lowerPairEnergy
#print axioms SourceHarmonicMaximumPrinciple.H20_bounds
#print axioms SourceHarmonicMaximumPrinciple.response_offdiag_nonpos
#print axioms SourceHarmonicMaximumPrinciple.actual_positive_pair_oracle
#print axioms SourceHarmonicSignedIntervals.clippedHBox_mem
#print axioms SourceHarmonicSignedIntervals.signedResponseBox_mem
#print axioms SourceHarmonicSignedIntervals.pairWeightBox_lo_nonneg
#print axioms SourceHarmonicSignedIntervals.lowerPairEnergy_nonneg
#print axioms SourceHarmonicSignedIntervals.lowerPairEnergy_le_oracle
#print axioms SourceResponseLinearIntervals.fluxBox_mem
#print axioms SourceResponseLinearIntervals.jointResponseBox_mem
#print axioms SourceResponseLinearIntervals.linearH0Box_mem

-- All180 actual entries, not the proposed YN/10^8 table.
example (i : Fin 20) (j : Fin 9) :
    (clippedHBox i j).Mem (H20 j i) := clippedHBox_mem i j

-- The two real hub sites remain Fin11, not wrapped Fin9 slots.
example (j : Fin 9) :
    (clippedHBox (Fin.castAdd 9 (9 : Fin 11)) j).Mem
      (SourcePositiveHarmonicConsumer.sourceH
        (HarmonicSourceTransport.srcNode (.inl (9 : Fin 11))) j) := by
  rw [← H20_actual_site j (9 : Fin 11)]
  exact clippedHBox_mem _ _

example (j : Fin 9) :
    (clippedHBox (Fin.castAdd 9 (10 : Fin 11)) j).Mem
      (SourcePositiveHarmonicConsumer.sourceH
        (HarmonicSourceTransport.srcNode (.inl (10 : Fin 11))) j) := by
  rw [← H20_actual_site j (10 : Fin 11)]
  exact clippedHBox_mem _ _

example (i j : Fin 9) (hij : i < j) :
    0 ≤ ((pairWeightBox i j).lo : ℝ) ∧
      ((pairWeightBox i j).lo : ℝ) ≤ -sourceResponse i j := by
  exact ⟨by exact_mod_cast pairWeightBox_lo_nonneg i j (ne_of_lt hij),
    pairWeightBox_lo_bound i j⟩

-- Consume the new LINEAR-in-actualH representation as actual response/H0 input.
-- Intersecting with the old Gram/sign box is guaranteed not to widen it.
example (i j : Fin 9) :
    (SourceResponseLinearIntervals.jointResponseBox i j).Mem (sourceResponse i j) :=
  SourceResponseLinearIntervals.jointResponseBox_mem i j

example (i j : Fin 9) :
    (SourceResponseLinearIntervals.linearH0Box i j).Mem
      (SourceResponseKernelConsumer.H0 i j) :=
  SourceResponseLinearIntervals.linearH0Box_mem i j

example (i j : Fin 9) :
    (SourceResponseLinearIntervals.jointResponseBox i j).Valid := by
  have h := SourceResponseLinearIntervals.jointResponseBox_mem i j
  exact_mod_cast h.1.trans h.2

-- Actual all-angle rational-box energy → actual complete51-row radius consumer.
-- Feasible is explicitly retained; arbitrary Covers production is NOT claimed.
example (θ : Fin 9 → ℝ) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (fun j => circleMap (θ j)) C Z r) :
    lowerPairEnergy θ ≤ r^2 :=
  (lowerPairEnergy_le_oracle θ).trans (ResumeNetwork.oracle_le_feasible hf)

-- Different-representation / known-answer scalar checks.
example : clipUnit (RatInterval.intv (-1/3) (4/3)) = RatInterval.intv 0 1 := by
  norm_num [clipUnit,RatInterval.intv]

example : ((min (-2 : ℝ) 0 - min 3 0)^2 : ℝ) = 4 ∧
    ((-2 : ℝ)-3)*(min (-2) 0-min 3 0) = 10 := by norm_num

-- Negative control: an ungrounded edge permits a negative constant harmonic
-- value. Positivity of edge weights alone does not imply this maximum principle.
example : (1 : ℝ)*((-1)-(-1)) = 0 ∧ ¬ (0 ≤ (-1 : ℝ)) := by norm_num

-- Source/raw2 corresponds to canonical anchor0; wrap8 still uses siteMap8=6.
example : SourceActiveHarmonicSolve.anchorRow (.inl ((2 : Fin 9),(0 : Fin 2))) 0 = -1 := by
  rw [anchorRow_spoke]
  have h : ResumeLocalIncidence.siteMap (2 : Fin 9) = 0 := by decide
  simp only [h,ite_true]

example : SourceActiveHarmonicSolve.anchorRow (.inl ((8 : Fin 9),(1 : Fin 2))) 6 = -1 := by
  rw [anchorRow_spoke]
  have h : ResumeLocalIncidence.siteMap (8 : Fin 9) = 6 := by decide
  simp only [h,ite_true]

example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms SourceExactRoot.source_attainment
