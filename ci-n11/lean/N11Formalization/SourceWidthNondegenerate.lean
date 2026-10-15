import Mathlib
import N11Formalization.WidthRadialDerivative
import N11Formalization.FanFoutPos
import N11Formalization.TCChartStationarityRoot
import N11Formalization.F1.BallD35C13
set_option autoImplicit false
namespace N11Formalization.SourceWidthNondegenerate
open N11Formalization WidthRadialDerivative
noncomputable section

/-- All nine source half-widths lie strictly between zero and pi/2. -/
theorem source_width_bounds (k : Fin 9) :
    0 < angleVec SourceExactRoot.sourceRoot k ∧
      angleVec SourceExactRoot.sourceRoot k < Real.pi/2 := by
  let u := SourceExactRoot.sourceRoot
  have l0 := (SourceExactRoot.sourceRoot_mem.1 0).1
  have l1 := (SourceExactRoot.sourceRoot_mem.1 1).1
  have l2 := (SourceExactRoot.sourceRoot_mem.1 2).1
  have l3 := (SourceExactRoot.sourceRoot_mem.1 3).1
  have h0 := (SourceExactRoot.sourceRoot_mem.1 0).2
  have h1 := (SourceExactRoot.sourceRoot_mem.1 1).2
  have h2 := (SourceExactRoot.sourceRoot_mem.1 2).2
  have h3 := (SourceExactRoot.sourceRoot_mem.1 3).2
  rw [ndBoxLo_0] at l0
  rw [ndBoxLo_1] at l1
  rw [ndBoxLo_2] at l2
  rw [ndBoxLo_3] at l3
  rw [ndBoxHi_0] at h0
  rw [ndBoxHi_1] at h1
  rw [ndBoxHi_2] at h2
  rw [ndBoxHi_3] at h3
  norm_num at l0 l1 l2 l3 h0 h1 h2 h3
  have hp := Real.pi_gt_three
  have hp4 := Real.pi_lt_four
  fin_cases k <;> simp only [angleVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.reduceFinMk] <;> constructor <;> linarith

/-- Strict source radicands come from the certified interval lower bounds, not an interval containing 0. -/
theorem source_radicand_pos (k : Fin 9) :
    0 < (SourceExactRoot.sourceRoot 6)^2 - Real.sin (angleVec SourceExactRoot.sourceRoot k)^2 := by
  have hl := (wkBox_mem TCChartStationarityRoot.sourceRoot_mem_ball k).1
  have hp : (0 : ℝ) < (((wkBox k).lo : ℚ) : ℝ) := by exact_mod_cast wkBox_pos k
  simpa only [pow_two] using lt_of_lt_of_le hp hl

/-- Actual source half-width radial derivative is strictly positive at every ring index. -/
theorem source_widthSlope_pos (k : Fin 9) :
    0 < widthSlope (SourceExactRoot.sourceRoot 6) (angleVec SourceExactRoot.sourceRoot k) := by
  have ha := source_width_bounds k
  have hsin := Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos])
  have hcos := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha.2⟩
  have hr := FanFoutPos.radius_sq_lt _ SourceExactRoot.sourceRoot_mem
  exact widthSlope_pos _ _ hsin hcos (source_radicand_pos k) (by linarith)

/-- Scalar derivative consumer at every actual source half-width; radius fixed to the SAME root. -/
theorem source_width_hasDerivAt (k : Fin 9) :
    HasDerivAt (rhoMinus (SourceExactRoot.sourceRoot 6))
      (widthSlope (SourceExactRoot.sourceRoot 6) (angleVec SourceExactRoot.sourceRoot k))
      (angleVec SourceExactRoot.sourceRoot k) :=
  hasDerivAt_rhoMinus_width _ _ (source_radicand_pos k)

/-- Scalar C1 in a neighborhood of each actual source half-width. -/
theorem source_width_contDiffAt (k : Fin 9) :
    ContDiffAt ℝ 1 (rhoMinus (SourceExactRoot.sourceRoot 6))
      (angleVec SourceExactRoot.sourceRoot k) := by
  have hc : ContDiffAt ℝ 1 Real.cos (angleVec SourceExactRoot.sourceRoot k) :=
    Real.contDiff_cos.contDiffAt
  have hs : ContDiffAt ℝ 1 Real.sin (angleVec SourceExactRoot.sourceRoot k) :=
    Real.contDiff_sin.contDiffAt
  have hrad : ContDiffAt ℝ 1
      (fun a => (SourceExactRoot.sourceRoot 6)^2 - Real.sin a^2)
      (angleVec SourceExactRoot.sourceRoot k) := contDiffAt_const.sub (hs.pow 2)
  exact hc.sub (hrad.sqrt (ne_of_gt (source_radicand_pos k)))

theorem source_width_hasStrictDerivAt (k : Fin 9) :
    HasStrictDerivAt (rhoMinus (SourceExactRoot.sourceRoot 6))
      (widthSlope (SourceExactRoot.sourceRoot 6) (angleVec SourceExactRoot.sourceRoot k))
      (angleVec SourceExactRoot.sourceRoot k) :=
  (source_width_contDiffAt k).hasStrictDerivAt' (source_width_hasDerivAt k) (by norm_num)

/-- Consumer-level local inverse of HALF-WIDTH -> RADIUS, fixing the SAME source R.
This does not yet prove the coupled 12D frame-to-Cartesian coordinate inverse. -/
theorem source_width_local_inverse (k : Fin 9) :
    ∃ g : ℝ → ℝ,
      (∀ᶠ a in nhds (angleVec SourceExactRoot.sourceRoot k),
        g (rhoMinus (SourceExactRoot.sourceRoot 6) a) = a) ∧
      (∀ᶠ r in nhds (rhoK SourceExactRoot.sourceRoot k),
        rhoMinus (SourceExactRoot.sourceRoot 6) (g r) = r) ∧
      HasStrictDerivAt g
        (widthSlope (SourceExactRoot.sourceRoot 6) (angleVec SourceExactRoot.sourceRoot k))⁻¹
        (rhoK SourceExactRoot.sourceRoot k) := by
  have hd := source_width_hasStrictDerivAt k
  have hn := ne_of_gt (source_widthSlope_pos k)
  refine ⟨hd.localInverse _ _ _ hn, hd.eventually_left_inverse hn, ?_, ?_⟩
  · exact hd.eventually_right_inverse hn
  · exact hd.to_localInverse hn

end
end N11Formalization.SourceWidthNondegenerate
#print N11Formalization.SourceWidthNondegenerate.source_widthSlope_pos
#print axioms N11Formalization.SourceWidthNondegenerate.source_widthSlope_pos
#print axioms N11Formalization.SourceWidthNondegenerate.source_width_hasDerivAt
#check @N11Formalization.SourceWidthNondegenerate.source_width_local_inverse
#print axioms N11Formalization.SourceWidthNondegenerate.source_width_local_inverse
