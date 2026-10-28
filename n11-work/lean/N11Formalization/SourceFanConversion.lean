import N11Formalization.SourceFanLengthCovector

/-!
Correct LENGTH conversion factor from the actual normal covector. Its identity
c=1-a-b=y/h is exact, and c>0 at each of the four source fan contacts is paid
from previously proved source branch signs. This is not a complete
circumradius-gradient/B2 theorem; positivity of the other barycentric weights
remains separate.
-/
set_option autoImplicit false
namespace N11Formalization.SourceFanConversion
open N11Formalization SourceFanLengthCovector PinBranchBind PinTangentGeometry
noncomputable section

theorem conversion_eq_hubCoord_div_height (P Q U H : Point)
    (heq : ‖U-P‖ = ‖U-Q‖) (hrank : det (U-P) (U-Q) ≠ 0)
    (hh : 0 < pinHeight P Q U) :
    1 - coefficientA (U-P) (U-Q) (U-H) - coefficientB (U-P) (U-Q) (U-H) =
      hubCoord P Q U H / pinHeight P Q U := by
  let W := U-chordMid P Q
  have ho : inner ℝ W (Q-P) = 0 := PinHeightPayV6.sub_midpoint_orthogonal heq
  have hpm : P-chordMid P Q = -(1/2 : ℝ) • (Q-P) := by
    unfold chordMid
    module
  have horth : inner ℝ W (P-chordMid P Q) = 0 := by
    rw [hpm, real_inner_smul_right, ho]
    ring
  have hUP : U-P = W-(P-chordMid P Q) := by dsimp [W]; abel
  have hUQ : U-Q = W+(P-chordMid P Q) := by
    dsimp [W]
    unfold chordMid
    module
  have hUH : U-H = W-(H-chordMid P Q) := by dsimp [W]; abel
  have hP : inner ℝ W (U-P) = ‖W‖^2 := by
    rw [hUP, inner_sub_right, horth, sub_zero, real_inner_self_eq_norm_sq]
  have hQ : inner ℝ W (U-Q) = ‖W‖^2 := by
    rw [hUQ, inner_add_right, horth, add_zero, real_inner_self_eq_norm_sq]
  have h := congrArg (fun n : Point => inner ℝ W n)
    (normal_expansion (U-P) (U-Q) (U-H) hrank)
  rw [hUH, inner_sub_right, real_inner_self_eq_norm_sq,
    inner_add_right, real_inner_smul_right, real_inner_smul_right, hP, hQ] at h
  have hy : inner ℝ W (H-chordMid P Q) = hubCoord P Q U H * ‖W‖ := by
    rw [real_inner_comm]
    exact inner_eq_hubCoord_mul_pinHeight P Q U H
  rw [hy] at h
  rw [← hUH] at h
  have hne : ‖W‖ ≠ 0 := ne_of_gt hh
  have hz : ((1-coefficientA (U-P) (U-Q) (U-H)-coefficientB (U-P) (U-Q) (U-H)) *
      ‖W‖ - hubCoord P Q U H) * ‖W‖ = 0 := by
    nlinarith [h]
  have hz' := (mul_eq_zero.mp hz).resolve_right hne
  apply (eq_div_iff (ne_of_gt hh)).mpr
  change (1-coefficientA (U-P) (U-Q) (U-H)-coefficientB (U-P) (U-Q) (U-H)) *
      ‖W‖ = hubCoord P Q U H
  linarith

def sourceConversion (k : Fin 9) : ℝ := 1-sourceA k-sourceB k
def sourceY (k : Fin 9) : ℝ :=
  hubCoord (ringCenter SourceExactRoot.sourceRoot k)
    (ringCenter SourceExactRoot.sourceRoot (k+1)) (Uvec SourceExactRoot.sourceRoot k) (sourceHub k)
def sourceHeight (k : Fin 9) : ℝ :=
  pinHeight (ringCenter SourceExactRoot.sourceRoot k)
    (ringCenter SourceExactRoot.sourceRoot (k+1)) (Uvec SourceExactRoot.sourceRoot k)

theorem sourceY_pos (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) : 0 < sourceY k := by
  rcases hk with rfl | rfl | rfl | rfl
  · simpa [sourceY, sourceHub, nd_fin_succ_1] using RootFanBranchConsumer.contact_y_pos_1.1
  · simpa [sourceY, sourceHub, nd_fin_succ_2] using RootFanBranchConsumer.contact_y_pos_2.1
  · simpa [sourceY, sourceHub, nd_fin_succ_3] using RootFanBranchConsumer.contact_y_pos_3.1
  · simpa [sourceY, sourceHub, nd_fin_succ_8] using RootFanBranchConsumer.contact_y_pos_8.1

theorem sourceConversion_eq (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    sourceConversion k = sourceY k / sourceHeight k :=
  conversion_eq_hubCoord_div_height _ _ _ _
    (RootPinNormalConsumer.source_contact_equidistant k)
    (RootPinNormalConsumer.source_contact_normals_independent k hk)
    (RootPinNormalConsumer.source_contact_height k hk)

/-- Correct LENGTH conversion factor sign, with all actual-source premises paid. -/
theorem sourceConversion_pos (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    0 < sourceConversion k := by
  rw [sourceConversion_eq k hk]
  exact div_pos (sourceY_pos k hk) (RootPinNormalConsumer.source_contact_height k hk)

def sourceFout (k : Fin 9) : ℝ :=
  ‖sourceHub k - pinOut (ringCenter SourceExactRoot.sourceRoot k)
    (ringCenter SourceExactRoot.sourceRoot (k+1)) (Uvec SourceExactRoot.sourceRoot k)‖^2 -
      (SourceExactRoot.sourceRoot 6)^2

theorem sourceFout_eq (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    sourceFout k = 4 * sourceY k * sourceHeight k := by
  have hd : ‖sourceHub k - Uvec SourceExactRoot.sourceRoot k‖ =
      SourceExactRoot.sourceRoot 6 := by
    rw [norm_sub_rev]
    exact source_normalH_norm k hk
  have he := Fout_eq_Fin_add_yh (ringCenter SourceExactRoot.sourceRoot k)
    (ringCenter SourceExactRoot.sourceRoot (k+1)) (Uvec SourceExactRoot.sourceRoot k)
    (sourceHub k) (SourceExactRoot.sourceRoot 6)
  rw [hd, sub_self, zero_add] at he
  exact he

/-- Exact LENGTH factor; the SQUARED-distance factor would carry an additional 2R. -/
theorem sourceConversion_eq_four_y_sq_over_Fout (k : Fin 9)
    (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    sourceConversion k = 4 * (sourceY k)^2 / sourceFout k := by
  rw [sourceConversion_eq k hk, sourceFout_eq k hk]
  have hy : sourceY k ≠ 0 := ne_of_gt (sourceY_pos k hk)
  have hh : sourceHeight k ≠ 0 :=
    ne_of_gt (RootPinNormalConsumer.source_contact_height k hk)
  field_simp [hy, hh]

def betaP (k : Fin 9) : ℝ := -sourceA k / sourceConversion k
def betaQ (k : Fin 9) : ℝ := -sourceB k / sourceConversion k
def betaH (k : Fin 9) : ℝ := 1 / sourceConversion k

theorem beta_sum_one (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    betaP k + betaQ k + betaH k = 1 := by
  have hc : sourceConversion k ≠ 0 := ne_of_gt (sourceConversion_pos k hk)
  unfold betaP betaQ betaH
  field_simp [hc]
  unfold sourceConversion
  ring

theorem betaH_pos (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) : 0 < betaH k :=
  one_div_pos.mpr (sourceConversion_pos k hk)

/-- The normalized coefficients reproduce the ACTUAL source circle centre.
They are affine barycentric coordinates; positivity of betaP/betaQ is not assumed
or concluded by this identity. -/
theorem beta_center_identity (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    Uvec SourceExactRoot.sourceRoot k =
      betaP k • ringCenter SourceExactRoot.sourceRoot k +
      betaQ k • ringCenter SourceExactRoot.sourceRoot (k+1) +
      betaH k • sourceHub k := by
  have hc : sourceConversion k ≠ 0 := ne_of_gt (sourceConversion_pos k hk)
  ext i
  have he := congrArg (fun p : Point => p i) (source_normalH_expansion k hk)
  simp only [normalH, normalP, normalQ, PiLp.sub_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul] at he
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  unfold betaP betaQ betaH
  field_simp [hc]
  unfold sourceConversion
  linear_combination he

/-- Normalized centre covector formula with exact sourceConversion scale.
The expression in parentheses is not yet equated to fderiv of circumradius. -/
theorem normalized_fan_length (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8)
    (v : CartesianReflectionSpace.Full) :
    fderiv ℝ (fanLength k) FullCartesianResidual.sourcePoint v =
      sourceConversion k *
        (-(betaP k * inner ℝ (normalP k)
              (TrueCirclePinSmooth.left (FullCartesianResidual.ringData k v)) +
           betaQ k * inner ℝ (normalQ k)
              (TrueCirclePinSmooth.right (FullCartesianResidual.ringData k v)) +
           betaH k * inner ℝ (normalH k) (fullHub k v)) /
          SourceExactRoot.sourceRoot 6 - v 22) := by
  rw [fanLength_source_fderiv k hk v]
  have hc : sourceConversion k ≠ 0 := ne_of_gt (sourceConversion_pos k hk)
  have hR : SourceExactRoot.sourceRoot 6 ≠ 0 := ne_of_gt SourceExactRoot.sourceRadius_pos
  unfold betaP betaQ betaH
  field_simp [hc, hR]
  unfold sourceConversion
  ring

end
end N11Formalization.SourceFanConversion
#check @N11Formalization.SourceFanConversion.sourceConversion_pos
#check @N11Formalization.SourceFanConversion.normalized_fan_length
#check @N11Formalization.SourceFanConversion.sourceConversion_eq_four_y_sq_over_Fout
#check @N11Formalization.SourceFanConversion.beta_center_identity
#print axioms N11Formalization.SourceFanConversion.sourceConversion_pos
#print axioms N11Formalization.SourceFanConversion.normalized_fan_length
