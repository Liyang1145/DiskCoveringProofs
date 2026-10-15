import N11Formalization.TrueCirclePin
import N11Formalization.RootPinNormalConsumer
set_option autoImplicit false
namespace N11Formalization.TrueCirclePinSmooth
open N11Formalization PinBranchBind PinTangentGeometry TrueCirclePin
noncomputable section
abbrev Data := Fin 5 → ℝ

def left (z : Data) : Point := !₂[z 0,z 1]
def right (z : Data) : Point := !₂[z 2,z 3]
def pinData (W : Point) (z : Data) : Point := pin W (left z) (right z) (z 4)

theorem left_smooth (z : Data) : ContDiffAt ℝ 1 left z := by
  rw [contDiffAt_piLp 2]
  intro i; fin_cases i <;> simp [left] <;> fun_prop

theorem right_smooth (z : Data) : ContDiffAt ℝ 1 right z := by
  rw [contDiffAt_piLp 2]
  intro i; fin_cases i <;> simp [right] <;> fun_prop

theorem normal_smooth (W : Point) (z : Data) (hPQ : left z ≠ right z) :
    ContDiffAt ℝ 1 (fun y => normal W (left y) (right y)) z := by
  have hd := (right_smooth z).sub (left_smooth z)
  have hn : ‖right z-left z‖^2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hPQ.symm))
  have hc : ContDiffAt ℝ 1 (fun y : Data => inner ℝ W (right y-left y)) z :=
    contDiffAt_const.inner ℝ hd
  exact contDiffAt_const.sub ((hc.div (hd.norm_sq ℝ) hn).smul hd)

theorem rad_smooth (z : Data) :
    ContDiffAt ℝ 1 (fun y => rad (left y) (right y) (y 4)) z := by
  have hR : ContDiffAt ℝ 1 (fun y : Data => y 4) z := by fun_prop
  exact (hR.pow 2).sub (((right_smooth z).sub (left_smooth z)).norm_sq ℝ |>.div_const 4)

/-- Smooth on an open legal locus in five independent Cartesian center/radius variables. -/
theorem pinData_smooth (W : Point) (z : Data) (hPQ : left z ≠ right z)
    (hN : normal W (left z) (right z) ≠ 0) (hr : rad (left z) (right z) (z 4) ≠ 0) :
    ContDiffAt ℝ 1 (pinData W) z := by
  have hn := normal_smooth W z hPQ
  have hs := (rad_smooth z).sqrt hr
  have hnorm := hn.norm ℝ hN
  have hm : ContDiffAt ℝ 1 (fun y : Data => chordMid (left y) (right y)) z :=
    ((left_smooth z).add (right_smooth z)).const_smul (2:ℝ)⁻¹
  exact hm.add ((hs.div hnorm (norm_ne_zero_iff.mpr hN)).smul hn)

def sourceData (k : Fin 9) : Data :=
  ![(ringCenter SourceExactRoot.sourceRoot k) 0,
    (ringCenter SourceExactRoot.sourceRoot k) 1,
    (ringCenter SourceExactRoot.sourceRoot (k+1)) 0,
    (ringCenter SourceExactRoot.sourceRoot (k+1)) 1, SourceExactRoot.sourceRoot 6]
def sourceSeed (k : Fin 9) : Point := Uvec SourceExactRoot.sourceRoot k -
  chordMid (ringCenter SourceExactRoot.sourceRoot k) (ringCenter SourceExactRoot.sourceRoot (k+1))

@[simp] theorem left_source (k : Fin 9) : left (sourceData k) = ringCenter SourceExactRoot.sourceRoot k := by
  ext i; fin_cases i <;> rfl
@[simp] theorem right_source (k : Fin 9) : right (sourceData k) = ringCenter SourceExactRoot.sourceRoot (k+1) := by
  ext i; fin_cases i <;> rfl
@[simp] theorem radius_source (k : Fin 9) : sourceData k 4 = SourceExactRoot.sourceRoot 6 := rfl

theorem source_distances (k : Fin 9) :
    ‖Uvec SourceExactRoot.sourceRoot k - left (sourceData k)‖ = sourceData k 4 ∧
    ‖Uvec SourceExactRoot.sourceRoot k - right (sourceData k)‖ = sourceData k 4 := by
  have hs : ∀ j : Fin 9, Real.sin (angleVec SourceExactRoot.sourceRoot j)^2 ≤
      (SourceExactRoot.sourceRoot 6)^2 := fun j => by
    linarith [SourceWidthNondegenerate.source_radicand_pos j]
  have hr := le_of_lt SourceExactRoot.sourceRadius_pos
  constructor
  · simpa only [left_source, radius_source, dist_eq_norm] using
      dist_Uvec_ringCenter_self SourceExactRoot.sourceRoot hs hr k
  · simpa only [right_source, radius_source, dist_eq_norm] using
      dist_Uvec_ringCenter_succ SourceExactRoot.sourceRoot hs hr k

theorem source_radicand_pos (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    0 < rad (left (sourceData k)) (right (sourceData k)) (sourceData k 4) := by
  have hd := source_distances k
  have hh := RootPinNormalConsumer.source_contact_height k hk
  have he := PinHeightPayV6.pinHeight_sq_of_equidistant hd.1 hd.2
  change ‖Uvec SourceExactRoot.sourceRoot k - chordMid (left (sourceData k)) (right (sourceData k))‖^2 =
    (sourceData k 4)^2 - (‖right (sourceData k)-left (sourceData k)‖/2)^2 at he
  have hp : 0 < ‖Uvec SourceExactRoot.sourceRoot k - chordMid (left (sourceData k)) (right (sourceData k))‖ := by
    simpa only [left_source, right_source, pinHeight] using hh
  unfold rad
  nlinarith [sq_pos_of_pos hp]

theorem source_normal_ne (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    normal (sourceSeed k) (left (sourceData k)) (right (sourceData k)) ≠ 0 := by
  have he := RootPinNormalConsumer.source_contact_equidistant k
  have hh := RootPinNormalConsumer.source_contact_height k hk
  simp only [left_source, right_source, sourceSeed, normal_source he]
  exact norm_ne_zero_iff.mp (ne_of_gt hh)

/-- This is the actual source branch, with every source premise discharged. -/
theorem source_pinData_eq (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    pinData (sourceSeed k) (sourceData k) = Uvec SourceExactRoot.sourceRoot k := by
  have hd := source_distances k
  unfold pinData sourceSeed
  simp only [← left_source k, ← right_source k]
  exact pin_source hd.1 hd.2 (by
    simpa only [left_source, right_source] using RootPinNormalConsumer.source_contact_height k hk)

theorem source_pinData_smooth (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ContDiffAt ℝ 1 (pinData (sourceSeed k)) (sourceData k) :=
  pinData_smooth _ _ (by simpa only [left_source, right_source] using
    RootPinNormalConsumer.source_contact_chord_ne k hk)
    (source_normal_ne k hk) (ne_of_gt (source_radicand_pos k hk))

/-- Both true-circle equations hold on an entire neighborhood in independent Cartesian data. -/
theorem source_pinData_equations_eventually (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ∀ᶠ z in nhds (sourceData k),
      ‖pinData (sourceSeed k) z-left z‖^2 = (z 4)^2 ∧
      ‖pinData (sourceSeed k) z-right z‖^2 = (z 4)^2 := by
  have hD := (right_smooth (sourceData k)).sub (left_smooth (sourceData k))
  have hne : right (sourceData k)-left (sourceData k) ≠ 0 :=
    sub_ne_zero.mpr (by simpa only [left_source, right_source] using
      (RootPinNormalConsumer.source_contact_chord_ne k hk).symm)
  have heD := hD.continuousAt.eventually_ne hne
  have heN := (normal_smooth (sourceSeed k) (sourceData k) (by
    simpa only [left_source, right_source] using RootPinNormalConsumer.source_contact_chord_ne k hk)).continuousAt.eventually_ne (source_normal_ne k hk)
  have her := (rad_smooth (sourceData k)).continuousAt.eventually
    (eventually_gt_nhds (source_radicand_pos k hk))
  filter_upwards [heD, heN, her] with z hzD hzN hzr
  exact pin_circle_equations _ _ _ _ (by
    intro h
    apply hzD
    rw [h, sub_self]) hzN (le_of_lt hzr)

end
end N11Formalization.TrueCirclePinSmooth
#check @N11Formalization.TrueCirclePinSmooth.source_pinData_eq
#check @N11Formalization.TrueCirclePinSmooth.source_pinData_smooth
#print axioms N11Formalization.TrueCirclePinSmooth.source_pinData_smooth
#print axioms N11Formalization.TrueCirclePinSmooth.source_pinData_eq
