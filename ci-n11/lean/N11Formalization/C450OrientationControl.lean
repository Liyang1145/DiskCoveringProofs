import N11Formalization.DSHTenBoundaryData
import N11Formalization.DSHTenBoundaryReduce

/-! Negative control for the existing fixed-density/arbitrary-hub obligation.
This does NOT refute source C450 or the original arbitrary-cover theorem. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace N11Formalization.C450OrientationControl
open scoped Interval
open MeasureTheory

def seg : TenSeg := c450Segs[35]'(by decide +kernel)
theorem member : seg ∈ c450Segs := by decide +kernel
theorem nonneg0 : |seg.a1| + |seg.a2| + |seg.a3| ≤ seg.a0 := by decide +kernel
theorem nonneg1 : |seg.b1| + |seg.b2| + |seg.b3| ≤ seg.b0 := by decide +kernel
def W0 : TrigDensity := seg.W0 nonneg0
def W1 : TrigDensity := seg.W1 nonneg1
def c : Point := ringPt (7/10) Real.pi
def h : Point := hubPt (-7/50)
def t : ℝ := Real.arccos (841/875)
def beta : ℝ := Real.arccos (14/19)
def half (W : TrigDensity) (x : ℝ) : ℝ :=
  W.a0*x - W.a1*Real.sin x + W.a2*Real.sin (2*x)/2 -
    W.a3*Real.sin (3*x)/3

theorem norm_c : ‖c‖ = (7:ℝ)/10 := by
  rw [c,norm_ringPt]
  norm_num
theorem norm_h : ‖h‖ = (7:ℝ)/50 := by
  rw [h,norm_hubPt]
  norm_num
theorem sub_eq : c-h = hubPt (-14/25) := by
  ext i
  fin_cases i <;> norm_num [c,h,ringPt,hubPt]
theorem norm_sub : ‖c-h‖ = (14:ℝ)/25 := by
  rw [sub_eq,norm_hubPt]
  norm_num
theorem sub_ne : c-h ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_sub]
  norm_num
theorem relative_cos : (c-h) 0 / ‖c-h‖ = -1 := by
  rw [norm_sub,sub_eq]
  norm_num [hubPt]

theorem t_mem : t ∈ Set.Icc (1/4:ℝ) 1 := by
  have hU : cosHiNLag 1 ≤ (841:ℚ)/875 := by decide +kernel
  have hL : (841:ℚ)/875 ≤ cosLoNLag (1/4) := by decide +kernel
  have hb := arccos_bracket_of_cos (q := (841:ℚ)/875) (lo := 1/4) (hi := 1)
    (by norm_num) (by norm_num; linarith [Real.pi_gt_three])
    (by norm_num) (by norm_num; linarith [Real.pi_gt_three])
    (by norm_num)
    ((Rat.cast_le (K := ℝ)).mpr hU) ((Rat.cast_le (K := ℝ)).mpr hL)
  simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,t] using hb
theorem beta_mem : beta ∈ Set.Icc (7/10:ℝ) 1 := by
  have hU : cosHiNLag 1 ≤ (14:ℚ)/19 := by decide +kernel
  have hL : (14:ℚ)/19 ≤ cosLoNLag (7/10) := by decide +kernel
  have hb := arccos_bracket_of_cos (q := (14:ℚ)/19) (lo := 7/10) (hi := 1)
    (by norm_num) (by norm_num; linarith [Real.pi_gt_three])
    (by norm_num) (by norm_num; linarith [Real.pi_gt_three])
    (by norm_num)
    ((Rat.cast_le (K := ℝ)).mpr hU) ((Rat.cast_le (K := ℝ)).mpr hL)
  simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,beta] using hb
theorem cos_t : Real.cos t = (841:ℝ)/875 :=
  Real.cos_arccos (by norm_num) (by norm_num)
theorem cos_beta : Real.cos beta = (14:ℝ)/19 :=
  Real.cos_arccos (by norm_num) (by norm_num)

theorem outer_integral :
    (∫ theta in (0)..(2*Real.pi),
      if dist (angPt theta) c ≤ (19/50:ℝ) then W0.toFun theta else 0) =
      2*half W0 t := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) t_mem.1
  have htpi : t ≤ Real.pi := le_trans t_mem.2 (by linarith [Real.pi_gt_three])
  have hc : Real.cos t = (1+(7/10:ℝ)^2-(19/50:ℝ)^2)/(2*(7/10:ℝ)) := by
    rw [cos_t]
    norm_num
  have ho := arc_integral_interval W0 (ρ := 7/10) (r := 19/50)
    (φ := Real.pi) (t := t) (by norm_num) (by norm_num) ht0 htpi hc
  change (∫ theta in (0)..(2*Real.pi),
    if dist (angPt theta) c ≤ (19/50:ℝ) then W0.toFun theta else 0) = _ at ho
  rw [ho]
  have h2 := cos_two_mul_of_cos Real.cos_pi
  have h3 := cos_three_mul_of_cos Real.cos_pi
  rw [Real.cos_pi,h2,h3]
  unfold half
  ring

theorem inner_integral :
    (∫ theta in (0)..(2*Real.pi),
      if dist (h+(19/50:ℝ) • angPt theta) c ≤ (19/50:ℝ)
        then W1.toFun theta else 0) = 2*half W1 beta := by
  have hb0 : 0 ≤ beta := le_trans (by norm_num) beta_mem.1
  have hbpi : beta ≤ Real.pi := le_trans beta_mem.2 (by linarith [Real.pi_gt_three])
  have hc : Real.cos beta =
      ‖ringPt (7/10) Real.pi-hubPt (-7/50)‖/(2*(19/50:ℝ)) := by
    change Real.cos beta = ‖c-h‖/(2*(19/50:ℝ))
    rw [cos_beta,norm_sub]
    norm_num
  have hi := inner_integral_active W1 (ρ := 7/10) (e := -7/50)
    (φ := Real.pi) (t := beta) (by norm_num) sub_ne hb0 hbpi hc
  change (∫ theta in (0)..(2*Real.pi),
    if dist (h+(19/50:ℝ) • angPt theta) c ≤ (19/50:ℝ)
      then W1.toFun theta else 0) = 2*innerHalf W1 beta ((c-h) 0 / ‖c-h‖) at hi
  rw [hi,relative_cos]
  unfold innerHalf half
  ring

theorem outer_lower :
    (26531:ℝ)/12500/4-(59453:ℝ)/500000/3 ≤ half W0 t := by
  have hs1 : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc
    ⟨le_trans (by norm_num) t_mem.1,
      le_trans t_mem.2 (by linarith [Real.pi_gt_three])⟩
  have hs2 : 0 ≤ Real.sin (2*t) := Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [t_mem.1],by linarith [t_mem.2,Real.pi_gt_three]⟩
  have hs3 := Real.sin_le_one (3*t)
  norm_num [half,W0,seg,c450Segs,TenSeg.W0]
  nlinarith [t_mem.1]
theorem inner_lower : (640343:ℝ)/500000*(7/10) ≤ half W1 beta := by
  have hs1 : 0 ≤ Real.sin beta := Real.sin_nonneg_of_mem_Icc
    ⟨le_trans (by norm_num) beta_mem.1,
      le_trans beta_mem.2 (by linarith [Real.pi_gt_three])⟩
  have hs2 : 0 ≤ Real.sin (2*beta) := Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [beta_mem.1],by linarith [beta_mem.2,Real.pi_gt_three]⟩
  have hs3 : 0 ≤ Real.sin (3*beta) := Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [beta_mem.1],by linarith [beta_mem.2,Real.pi_gt_three]⟩
  norm_num [half,W1,seg,c450Segs,TenSeg.W1]
  nlinarith [beta_mem.1]
theorem capacity_below_lower :
    (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 <
      2*((26531:ℝ)/12500/4-(59453:ℝ)/500000/3+
        (640343:ℝ)/500000*(7/10)) := by
  norm_num [W0,W1,seg,c450Segs,TenSeg.W0,TenSeg.W1]
  nlinarith [Real.pi_lt_four]

theorem not_perDisk : ¬seg.PerDisk := by
  intro hp
  have hb := hp nonneg0 nonneg1 c h
    (by rw [norm_c]; norm_num) (by rw [norm_c]; norm_num)
    (by rw [norm_h]; norm_num [seg,c450Segs])
    (by rw [norm_h]; norm_num [seg,c450Segs])
  change (∫ theta in (0)..(2*Real.pi),
      if dist (angPt theta) c ≤ (19/50:ℝ) then W0.toFun theta else 0) +
    (∫ theta in (0)..(2*Real.pi),
      if dist (h+(19/50:ℝ) • angPt theta) c ≤ (19/50:ℝ)
        then W1.toFun theta else 0) <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 at hb
  rw [outer_integral,inner_integral] at hb
  linarith [outer_lower,inner_lower,capacity_below_lower]
theorem not_obligation : ¬C450PerDiskObligation := by
  intro hp
  exact not_perDisk (hp seg member)
end N11Formalization.C450OrientationControl

#check @N11Formalization.C450OrientationControl.not_perDisk
#check @N11Formalization.C450OrientationControl.not_obligation
#print axioms N11Formalization.C450OrientationControl.outer_integral
#print axioms N11Formalization.C450OrientationControl.inner_integral
#print axioms N11Formalization.C450OrientationControl.not_perDisk
#print axioms N11Formalization.C450OrientationControl.not_obligation
