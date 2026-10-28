import N11Formalization.ActualBoundaryNeighborTies

/-! Actual private circle points exclude tangential bisector/circle ties.
This proves nonzero gap derivative, rather than assuming transversality. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryTransversality
open ActualBoundaryNeighborTies ActualBoundaryTieUniqueness ActualHubEdgeGeometry
open DSHTopologyOwnership DSHTopologyOwnershipSwitches
open ActualCoverStructuralReduction ActualRingDirectionOrder ActualBoundaryCyclicOrder

def gapDerivative (a b : Point) (t : ℝ) : ℝ :=
  2*(Real.sin t*(b 0-a 0)-Real.cos t*(b 1-a 1))

theorem hasDerivAt_sqDist (a : Point) (t : ℝ) :
    HasDerivAt (sqDist a) (2*(Real.sin t*a 0-Real.cos t*a 1)) t := by
  have hh := (((Real.hasDerivAt_cos t).mul_const (a 0)).add
    ((Real.hasDerivAt_sin t).mul_const (a 1))).const_mul 2
  have he := (hh.const_sub (1+‖a‖^2)).congr_deriv
    (show -(2*(-Real.sin t*a 0+Real.cos t*a 1)) =
      2*(Real.sin t*a 0-Real.cos t*a 1) by ring)
  exact he

theorem hasDerivAt_gap (a b : Point) (t : ℝ) :
    HasDerivAt (fun s => sqDist b s-sqDist a s) (gapDerivative a b t) t := by
  exact ((hasDerivAt_sqDist b t).sub (hasDerivAt_sqDist a t)).congr_deriv
    (by dsimp [gapDerivative]; ring)

theorem gapDerivative_ne_zero {a b y z : Point} {t : ℝ}
    (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hya : dist y a < dist y b) (hzb : dist z b < dist z a)
    (ht : dist (circleMap t) a = dist (circleMap t) b) :
    gapDerivative a b t ≠ 0 := by
  let d := b-a
  let beta := inner ℝ (circleMap t) d
  have he : 2*beta = ‖b‖^2-‖a‖^2 := bisector_equation ht
  have hey := square_difference y a b
  have hez := square_difference z a b
  have hysq := (dist_lt_dist_iff_sq y a b).mp hya
  have hzsq := (dist_lt_dist_iff_sq z b a).mp hzb
  have hpy : inner ℝ y d < beta := by change inner ℝ y (b-a) < beta; linarith
  have hpz : beta < inner ℝ z d := by change beta < inner ℝ z (b-a); linarith
  have hcy := abs_real_inner_le_norm y d
  have hcz := abs_real_inner_le_norm z d
  rw [hy,one_mul] at hcy
  rw [hz,one_mul] at hcz
  have hyb := (abs_le.mp hcy).1
  have hzb := (abs_le.mp hcz).2
  have hblo : -‖d‖ < beta := hyb.trans_lt hpy
  have hbhi : beta < ‖d‖ := hpz.trans_le hzb
  have hsq : beta^2 < ‖d‖^2 := by nlinarith
  intro hzero
  have htan : Real.sin t*d 0-Real.cos t*d 1 = 0 := by
    dsimp [gapDerivative] at hzero
    simp only [d,PiLp.sub_apply]
    linarith
  have hproj : beta = Real.cos t*d 0+Real.sin t*d 1 := inner_circleMap_point t d
  have hnorm : ‖d‖^2 = d 0^2+d 1^2 := PinTangentGeometry.norm_sq_coords d
  have hid := Real.cos_sq_add_sin_sq t
  have hpara : beta^2+(Real.sin t*d 0-Real.cos t*d 1)^2 = ‖d‖^2 := by
    rw [hproj,hnorm]
    nlinarith [congrArg (fun q : ℝ => q*(d 0)^2) hid,
      congrArg (fun q : ℝ => q*(d 1)^2) hid]
  rw [htan] at hpara
  norm_num at hpara
  linarith

theorem Representative.neighbor_transverse {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (i : Fin 9) (v : NeighborTie c r i) :
    gapDerivative (c (ringSite i)) (c (ringSite (nextRing i))) v.angle ≠ 0 := by
  obtain ⟨y,hy,hya,hyother⟩ := h.private_circle i
  obtain ⟨z,hz,hzb,hzother⟩ := h.private_circle (nextRing i)
  have hsites : ringSite i ≠ ringSite (nextRing i) := by
    intro he
    exact next_ne i (Fin.ext (congrArg (fun q : Fin 11 => q.val) he))
  exact gapDerivative_ne_zero hy hz
    (hya.trans_lt (hyother _ hsites.symm)) (hzb.trans_lt (hzother _ hsites)) v.equidistant

end N11Formalization.ActualBoundaryTransversality
#check @N11Formalization.ActualBoundaryTransversality.Representative.neighbor_transverse
#print axioms N11Formalization.ActualBoundaryTransversality.Representative.neighbor_transverse
