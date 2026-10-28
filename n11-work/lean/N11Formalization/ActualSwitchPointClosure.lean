import N11Formalization.ActualRingAngleClosure
import N11Formalization.ActualDelaunayAngleBounds

/-! Exact closure at the genuine unit-circle switch points.
Sector endpoint angles are ordinary Euclidean angles with both original
endpoint radii. A strict inward halfplane fixes the local ray order;
flat owned triangles are retained without a closure premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSwitchPointClosure

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryNineTies ActualOwnedSectorDecomposition ActualOwnedChordGeometry
open ActualOwnershipSwitchWidths ActualBoundaryArcFrame ActualBoundaryCyclicOrder
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualMetricAngleAtoms
open ActualSectorMetricDomain ActualBoundarySwitchMetric ActualBoundarySwitchAngles
open ActualSwitchAtomAggregate ActualSwitchBaseAngle ActualSwitchWedgeArea
open ActualHubOneTurn ActualDelaunayAngleBounds ActualRingShoelacePositive
open ActualBoundaryExteriorGeometry FlashTiling

def sectorLeftEndpointAngle {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) : ℝ :=
  EuclideanGeometry.angle (c (nextSite i)) (switchPoint v i) (switchPoint v (nextRing i))

def sectorRightEndpointAngle {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) : ℝ :=
  EuclideanGeometry.angle (switchPoint v i) (switchPoint v (nextRing i)) (c (nextSite i))

theorem nextRing_prev (i : Fin 9) : nextRing (i-1) = i := by
  unfold nextRing
  exact sub_add_cancel i 1

theorem nextSite_prev (i : Fin 9) : nextSite (i-1) = ringSite i := by
  unfold nextSite
  rw [nextRing_prev]

theorem det_transitive_in_halfplane {n x y z : Point}
    (hx : inner ℝ n x < 0) (hy : inner ℝ n y < 0) (hz : inner ℝ n z < 0)
    (hxy : 0 ≤ det2 x y) (hyz : 0 ≤ det2 y z)
    (hstrict : 0 < det2 x y ∨ 0 < det2 y z) : 0 < det2 x z := by
  have hid := det_inner_basis x y z n
  have hleft := mul_nonpos_of_nonneg_of_nonpos hxy hz.le
  have hright := mul_nonpos_of_nonneg_of_nonpos hyz hx.le
  have hsum : det2 x y * inner ℝ n z + det2 y z * inner ℝ n x < 0 := by
    rcases hstrict with hh | hh
    · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hh hz) hright
    · exact add_neg_of_nonpos_of_neg hleft (mul_neg_of_pos_of_neg hh hx)
  have hm : det2 x z * inner ℝ n y < 0 := by linarith only [hid,hsum]
  rcases mul_neg_iff.mp hm with ⟨hp,_⟩ | ⟨_,hp⟩
  · exact hp
  · linarith

theorem ordered_angle_add {x y z : Point} (hy : y ≠ 0)
    (hxz : 0 < det2 x z) (hxy : 0 ≤ det2 x y) (hyz : 0 ≤ det2 y z) :
    InnerProductGeometry.angle x y + InnerProductGeometry.angle y z =
      InnerProductGeometry.angle x z := by
  have hx : x ≠ 0 := by
    intro he
    rw [he,det2_zero_left] at hxz
    exact (lt_irrefl 0) hxz
  have hz : z ≠ 0 := by intro he; simp [he,det2] at hxz
  let B := det2 y z / det2 x z
  let C := det2 x y / det2 x z
  have hB : 0 ≤ B := div_nonneg hyz hxz.le
  have hC : 0 ≤ C := div_nonneg hxy hxz.le
  have he : y = B • x+C • z := cramer_edges x z y hxz.ne'
  by_cases hb0 : B = 0
  · have hc0 : C ≠ 0 := by
      intro hh
      simp only [hb0,hh,zero_smul,add_zero] at he
      exact hy he
    have hcpos : 0 < C := lt_of_le_of_ne hC hc0.symm
    rw [he,hb0,zero_smul,zero_add,InnerProductGeometry.angle_smul_right_of_pos x z hcpos,
      InnerProductGeometry.angle_smul_left_of_pos z z hcpos,InnerProductGeometry.angle_self hz,add_zero]
  have hbpos : 0 < B := lt_of_le_of_ne hB (fun hh => hb0 hh.symm)
  by_cases hc0 : C = 0
  · rw [he,hc0,zero_smul,add_zero,InnerProductGeometry.angle_smul_right_of_pos x x hbpos,
      InnerProductGeometry.angle_smul_left_of_pos x z hbpos,InnerProductGeometry.angle_self hx,zero_add]
  have hcpos : 0 < C := lt_of_le_of_ne hC (fun hh => hc0 hh.symm)
  have hadd := InnerProductGeometry.angle_eq_angle_add_add_angle_add (B • x)
    (smul_ne_zero hcpos.ne' hz)
  rw [← he,InnerProductGeometry.angle_smul_left_of_pos x (C • z) hbpos,
    InnerProductGeometry.angle_smul_right_of_pos x z hcpos,
    InnerProductGeometry.angle_smul_left_of_pos x y hbpos,
    InnerProductGeometry.angle_smul_left_of_pos z y hcpos,
    InnerProductGeometry.angle_comm z y] at hadd
  exact hadd.symm

theorem four_ray_angle_chain {n x y z w : Point}
    (hx : inner ℝ n x < 0) (hy : inner ℝ n y < 0)
    (hz : inner ℝ n z < 0) (hw : inner ℝ n w < 0)
    (hxy : 0 ≤ det2 x y) (hyz : 0 < det2 y z) (hzw : 0 ≤ det2 z w) :
    InnerProductGeometry.angle x y + InnerProductGeometry.angle y z +
      InnerProductGeometry.angle z w = InnerProductGeometry.angle x w := by
  have hyn : y ≠ 0 := by intro he; rw [he,inner_zero_right] at hy; exact (lt_irrefl 0) hy
  have hzn : z ≠ 0 := by intro he; rw [he,inner_zero_right] at hz; exact (lt_irrefl 0) hz
  have hxz := det_transitive_in_halfplane hx hy hz hxy hyz.le (Or.inr hyz)
  have hxw := det_transitive_in_halfplane hx hz hw hxz.le hzw (Or.inl hxz)
  rw [ordered_angle_add hyn hxz hxy hyz.le, ordered_angle_add hzn hxw hxz.le hzw]

theorem unit_chord_inward {P Q : Point} (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1)
    (hne : P ≠ Q) : inner ℝ P (Q-P) < 0 := by
  have hn : 0 < ‖Q-P‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hsq := norm_sub_sq_real Q P
  rw [hQ,hP,real_inner_comm P Q] at hsq
  rw [inner_sub_right,real_inner_self_eq_norm_sq,hP]
  nlinarith only [hsq,sq_pos_of_pos hn]

theorem inside_ray_inward {P C : Point} (hP : ‖P‖ = 1) (hC : ‖C‖ < 1) :
    inner ℝ P (C-P) < 0 := by
  have hh := outward_inner_positive hP hC
  have he : inner ℝ P (C-P) = -inner ℝ P (P-C) := by
    simp only [inner_sub_right]
    ring
  rw [he]
  linarith

theorem circle_minor_chord (t : ℝ) {w : ℝ} (hw0 : 0 < w) (hwpi : w < Real.pi) :
    dist (circleMap t) (circleMap (t+w)) = 2*Real.sin (w/2) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (show 0 < w/2 by linarith)
    (show w/2 < Real.pi by linarith [Real.pi_pos])
  have hsq := circle_chord_square t (t+w)
  rw [show (t+w-t)/2=w/2 by ring] at hsq
  nlinarith only [hsq,hs,dist_nonneg (x := circleMap t) (y := circleMap (t+w))]

theorem unit_pair_base_angle {P Q : Point} {w : ℝ}
    (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1) (hw0 : 0 < w) (hwpi : w < Real.pi)
    (hchord : dist P Q = 2*Real.sin (w/2)) :
    EuclideanGeometry.angle Q P (0 : Point) = Real.pi/2-w/2 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (show 0 < w/2 by linarith)
    (show w/2 < Real.pi by linarith [Real.pi_pos])
  have hUP : dist (0 : Point) P = 1 := by rw [dist_zero_left,hP]
  have hUQ : dist (0 : Point) Q = 1 := by rw [dist_zero_left,hQ]
  have hc := isosceles_base_cos (hUP.trans hUQ.symm) hchord hUP hs (by norm_num : (0 : ℝ)<1)
  rw [div_one] at hc
  have htarget : Real.cos (Real.pi/2-w/2) = Real.sin (w/2) := Real.cos_pi_div_two_sub _
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by linarith,by linarith [Real.pi_pos]⟩ (hc.trans htarget.symm)

/-- Three consecutive unit-circle points, with both genuine minor widths. -/
theorem circle_three_point_angle (t : ℝ) {p n : ℝ}
    (hp0 : 0 < p) (hppi : p < Real.pi) (hn0 : 0 < n) (hnpi : n < Real.pi) :
    EuclideanGeometry.angle (circleMap (t+n)) (circleMap t) (circleMap (t-p)) =
      Real.pi-(p+n)/2 := by
  have hdn := circle_minor_chord t hn0 hnpi
  have hdp := circle_minor_chord (t-p) hp0 hppi
  rw [show t-p+p=t by ring] at hdp
  have hsn := Real.sin_pos_of_pos_of_lt_pi hn0 hnpi
  have hsp := Real.sin_pos_of_pos_of_lt_pi hp0 hppi
  have hsnh := Real.sin_pos_of_pos_of_lt_pi (show 0 < n/2 by linarith)
    (show n/2 < Real.pi by linarith [Real.pi_pos])
  have hsph := Real.sin_pos_of_pos_of_lt_pi (show 0 < p/2 by linarith)
    (show p/2 < Real.pi by linarith [Real.pi_pos])
  have hnn : circleMap t ≠ circleMap (t+n) := dist_pos.mp (by rw [hdn]; positivity)
  have hpn : circleMap t ≠ circleMap (t-p) :=
    (dist_pos.mp (by rw [hdp]; positivity : 0 < dist (circleMap (t-p)) (circleMap t))).symm
  have hx := unit_chord_inward (circleMap_norm t) (circleMap_norm (t+n)) hnn
  have hz := unit_chord_inward (circleMap_norm t) (circleMap_norm (t-p)) hpn
  have hy : inner ℝ (circleMap t) (-circleMap t) < 0 := by
    rw [inner_neg_right,real_inner_self_eq_norm_sq,circleMap_norm]
    norm_num
  have hxy : 0 < det2 (circleMap (t+n)-circleMap t) (-circleMap t) := by
    have he : det2 (circleMap (t+n)-circleMap t) (-circleMap t) =
        det2 (circleMap t) (circleMap (t+n)) := by
      simp only [det2,PiLp.sub_apply,PiLp.neg_apply]
      ring
    rw [he,det_circleMap,show t+n-t=n by ring]
    exact hsn
  have hyz : 0 < det2 (-circleMap t) (circleMap (t-p)-circleMap t) := by
    have he : det2 (-circleMap t) (circleMap (t-p)-circleMap t) =
        -det2 (circleMap t) (circleMap (t-p)) := by
      simp only [det2,PiLp.sub_apply,PiLp.neg_apply]
      ring
    rw [he,det_circleMap,show t-p-t= -p by ring,Real.sin_neg,neg_neg]
    exact hsp
  have hxz := det_transitive_in_halfplane hx hy hz hxy.le hyz.le (Or.inl hxy)
  have hyn : -circleMap t ≠ 0 := by
    intro he
    rw [he,inner_zero_right] at hy
    exact (lt_irrefl 0) hy
  have hadd := ordered_angle_add hyn hxz hxy.le hyz.le
  have hadd' : EuclideanGeometry.angle (circleMap (t+n)) (circleMap t) (0 : Point) +
    EuclideanGeometry.angle (0 : Point) (circleMap t) (circleMap (t-p)) =
      EuclideanGeometry.angle (circleMap (t+n)) (circleMap t) (circleMap (t-p)) := by
    simpa only [EuclideanGeometry.angle,vsub_eq_sub,zero_sub] using hadd
  have hbn := unit_pair_base_angle (circleMap_norm t) (circleMap_norm (t+n)) hn0 hnpi hdn
  have hbp := unit_pair_base_angle (circleMap_norm t) (circleMap_norm (t-p)) hp0 hppi
    (by rwa [dist_comm])
  rw [EuclideanGeometry.angle_comm (0 : Point) (circleMap t) (circleMap (t-p)),hbn,hbp] at hadd'
  linarith

theorem actual_switch_gap_lt_pi {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    switchGap v i < Real.pi := by
  have hh := actual_switch_gap_le_two_arcsin h hr v i
  have ha := (Real.arcsin_lt_pi_div_two).mpr (show r < 1 by linarith)
  linarith

theorem actual_switch_points_distinct {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    switchPoint v i ≠ switchPoint v (nextRing i) := by
  have hg := actual_switch_gap_positive h hr v i
  have hu := actual_switch_gap_lt_pi h hr v i
  have hs := Real.sin_pos_of_pos_of_lt_pi (show 0 < switchGap v i/2 by linarith)
    (show switchGap v i/2 < Real.pi by linarith [Real.pi_pos])
  apply dist_pos.mp
  rw [actual_minor_chord h hr v i]
  positivity

theorem actual_sector_triangle_angle_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (v : NineTies c r) (i : Fin 9) :
    sectorAngle v i + sectorLeftEndpointAngle v i + sectorRightEndpointAngle v i = Real.pi := by
  have hn : c (nextSite i) ≠ switchPoint v i :=
    (dist_pos.mp (actual_endpoint_radii_positive h v i).1).symm
  have hh := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := switchPoint v i) (p₂ := c (nextSite i)) (switchPoint v (nextRing i)) hn
  unfold sectorAngle sectorLeftEndpointAngle sectorRightEndpointAngle
  rw [EuclideanGeometry.angle_comm (c (nextSite i)) (switchPoint v (nextRing i)) (switchPoint v i),
    EuclideanGeometry.angle_comm (switchPoint v (nextRing i)) (switchPoint v i) (c (nextSite i))] at hh
  linarith

theorem actual_switch_apex_angle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    EuclideanGeometry.angle (c (nextSite i)) (switchPoint v i) (c (ringSite i)) =
      2*SwitchData.angle (switchData h hr v i) := by
  have hn := h.injective.ne (boundary_sites_distinct i).2.1.symm
  have hs := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c (nextSite i)) (p₂ := c (ringSite i)) (switchPoint v i) hn
  have hb := SwitchData.base_angles (switchData h hr v i) (v.tie i).equidistant
  change EuclideanGeometry.angle (c (nextSite i)) (c (ringSite i)) (switchPoint v i) =
      Real.pi/2-SwitchData.angle (switchData h hr v i) ∧
    EuclideanGeometry.angle (c (ringSite i)) (c (nextSite i)) (switchPoint v i) =
      Real.pi/2-SwitchData.angle (switchData h hr v i) at hb
  rw [EuclideanGeometry.angle_comm (c (ringSite i)) (switchPoint v i) (c (nextSite i)),
    EuclideanGeometry.angle_comm (switchPoint v i) (c (nextSite i)) (c (ringSite i))] at hs
  rw [hb.1,hb.2] at hs
  linarith

theorem previous_switch_circle {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    circleMap ((v.tie i).angle-switchGap v (i-1)) = switchPoint v (i-1) := by
  have he : (v.tie i).angle-switchGap v (i-1) =
      (v.tie (i-1)).angle + ((-nextShift (i-1) : ℤ) : ℝ)*period := by
    unfold switchGap nextLift
    rw [nextRing_prev,Int.cast_neg]
    ring
  rw [he,circleMap_periodic]
  rfl

theorem following_switch_circle {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    circleMap ((v.tie i).angle+switchGap v i) = switchPoint v (nextRing i) := by
  rw [show (v.tie i).angle+switchGap v i=nextLift v i by unfold switchGap; ring,
    nextLift_circle]
  rfl

theorem actual_three_switch_angle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    EuclideanGeometry.angle (switchPoint v (nextRing i)) (switchPoint v i) (switchPoint v (i-1)) =
      Real.pi-(switchGap v (i-1)+switchGap v i)/2 := by
  have hh := circle_three_point_angle (v.tie i).angle
    (actual_switch_gap_positive h hr v (i-1)) (actual_switch_gap_lt_pi h hr v (i-1))
    (actual_switch_gap_positive h hr v i) (actual_switch_gap_lt_pi h hr v i)
  rw [previous_switch_circle,following_switch_circle] at hh
  exact hh

theorem actual_switch_endpoint_angle_chain {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) :
    sectorRightEndpointAngle v (i-1) +
      EuclideanGeometry.angle (c (nextSite i)) (switchPoint v i) (c (ringSite i)) +
      sectorLeftEndpointAngle v i =
        EuclideanGeometry.angle (switchPoint v (nextRing i)) (switchPoint v i) (switchPoint v (i-1)) := by
  have hP : ‖switchPoint v i‖ = 1 := circleMap_norm _
  have hnext := actual_switch_points_distinct h hr v i
  have hprev := actual_switch_points_distinct h hr v (i-1)
  rw [nextRing_prev] at hprev
  have hx := unit_chord_inward hP (circleMap_norm _) hnext
  have hw := unit_chord_inward hP (circleMap_norm _) hprev.symm
  have hy := inside_ray_inward hP (h.center_inside (nextSite i))
  have hz := inside_ray_inward hP (h.center_inside (ringSite i))
  have hrigh := actual_owned_chord_triangle_nonneg h hr v i
  change 0 ≤ orient (c (nextSite i)) (switchPoint v i) (switchPoint v (nextRing i)) at hrigh
  have hleft := actual_owned_chord_triangle_nonneg h hr v (i-1)
  change 0 ≤ orient (c (nextSite (i-1))) (switchPoint v (i-1)) (switchPoint v (nextRing (i-1))) at hleft
  rw [nextSite_prev,nextRing_prev] at hleft
  have hswitch := actual_switch_wedge_positive h hr R i (v.tie i)
  change 0 < orient (c (ringSite i)) (switchPoint v i) (c (nextSite i)) at hswitch
  have hxy : 0 ≤ det2 (switchPoint v (nextRing i)-switchPoint v i)
      (c (nextSite i)-switchPoint v i) := by
    have he : det2 (switchPoint v (nextRing i)-switchPoint v i) (c (nextSite i)-switchPoint v i) =
        orient (c (nextSite i)) (switchPoint v i) (switchPoint v (nextRing i)) := by
      simp only [orient,det2,PiLp.sub_apply]; ring
    rwa [he]
  have hyz : 0 < det2 (c (nextSite i)-switchPoint v i) (c (ringSite i)-switchPoint v i) := by
    have he : det2 (c (nextSite i)-switchPoint v i) (c (ringSite i)-switchPoint v i) =
        orient (c (ringSite i)) (switchPoint v i) (c (nextSite i)) := by
      simp only [orient,det2,PiLp.sub_apply]; ring
    rwa [he]
  have hzw : 0 ≤ det2 (c (ringSite i)-switchPoint v i) (switchPoint v (i-1)-switchPoint v i) := by
    have he : det2 (c (ringSite i)-switchPoint v i) (switchPoint v (i-1)-switchPoint v i) =
        orient (c (ringSite i)) (switchPoint v (i-1)) (switchPoint v i) := by
      simp only [orient,det2,PiLp.sub_apply]; ring
    rwa [he]
  have hh := four_ray_angle_chain hx hy hz hw hxy hyz hzw
  change EuclideanGeometry.angle (switchPoint v (nextRing i)) (switchPoint v i) (c (nextSite i)) +
    EuclideanGeometry.angle (c (nextSite i)) (switchPoint v i) (c (ringSite i)) +
    EuclideanGeometry.angle (c (ringSite i)) (switchPoint v i) (switchPoint v (i-1)) =
      EuclideanGeometry.angle (switchPoint v (nextRing i)) (switchPoint v i) (switchPoint v (i-1)) at hh
  unfold sectorRightEndpointAngle sectorLeftEndpointAngle
  rw [nextSite_prev,nextRing_prev,EuclideanGeometry.angle_comm (switchPoint v (i-1)) (switchPoint v i) (c (ringSite i)),
    EuclideanGeometry.angle_comm (c (nextSite i)) (switchPoint v i) (switchPoint v (nextRing i))]
  linarith

/-- Closure at Pi uses the right endpoint of sector i-1 and the left
endpoint of sector i. It is independent of an assumed ring-site closure. -/
theorem actual_switch_point_closure {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    sectorRightEndpointAngle v (i-1) + sectorLeftEndpointAngle v i +
      2*SwitchData.angle (switchData h hr v i) +
      (switchGap v (i-1)+switchGap v i)/2 = Real.pi := by
  obtain ⟨R⟩ := actual_refinement h hr
  have hh := actual_switch_endpoint_angle_chain h hr R v i
  rw [actual_switch_apex_angle h hr v i, actual_three_switch_angle h hr v i] at hh
  linarith

end N11Formalization.ActualSwitchPointClosure

#check @N11Formalization.ActualSwitchPointClosure.actual_sector_triangle_angle_sum
#check @N11Formalization.ActualSwitchPointClosure.actual_switch_point_closure
#print axioms N11Formalization.ActualSwitchPointClosure.four_ray_angle_chain
#print axioms N11Formalization.ActualSwitchPointClosure.actual_sector_triangle_angle_sum
#print axioms N11Formalization.ActualSwitchPointClosure.actual_switch_apex_angle
#print axioms N11Formalization.ActualSwitchPointClosure.actual_three_switch_angle
#print axioms N11Formalization.ActualSwitchPointClosure.actual_switch_point_closure
