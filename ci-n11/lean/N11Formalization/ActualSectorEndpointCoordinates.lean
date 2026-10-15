import N11Formalization.ActualSwitchPointClosure

/-! Genuine normalized endpoint coordinates for the q0 closure factors.
The signed dot coordinate retains obtuse endpoint angles. Its paired
cross coordinate is nonnegative by the actual owned-chord orientation.
The arccos branch covers [0,pi], including flat owned sectors, while both
original endpoint radii remain in the exact norm and coordinate rows. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSectorEndpointCoordinates

open ActualCoverStructuralReduction ActualBoundaryNineTies ActualOwnedSectorDecomposition
open ActualOwnedChordGeometry ActualMetricAngleAtoms ActualSectorMetricDomain
open ActualSwitchPointClosure ActualOwnershipSwitchWidths ActualRingDirectionOrder
open ActualRingLinkBoundaryData ActualBoundaryCyclicOrder ActualBoundarySwitchAngles ActualSwitchAtomAggregate
open FlashTiling

def endpointAngleScalar (u v α : ℝ) : ℝ :=
  Real.arccos ((u-v*Real.cos α)/Real.sqrt (u^2+v^2-2*u*v*Real.cos α))

theorem actual_left_radius_units {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    leftRadius v i = (19/50 : ℝ)*leftNormalized v i := by
  unfold leftNormalized
  ring

theorem actual_right_radius_units {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    rightRadius v i = (19/50 : ℝ)*rightNormalized v i := by
  unfold rightNormalized
  ring

theorem actual_endpoint_ray_norms {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    ‖c (nextSite i)-switchPoint v i‖ = (19/50 : ℝ)*leftNormalized v i ∧
      ‖c (nextSite i)-switchPoint v (nextRing i)‖ = (19/50 : ℝ)*rightNormalized v i := by
  constructor
  · rw [← dist_eq_norm,dist_comm]
    exact actual_left_radius_units v i
  · rw [← dist_eq_norm,dist_comm]
    exact actual_right_radius_units v i

theorem actual_chord_quadratic_pos {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    0 < chordQuadratic v i := by
  have hd : 0 < dist (switchPoint v i) (switchPoint v (nextRing i)) :=
    dist_pos.mpr (actual_switch_points_distinct h hr v i)
  have he := actual_quadratic_chord v i
  nlinarith only [he,sq_pos_of_pos hd]

theorem actual_normalized_chord_pos {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    0 < Real.sqrt (chordQuadratic v i) := Real.sqrt_pos.mpr (actual_chord_quadratic_pos h hr v i)

theorem actual_chord_ray_norm {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    ‖switchPoint v (nextRing i)-switchPoint v i‖ =
      (19/50 : ℝ)*Real.sqrt (chordQuadratic v i) := by
  have he := actual_quadratic_chord v i
  have hq := actual_chord_quadratic_pos h hr v i
  have hs := Real.sq_sqrt hq.le
  rw [dist_comm,dist_eq_norm] at he
  nlinarith only [he,hs,Real.sqrt_nonneg (chordQuadratic v i),
    norm_nonneg (switchPoint v (nextRing i)-switchPoint v i)]

theorem chord_endpoint_inner (P Q C : Point) :
    inner ℝ (Q-P) (C-P) = dist P C^2-dist P C*dist Q C*
      Real.cos (EuclideanGeometry.angle P C Q) := by
  have hv : Q-P=(Q-C)-(P-C) := by module
  have hw : C-P= -(P-C) := by module
  have hc := InnerProductGeometry.cos_angle_mul_norm_mul_norm (P-C) (Q-C)
  change Real.cos (EuclideanGeometry.angle P C Q)*(‖P-C‖*‖Q-C‖) =
    inner ℝ (P-C) (Q-C) at hc
  rw [hv,hw,inner_neg_right,inner_sub_left,real_inner_self_eq_norm_sq,
    real_inner_comm (P-C) (Q-C),← hc]
  simp only [dist_eq_norm]
  ring

theorem actual_endpoint_dot_coordinates {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    inner ℝ (switchPoint v (nextRing i)-switchPoint v i) (c (nextSite i)-switchPoint v i) =
        (19/50 : ℝ)^2*leftNormalized v i*
          (leftNormalized v i-rightNormalized v i*Real.cos (sectorAngle v i)) ∧
      inner ℝ (c (nextSite i)-switchPoint v (nextRing i)) (switchPoint v i-switchPoint v (nextRing i)) =
        (19/50 : ℝ)^2*rightNormalized v i*
          (rightNormalized v i-leftNormalized v i*Real.cos (sectorAngle v i)) := by
  have hl := chord_endpoint_inner (switchPoint v i) (switchPoint v (nextRing i)) (c (nextSite i))
  change inner ℝ (switchPoint v (nextRing i)-switchPoint v i) (c (nextSite i)-switchPoint v i) =
    leftRadius v i^2-leftRadius v i*rightRadius v i*Real.cos (sectorAngle v i) at hl
  have hr := chord_endpoint_inner (switchPoint v (nextRing i)) (switchPoint v i) (c (nextSite i))
  rw [EuclideanGeometry.angle_comm] at hr
  change inner ℝ (switchPoint v i-switchPoint v (nextRing i)) (c (nextSite i)-switchPoint v (nextRing i)) =
    rightRadius v i^2-rightRadius v i*leftRadius v i*Real.cos (sectorAngle v i) at hr
  constructor
  · rw [hl,actual_left_radius_units,actual_right_radius_units]
    ring
  · rw [real_inner_comm (switchPoint v i-switchPoint v (nextRing i))
      (c (nextSite i)-switchPoint v (nextRing i)),hr,actual_left_radius_units,actual_right_radius_units]
    ring

theorem actual_endpoint_cross_coordinates {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    det2 (switchPoint v (nextRing i)-switchPoint v i) (c (nextSite i)-switchPoint v i) =
        (19/50 : ℝ)^2*leftNormalized v i*rightNormalized v i*Real.sin (sectorAngle v i) ∧
      det2 (c (nextSite i)-switchPoint v (nextRing i)) (switchPoint v i-switchPoint v (nextRing i)) =
        (19/50 : ℝ)^2*leftNormalized v i*rightNormalized v i*Real.sin (sectorAngle v i) := by
  have ha := actual_sector_area_angle h hr v i
  change orient (c (nextSite i)) (switchPoint v i) (switchPoint v (nextRing i))/2 =
    leftRadius v i*rightRadius v i*Real.sin (sectorAngle v i)/2 at ha
  have ho : orient (c (nextSite i)) (switchPoint v i) (switchPoint v (nextRing i)) =
      (19/50 : ℝ)^2*leftNormalized v i*rightNormalized v i*Real.sin (sectorAngle v i) := by
    rw [actual_left_radius_units,actual_right_radius_units] at ha
    nlinarith only [ha]
  constructor
  · rw [← ho]
    simp only [orient,det2,PiLp.sub_apply]
    ring
  · rw [← ho]
    simp only [orient,det2,PiLp.sub_apply]
    ring

theorem actual_endpoint_cross_nonneg {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    0 ≤ det2 (switchPoint v (nextRing i)-switchPoint v i) (c (nextSite i)-switchPoint v i) ∧
      0 ≤ det2 (c (nextSite i)-switchPoint v (nextRing i)) (switchPoint v i-switchPoint v (nextRing i)) := by
  have hc := actual_endpoint_cross_coordinates h hr v i
  have hd := actual_normalized_endpoint_domain h hr v i
  have hα := actual_sector_angle_bounds v i
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hα.1 hα.2
  rw [hc.1,hc.2]
  have hh := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg (19/50 : ℝ)) hd.1.le) hd.2.2.1.le) hs
  exact ⟨hh,hh⟩

theorem cancel_endpoint_normalization {u q a X Y : ℝ}
    (hu : 0 < u) (hq : 0 < q)
    (hcos : Real.cos a*((19/50 : ℝ)*u*((19/50 : ℝ)*q)) = (19/50 : ℝ)^2*u*X)
    (hsin : (19/50 : ℝ)*u*((19/50 : ℝ)*q)*Real.sin a = (19/50 : ℝ)^2*u*Y) :
    Real.cos a = X/q ∧ Real.sin a = Y/q := by
  have hf : (19/50 : ℝ)^2*u ≠ 0 := (mul_pos (by norm_num) hu).ne'
  constructor
  · apply (eq_div_iff hq.ne').2
    apply mul_left_cancel₀ hf
    calc
      _ = Real.cos a*((19/50 : ℝ)*u*((19/50 : ℝ)*q)) := by ring
      _ = _ := hcos
  · apply (eq_div_iff hq.ne').2
    apply mul_left_cancel₀ hf
    calc
      _ = (19/50 : ℝ)*u*((19/50 : ℝ)*q)*Real.sin a := by ring
      _ = _ := hsin

theorem actual_left_endpoint_cos_sin {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    Real.cos (sectorLeftEndpointAngle v i) =
        (leftNormalized v i-rightNormalized v i*Real.cos (sectorAngle v i))/Real.sqrt (chordQuadratic v i) ∧
      Real.sin (sectorLeftEndpointAngle v i) =
        rightNormalized v i*Real.sin (sectorAngle v i)/Real.sqrt (chordQuadratic v i) := by
  have hn := actual_endpoint_ray_norms v i
  have hch := actual_chord_ray_norm h hr v i
  have hdot := (actual_endpoint_dot_coordinates v i).1
  have hcross := (actual_endpoint_cross_coordinates h hr v i).1
  have hcos := InnerProductGeometry.cos_angle_mul_norm_mul_norm
    (c (nextSite i)-switchPoint v i) (switchPoint v (nextRing i)-switchPoint v i)
  change Real.cos (sectorLeftEndpointAngle v i)*
    (‖c (nextSite i)-switchPoint v i‖*‖switchPoint v (nextRing i)-switchPoint v i‖) = _ at hcos
  rw [real_inner_comm (switchPoint v (nextRing i)-switchPoint v i)
    (c (nextSite i)-switchPoint v i),hdot,hn.1,hch] at hcos
  have hsin := determinant_eq_norm_sin (actual_endpoint_cross_nonneg h hr v i).1
  change det2 (switchPoint v (nextRing i)-switchPoint v i) (c (nextSite i)-switchPoint v i) =
    ‖switchPoint v (nextRing i)-switchPoint v i‖*‖c (nextSite i)-switchPoint v i‖*
      Real.sin (EuclideanGeometry.angle (switchPoint v (nextRing i)) (switchPoint v i) (c (nextSite i))) at hsin
  rw [EuclideanGeometry.angle_comm (switchPoint v (nextRing i)) (switchPoint v i) (c (nextSite i)),
    hcross,hch,hn.1] at hsin
  change (19/50 : ℝ)^2*leftNormalized v i*rightNormalized v i*Real.sin (sectorAngle v i) =
    ((19/50 : ℝ)*Real.sqrt (chordQuadratic v i))*((19/50 : ℝ)*leftNormalized v i)*
      Real.sin (sectorLeftEndpointAngle v i) at hsin
  have hsin' : (19/50 : ℝ)*leftNormalized v i*((19/50 : ℝ)*Real.sqrt (chordQuadratic v i))*
      Real.sin (sectorLeftEndpointAngle v i) =
        (19/50 : ℝ)^2*leftNormalized v i*(rightNormalized v i*Real.sin (sectorAngle v i)) := by
    nlinarith only [hsin]
  exact cancel_endpoint_normalization (actual_normalized_endpoint_domain h hr v i).1
    (actual_normalized_chord_pos h hr v i) hcos hsin'

theorem actual_right_endpoint_cos_sin {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    Real.cos (sectorRightEndpointAngle v i) =
        (rightNormalized v i-leftNormalized v i*Real.cos (sectorAngle v i))/Real.sqrt (chordQuadratic v i) ∧
      Real.sin (sectorRightEndpointAngle v i) =
        leftNormalized v i*Real.sin (sectorAngle v i)/Real.sqrt (chordQuadratic v i) := by
  have hn := actual_endpoint_ray_norms v i
  have hch : ‖switchPoint v i-switchPoint v (nextRing i)‖ =
      (19/50 : ℝ)*Real.sqrt (chordQuadratic v i) := by
    rw [show switchPoint v i-switchPoint v (nextRing i)= -(switchPoint v (nextRing i)-switchPoint v i) by module,norm_neg]
    exact actual_chord_ray_norm h hr v i
  have hdot := (actual_endpoint_dot_coordinates v i).2
  have hcross := (actual_endpoint_cross_coordinates h hr v i).2
  have hcos := InnerProductGeometry.cos_angle_mul_norm_mul_norm
    (switchPoint v i-switchPoint v (nextRing i)) (c (nextSite i)-switchPoint v (nextRing i))
  change Real.cos (sectorRightEndpointAngle v i)*
    (‖switchPoint v i-switchPoint v (nextRing i)‖*‖c (nextSite i)-switchPoint v (nextRing i)‖) = _ at hcos
  rw [real_inner_comm (c (nextSite i)-switchPoint v (nextRing i))
    (switchPoint v i-switchPoint v (nextRing i)),hdot,hch,hn.2] at hcos
  have hcos' : Real.cos (sectorRightEndpointAngle v i)*
      ((19/50 : ℝ)*rightNormalized v i*((19/50 : ℝ)*Real.sqrt (chordQuadratic v i))) =
        (19/50 : ℝ)^2*rightNormalized v i*(rightNormalized v i-leftNormalized v i*Real.cos (sectorAngle v i)) := by
    nlinarith only [hcos]
  have hsin := determinant_eq_norm_sin (actual_endpoint_cross_nonneg h hr v i).2
  change det2 (c (nextSite i)-switchPoint v (nextRing i)) (switchPoint v i-switchPoint v (nextRing i)) =
    ‖c (nextSite i)-switchPoint v (nextRing i)‖*‖switchPoint v i-switchPoint v (nextRing i)‖*
      Real.sin (EuclideanGeometry.angle (c (nextSite i)) (switchPoint v (nextRing i)) (switchPoint v i)) at hsin
  rw [EuclideanGeometry.angle_comm (c (nextSite i)) (switchPoint v (nextRing i)) (switchPoint v i),
    hcross,hn.2,hch] at hsin
  change (19/50 : ℝ)^2*leftNormalized v i*rightNormalized v i*Real.sin (sectorAngle v i) =
    ((19/50 : ℝ)*rightNormalized v i)*((19/50 : ℝ)*Real.sqrt (chordQuadratic v i))*
      Real.sin (sectorRightEndpointAngle v i) at hsin
  have hsin' : (19/50 : ℝ)*rightNormalized v i*((19/50 : ℝ)*Real.sqrt (chordQuadratic v i))*
      Real.sin (sectorRightEndpointAngle v i) =
        (19/50 : ℝ)^2*rightNormalized v i*(leftNormalized v i*Real.sin (sectorAngle v i)) := by
    nlinarith only [hsin]
  exact cancel_endpoint_normalization (actual_normalized_endpoint_domain h hr v i).2.2.1
    (actual_normalized_chord_pos h hr v i) hcos' hsin'

theorem actual_endpoint_arccos_arguments_domain {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    (leftNormalized v i-rightNormalized v i*Real.cos (sectorAngle v i))/Real.sqrt (chordQuadratic v i) ∈ Set.Icc (-1 : ℝ) 1 ∧
      (rightNormalized v i-leftNormalized v i*Real.cos (sectorAngle v i))/Real.sqrt (chordQuadratic v i) ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [← (actual_left_endpoint_cos_sin h hr v i).1,← (actual_right_endpoint_cos_sin h hr v i).1]
  exact ⟨⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩,⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩⟩

theorem actual_endpoint_arccos_coordinates {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    sectorLeftEndpointAngle v i = Real.arccos
        ((leftNormalized v i-rightNormalized v i*Real.cos (sectorAngle v i))/Real.sqrt (chordQuadratic v i)) ∧
      sectorRightEndpointAngle v i = Real.arccos
        ((rightNormalized v i-leftNormalized v i*Real.cos (sectorAngle v i))/Real.sqrt (chordQuadratic v i)) := by
  have hl := congrArg Real.arccos (actual_left_endpoint_cos_sin h hr v i).1
  have hr' := congrArg Real.arccos (actual_right_endpoint_cos_sin h hr v i).1
  have hl0 : 0 ≤ sectorLeftEndpointAngle v i := EuclideanGeometry.angle_nonneg _ _ _
  have hlpi : sectorLeftEndpointAngle v i ≤ Real.pi := EuclideanGeometry.angle_le_pi _ _ _
  have hr0 : 0 ≤ sectorRightEndpointAngle v i := EuclideanGeometry.angle_nonneg _ _ _
  have hrpi : sectorRightEndpointAngle v i ≤ Real.pi := EuclideanGeometry.angle_le_pi _ _ _
  rw [Real.arccos_cos hl0 hlpi] at hl
  rw [Real.arccos_cos hr0 hrpi] at hr'
  exact ⟨hl,hr'⟩

theorem actual_endpoint_angle_scalars {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    sectorLeftEndpointAngle v i = endpointAngleScalar (leftNormalized v i) (rightNormalized v i) (sectorAngle v i) ∧
      sectorRightEndpointAngle v i = endpointAngleScalar (rightNormalized v i) (leftNormalized v i) (sectorAngle v i) := by
  have ha := actual_endpoint_arccos_coordinates h hr v i
  constructor
  · exact ha.1
  · unfold endpointAngleScalar
    have he : rightNormalized v i^2+leftNormalized v i^2-
        2*rightNormalized v i*leftNormalized v i*Real.cos (sectorAngle v i) = chordQuadratic v i := by
      unfold chordQuadratic
      ring
    rw [he]
    exact ha.2

/-- Full actual scalar-angle data for one sector, without an angle premise. -/
theorem actual_sector_endpoint_scalar_producer {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    0 < leftNormalized v i ∧ leftNormalized v i ≤ 1 ∧
      0 < rightNormalized v i ∧ rightNormalized v i ≤ 1 ∧
      0 ≤ sectorAngle v i ∧ sectorAngle v i ≤ Real.pi ∧
      0 < chordQuadratic v i ∧ 0 < Real.sqrt (chordQuadratic v i) ∧
      sectorLeftEndpointAngle v i = endpointAngleScalar (leftNormalized v i) (rightNormalized v i) (sectorAngle v i) ∧
      sectorRightEndpointAngle v i = endpointAngleScalar (rightNormalized v i) (leftNormalized v i) (sectorAngle v i) ∧
      sectorAngle v i + sectorLeftEndpointAngle v i + sectorRightEndpointAngle v i = Real.pi := by
  have hd := actual_normalized_endpoint_domain h hr v i
  have ha := actual_sector_angle_bounds v i
  have he := actual_endpoint_angle_scalars h hr v i
  exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,ha.1,ha.2,
    actual_chord_quadratic_pos h hr v i,actual_normalized_chord_pos h hr v i,he.1,he.2,
    actual_sector_triangle_angle_sum h v i⟩

/-- The paid switch-point closure expressed entirely in normalized factors. -/
theorem actual_switch_point_scalar_closure {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    endpointAngleScalar (rightNormalized v (i-1)) (leftNormalized v (i-1)) (sectorAngle v (i-1)) +
      endpointAngleScalar (leftNormalized v i) (rightNormalized v i) (sectorAngle v i) +
      2*SwitchData.angle (switchData h hr v i) + (switchGap v (i-1)+switchGap v i)/2 = Real.pi := by
  have hh := actual_switch_point_closure h hr v i
  rw [(actual_endpoint_angle_scalars h hr v (i-1)).2,(actual_endpoint_angle_scalars h hr v i).1] at hh
  exact hh

end N11Formalization.ActualSectorEndpointCoordinates

#check @N11Formalization.ActualSectorEndpointCoordinates.actual_sector_endpoint_scalar_producer
#check @N11Formalization.ActualSectorEndpointCoordinates.actual_switch_point_scalar_closure
#print axioms N11Formalization.ActualSectorEndpointCoordinates.actual_endpoint_dot_coordinates
#print axioms N11Formalization.ActualSectorEndpointCoordinates.actual_endpoint_cross_coordinates
#print axioms N11Formalization.ActualSectorEndpointCoordinates.actual_left_endpoint_cos_sin
#print axioms N11Formalization.ActualSectorEndpointCoordinates.actual_right_endpoint_cos_sin
#print axioms N11Formalization.ActualSectorEndpointCoordinates.actual_sector_endpoint_scalar_producer
#print axioms N11Formalization.ActualSectorEndpointCoordinates.actual_switch_point_scalar_closure
