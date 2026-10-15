import N11Formalization.ActualMetricAngleAtoms

/-! Genuine closed sector-factor inputs, retaining unequal endpoint radii.
The width is the actual nearest ownership width, not an SOC anchor gap.
Normalization uses 19/50 only as a change of units. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSectorMetricDomain
open ActualMetricAngleAtoms ActualCoverStructuralReduction ActualBoundaryNineTies
open ActualOwnedSectorDecomposition ActualOwnershipSwitchWidths
open ActualBoundaryArcFrame ActualBoundaryCyclicOrder ActualRingLinkBoundaryData
open ActualSwitchAtomAggregate ActualBoundarySwitchMetric

theorem circle_inside_dist_positive {x a : Point} (hx : ‖x‖=1) (ha : ‖a‖<1) :
    0 < dist x a := by
  apply dist_pos.mpr
  intro he
  rw [← he,hx] at ha
  exact (lt_irrefl 1) ha

theorem actual_endpoint_radii_positive {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (v : NineTies c r) (i : Fin 9) :
    0 < leftRadius v i ∧ 0 < rightRadius v i :=
  ⟨circle_inside_dist_positive (circleMap_norm _) (h.center_inside _),
    circle_inside_dist_positive (circleMap_norm _) (h.center_inside _)⟩

theorem actual_sector_radius_copies {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    leftRadius v i=(switchData h hr v i).radius ∧
      rightRadius v i=(switchData h hr v (nextRing i)).radius := by
  constructor
  · rw [(switchData h hr v i).radius_exact]
    exact (v.tie i).equidistant.symm
  · exact (switchData h hr v (nextRing i)).radius_exact.symm

def leftNormalized {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  leftRadius v i/(19/50)
def rightNormalized {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  rightRadius v i/(19/50)

theorem actual_normalized_endpoint_domain {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    0 < leftNormalized v i ∧ leftNormalized v i ≤ 1 ∧
      0 < rightNormalized v i ∧ rightNormalized v i ≤ 1 := by
  have hp := actual_endpoint_radii_positive h v i
  have hb := actual_sector_endpoint_radii v i
  unfold leftNormalized rightNormalized
  refine ⟨div_pos hp.1 (by norm_num),?_,div_pos hp.2 (by norm_num),?_⟩
  · rw [div_le_one₀ (by norm_num : (0:ℝ)<19/50)]
    exact hb.2.1.trans hr.le
  · rw [div_le_one₀ (by norm_num : (0:ℝ)<19/50)]
    exact hb.2.2.2.trans hr.le

theorem circle_chord_square (a b : ℝ) :
    dist (circleMap a) (circleMap b)^2=4*Real.sin ((b-a)/2)^2 := by
  rw [dist_eq_norm,norm_sub_sq_real,circleMap_norm,circleMap_norm,inner_circleMap]
  have hc : Real.cos (a-b)=1-2*Real.sin ((b-a)/2)^2 := by
    rw [show a-b=-(2*((b-a)/2)) by ring,Real.cos_neg,Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq ((b-a)/2)]
  rw [hc]
  ring

theorem actual_minor_chord {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    dist (switchPoint v i) (switchPoint v (nextRing i)) =
      2*Real.sin (switchGap v i/2) := by
  have hg := actual_switch_gap_positive h hr v i
  have hu := actual_switch_gap_le_two_arcsin h hr v i
  have hs : 0 ≤ Real.sin (switchGap v i/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith [Real.arcsin_le_pi_div_two r,Real.pi_pos])
  have hc := circle_chord_square (v.tie i).angle (nextLift v i)
  rw [nextLift_circle] at hc
  change dist (switchPoint v i) (switchPoint v (nextRing i))^2 =
    4*Real.sin (switchGap v i/2)^2 at hc
  nlinarith [dist_nonneg (x := switchPoint v i) (y := switchPoint v (nextRing i))]

theorem actual_width_arcsin_chord {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    switchGap v i =
      2*Real.arcsin (dist (switchPoint v i) (switchPoint v (nextRing i))/2) := by
  have hg := actual_switch_gap_positive h hr v i
  have hu := actual_switch_gap_le_two_arcsin h hr v i
  rw [actual_minor_chord h hr v i]
  have he : 2*Real.sin (switchGap v i/2)/2=Real.sin (switchGap v i/2) := by ring
  rw [he,Real.arcsin_sin (by linarith [Real.pi_pos])
    (by linarith [Real.arcsin_le_pi_div_two r])]
  ring

def chordQuadratic {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  leftNormalized v i^2+rightNormalized v i^2 -
    2*leftNormalized v i*rightNormalized v i*Real.cos (sectorAngle v i)

theorem actual_quadratic_chord {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    (19/50 : ℝ)^2*chordQuadratic v i =
      dist (switchPoint v i) (switchPoint v (nextRing i))^2 := by
  rw [actual_sector_cosine_law]
  unfold chordQuadratic leftNormalized rightNormalized
  ring

theorem actual_factor_width_formula {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    switchGap v i =
      2*Real.arcsin ((19/50 : ℝ)*Real.sqrt (chordQuadratic v i)/2) := by
  have hc := actual_quadratic_chord v i
  have hq : 0 ≤ chordQuadratic v i := by
    nlinarith [sq_nonneg (dist (switchPoint v i) (switchPoint v (nextRing i)))]
  have hs := Real.sq_sqrt hq
  have he : (19/50 : ℝ)*Real.sqrt (chordQuadratic v i) =
      dist (switchPoint v i) (switchPoint v (nextRing i)) := by
    nlinarith [Real.sqrt_nonneg (chordQuadratic v i),
      dist_nonneg (x := switchPoint v i) (y := switchPoint v (nextRing i))]
  rw [he]
  exact actual_width_arcsin_chord h hr v i

end N11Formalization.ActualSectorMetricDomain
#check @N11Formalization.ActualSectorMetricDomain.actual_sector_radius_copies
#check @N11Formalization.ActualSectorMetricDomain.actual_factor_width_formula
#print axioms N11Formalization.ActualSectorMetricDomain.actual_normalized_endpoint_domain
#print axioms N11Formalization.ActualSectorMetricDomain.actual_factor_width_formula
