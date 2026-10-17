import N11Formalization.ActualSwitchBaseAngle
import N11Formalization.ActualSiteAnglePacking
import N11Formalization.ActualSwitchWedgeArea
import N11Formalization.ActualSectorMetricDomain

/-! Exact real closure at every actual ring site.
The accepted boundary chain fixes the two surviving directed rays.
The two true switch base angles and owned sector close this phase chain.
The produced full-site angle packing fixes the integer lift, including
flat owned sectors and artificial zero-primal-length diagonals. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRingAngleClosure

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryChainConservation ActualCenterRingShoelace
open ActualTriangleBoundaryChain ActualRingDirectionOrder ActualRingLinkBoundaryData
open ActualBoundaryCyclicOrder ActualRefinementInteriorFacetCount
open ActualSiteAngleChain ActualSiteAnglePacking ActualAnglePhase ActualMetricAngleAtoms
open ActualBoundaryNineTies ActualOwnedSectorDecomposition ActualOwnedChordGeometry
open ActualBoundarySwitchMetric ActualBoundarySwitchAngles ActualSwitchAtomAggregate
open ActualSwitchBaseAngle ActualSwitchWedgeArea ActualSectorMetricDomain FlashTiling

theorem next_prev_site (i : Fin 9) : prevSite (nextRing i) = ringSite i := by
  unfold prevSite nextRing
  rw [add_sub_cancel_right]

theorem actual_ring_face_phase {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9) :
    (siteFaceSum R (ringSite i) : Real.Angle) =
      sitePhase c (ringSite i) (prevSite i) - sitePhase c (ringSite i) (nextSite i) := by
  classical
  have hn : total R (ringSite i) (nextSite i) = 1 :=
    actual_all_boundary_mass_positive_one h hr R i
  have hp : total R (ringSite i) (prevSite i) = -1 := by
    have hh := actual_all_boundary_mass_positive_one h hr R (i-1)
    have he : nextSite (i-1) = ringSite i := by
      unfold nextSite nextRing
      rw [sub_add_cancel]
    change total R (ringSite (i-1)) (nextSite (i-1)) = 1 at hh
    rw [he, total_antisymm R (ringSite (i-1)) (ringSite i)] at hh
    change -total R (ringSite i) (prevSite i) = 1 at hh
    omega
  have hs : (∑ j ∈ ({prevSite i,nextSite i} : Finset (Fin 11)),
      total R (ringSite i) j • sitePhase c (ringSite i) j) =
      ∑ j : Fin 11, total R (ringSite i) j • sitePhase c (ringSite i) j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hz : total R (ringSite i) j = 0 := by
      apply total_nonboundary_zero h hr R
      simpa only [boundary_labels_at_ring, Finset.mem_insert, Finset.mem_singleton] using hj
    rw [hz, zero_zsmul]
  rw [actual_site_face_phase_chain, ← hs,
    Finset.sum_pair (boundary_sites_distinct i).2.2, hp, hn]
  simp only [neg_one_zsmul, one_zsmul]
  abel

theorem positive_orient_phase {a b k : Point} (ho : 0 < orient a b k) :
    (EuclideanGeometry.angle b a k : Real.Angle) =
      (directionAngle (k-a) : Real.Angle) - (directionAngle (b-a) : Real.Angle) := by
  have hx : b-a ≠ 0 := by
    intro he
    simp only [orient, he, det2_zero_left] at ho
    exact (lt_irrefl 0) ho
  have hy : k-a ≠ 0 := by
    intro he
    simp [orient, he, det2] at ho
  exact positive_determinant_angle_phase hx hy ho.le

theorem actual_sector_phase {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    (sectorAngle v i : Real.Angle) =
      (directionAngle (switchPoint v (nextRing i)-c (nextSite i)) : Real.Angle) -
        (directionAngle (switchPoint v i-c (nextSite i)) : Real.Angle) := by
  have hp := actual_endpoint_radii_positive h v i
  have hx : switchPoint v i-c (nextSite i) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact dist_pos.mp hp.1
  have hy : switchPoint v (nextRing i)-c (nextSite i) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact dist_pos.mp hp.2
  have hd : 0 ≤ det2 (switchPoint v i-c (nextSite i))
      (switchPoint v (nextRing i)-c (nextSite i)) :=
    actual_owned_chord_triangle_nonneg h hr v i
  exact positive_determinant_angle_phase hx hy hd

theorem actual_ring_angle_phase_zero {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) :
    ((siteFaceSum R (nextSite i) + sectorAngle v i +
        EuclideanGeometry.angle (c (ringSite i)) (c (nextSite i)) (switchPoint v i) +
        EuclideanGeometry.angle (switchPoint v (nextRing i)) (c (nextSite i))
          (c (nextSite (nextRing i)))) : Real.Angle) = 0 := by
  have hS := actual_ring_face_phase h hr R (nextRing i)
  rw [next_prev_site] at hS
  change (siteFaceSum R (nextSite i) : Real.Angle) =
    (directionAngle (c (ringSite i)-c (nextSite i)) : Real.Angle) -
      (directionAngle (c (nextSite (nextRing i))-c (nextSite i)) : Real.Angle) at hS
  have hLorient : 0 < orient (c (nextSite i)) (c (ringSite i)) (switchPoint v i) := by
    rw [ActualIncidentFacetAdjacency.orient_cycle]
    exact actual_switch_wedge_positive h hr R i (v.tie i)
  have hL := positive_orient_phase hLorient
  have hRorient : 0 < orient (c (nextSite i)) (switchPoint v (nextRing i))
      (c (nextSite (nextRing i))) :=
    actual_switch_wedge_positive h hr R (nextRing i) (v.tie (nextRing i))
  have hR := positive_orient_phase hRorient
  rw [hS, actual_sector_phase h hr v i, hL, hR]
  abel

/-- The owner of sector `i` is `nextSite i`; its two switch angles are
the data at `i` and at `nextRing i`. No angular closure premise is assumed. -/
theorem actual_ring_angle_closure {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) :
    sectorAngle v i + siteFaceSum R (nextSite i) -
      SwitchData.angle (switchData h hr v i) -
      SwitchData.angle (switchData h hr v (nextRing i)) = Real.pi := by
  let γL := EuclideanGeometry.angle (c (ringSite i)) (c (nextSite i)) (switchPoint v i)
  let γR := EuclideanGeometry.angle (switchPoint v (nextRing i)) (c (nextSite i))
    (c (nextSite (nextRing i)))
  have hL : γL = Real.pi/2-SwitchData.angle (switchData h hr v i) :=
    (SwitchData.base_angles (switchData h hr v i) (v.tie i).equidistant).2
  have hR : γR = Real.pi/2-SwitchData.angle (switchData h hr v (nextRing i)) := by
    have hh := (SwitchData.base_angles (switchData h hr v (nextRing i))
      (v.tie (nextRing i)).equidistant).1
    change EuclideanGeometry.angle (switchPoint v (nextRing i)) (c (nextSite i))
      (c (nextSite (nextRing i))) = _
    rw [EuclideanGeometry.angle_comm]
    exact hh
  have hbL := SwitchData.angle_bounds (switchData h hr v i)
  have hbR := SwitchData.angle_bounds (switchData h hr v (nextRing i))
  have hγL : 0 < γL := by rw [hL]; linarith
  have hγR : 0 < γR := by rw [hR]; linarith
  have hS0 := actual_site_face_sum_nonneg R (nextSite i)
  have hS2 := actual_site_face_sum_le_two_pi R (nextSite i)
  have hα := actual_sector_angle_bounds v i
  let Q := siteFaceSum R (nextSite i) + sectorAngle v i + γL + γR
  have hQpos : 0 < Q := by dsimp [Q]; linarith
  have hQlt : Q < 4*Real.pi := by dsimp [Q]; rw [hL,hR]; linarith
  have hQphase : (Q : Real.Angle) = 0 := actual_ring_angle_phase_zero h hr R v i
  obtain ⟨n,hn⟩ := Real.Angle.coe_eq_zero_iff.mp hQphase
  have hQ : Q = (n : ℝ)*(2*Real.pi) := by simpa only [zsmul_eq_mul] using hn.symm
  have hnpos : 0 < (n : ℝ) := by
    by_contra hnot
    have hnon := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot)
      (show 0 ≤ 2*Real.pi by positivity)
    rw [← hQ] at hnon
    exact (not_lt_of_ge hnon) hQpos
  have hnlt : (n : ℝ) < 2 := by
    by_contra hnot
    have hnon := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
      (show 0 ≤ 2*Real.pi by positivity)
    nlinarith only [hQ, hQlt, hnon]
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hnpos
  have hn2 : n < (2 : ℤ) := by exact_mod_cast hnlt
  have hn1 : n = 1 := by omega
  rw [hn1, Int.cast_one, one_mul] at hQ
  dsimp [Q] at hQ
  rw [hL,hR] at hQ
  linarith

end N11Formalization.ActualRingAngleClosure
#check @N11Formalization.ActualRingAngleClosure.actual_ring_face_phase
#check @N11Formalization.ActualRingAngleClosure.actual_ring_angle_phase_zero
#check @N11Formalization.ActualRingAngleClosure.actual_ring_angle_closure
#print axioms N11Formalization.ActualRingAngleClosure.actual_ring_face_phase
#print axioms N11Formalization.ActualRingAngleClosure.actual_ring_angle_phase_zero
#print axioms N11Formalization.ActualRingAngleClosure.actual_ring_angle_closure
