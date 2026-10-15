import N11Formalization.SharedMomentFacePlaneRoundedGradientCertificate
import N11Formalization.MetricSectorLocalGradientCertificate
import N11Formalization.CanonicalBalancedGraphOrbits

/-! Semantic controls for the A25 certificate boundaries. These give
actual admissible points lost by incorrect pruning or radius rounding,
and distinguish sector owners from reflected switch edges. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentA25CertificateControls
open RationalBoxSubdivision SharedMomentFacePlaneCertificate
open SharedMomentFacePlaneGradientCertificate SharedMomentFacePlaneRoundedGradientCertificate
open SharedMomentFactorGridCertificate SharedMomentFactorIntervalCertificate
open SharedMomentFactorLocalGradientCertificate CompactQuadraticMomentMaximum
open CompactQuadraticArgmaxRange MetricSectorLocalGradientCertificate
open CanonicalBalancedGraphOrbits ActualRingLinkBoundaryData

def boundaryPlaneCell : Cell (Fin 2) :=
  ![⟨RatInterval.piLo,RatInterval.piHi⟩,RatInterval.ofRat 0]

theorem boundary_plane_mem : Mem boundaryPlaneCell (![Real.pi,0] : Fin 2 → ℝ) := by
  intro i
  fin_cases i
  · exact ⟨RatInterval.piLo_lt_pi.le,RatInterval.pi_lt_piHi.le⟩
  · norm_num [boundaryPlaneCell,RatInterval.ofRat,RatInterval.mem_iff]

/-- Replacing piHi by piLo in the lower-endpoint prune loses a genuine
closed simplex boundary, even with both retained coordinates nonnegative. -/
theorem wrong_piLo_prune_discards_boundary :
    RatInterval.piLo ≤ (boundaryPlaneCell 0).lo+(boundaryPlaneCell 1).lo ∧
    Mem boundaryPlaneCell (![Real.pi,0] : Fin 2 → ℝ) ∧
    (∀ s, planeAngles (![Real.pi,0] : Fin 2 → ℝ) s ∈ Set.Icc (0 : ℝ) Real.pi) ∧
    ¬ PlaneOutside boundaryPlaneCell := by
  refine ⟨by simp [boundaryPlaneCell,RatInterval.ofRat],boundary_plane_mem,?_,?_⟩
  · intro s
    fin_cases s <;> simp [planeAngles,Real.pi_pos.le]
  · exact plane_not_outside boundary_plane_mem (by simp)

/-- The failure persists when the incorrect piLo test is strict. -/
theorem wrong_piLo_strict_prune_discards_boundary :
    ∃ B : Cell (Fin 2), RatInterval.piLo < (B 0).lo+(B 1).lo ∧
      Mem B (![Real.pi,0] : Fin 2 → ℝ) ∧ ¬ PlaneOutside B := by
  obtain ⟨r,hl,hr⟩ := exists_rat_btwn RatInterval.piLo_lt_pi
  let B : Cell (Fin 2) := ![⟨r,RatInterval.piHi⟩,RatInterval.ofRat 0]
  have hx : Mem B (![Real.pi,0] : Fin 2 → ℝ) := by
    intro i
    fin_cases i
    · exact ⟨hr.le,RatInterval.pi_lt_piHi.le⟩
    · norm_num [B,RatInterval.ofRat,RatInterval.mem_iff]
  refine ⟨B,?_,hx,plane_not_outside hx (by simp)⟩
  change RatInterval.piLo < r+0
  simp only [add_zero]
  exact_mod_cast hl

/-- Positive derivative leaves exclude zero chord at nonzero coincident
endpoints, so they cannot replace the full-sector fallback. -/
theorem zero_chord_cell_not_gradient_valid {B : Cell (Fin 3)}
    (hx : Mem B (![0,1,1] : Fin 3 → ℝ))
    (K : MetricSectorRationalCellCertificate.CellBounds) (D : GradientBounds) :
    ¬ GradientValid B K D := by
  intro hD
  have hp := (point_positive hD hx).1
  simp [chordSq] at hp
  exact absurd hp (by norm_num)

theorem zero_chord_cell_not_positive_certificate {B : Cell (Fin 3)}
    (hx : Mem B (![0,1,1] : Fin 3 → ℝ)) (C mu dL dR bL bR M : ℚ) :
    ¬ Nonempty (PositiveCertificate C mu dL dR bL bR M B) := by
  rintro ⟨cert⟩
  exact zero_chord_cell_not_gradient_valid hx cert.cell_bounds cert.denominator_bounds cert.valid

/-- At the true pi boundary q=b=0 makes every radius maximize the same
quadratic. The exact corner enclosure must retain its endpoint y=1. -/
theorem flat_plane_endpoint_mem {B : Cell (Fin 2)}
    (hx : Mem B (![Real.pi,0] : Fin 2 → ℝ)) :
    (planeRadiusCell (fun _ => 0) (fun _ => 0) B).Mem 1 := by
  have ha := plane_domain_cell_mem hx (by simp [Real.pi_pos.le])
  have hA := face_quadratic_mem (fun _ => 0) ha
  have hB := face_linear_mem (fun _ => 0) ha
  have hzA : faceQuadratic (fun _ => 0) (planeAngles (![Real.pi,0] : Fin 2 → ℝ))=0 := by
    simp [faceQuadratic,planeAngles]
  have hzB : faceLinear (fun _ => 0) (planeAngles (![Real.pi,0] : Fin 2 → ℝ))=0 := by
    simp [faceLinear]
  simp only [Rat.cast_zero] at hA hB
  rw [hzA] at hA
  rw [hzB] at hB
  exact maximizer_rational_enclosure hA.1 hA.2 hB.1 hB.2
    (by norm_num) (zero_coefficients_all_maximizers 1)

theorem flat_plane_rounded_endpoint_retained {B : Cell (Fin 2)} {Y : RatInterval}
    (hx : Mem B (![Real.pi,0] : Fin 2 → ℝ))
    (hY : RadiusContains (fun _ => 0) (fun _ => 0) B Y) : Y.Mem 1 :=
  radius_mem_of_contains hY (flat_plane_endpoint_mem hx)

theorem inward_radius_rounding_rejected {B : Cell (Fin 2)} {Y : RatInterval}
    (hx : Mem B (![Real.pi,0] : Fin 2 → ℝ)) (hhi : Y.hi < 1) :
    ¬ RadiusContains (fun _ => 0) (fun _ => 0) B Y := by
  intro hY
  have hmem := (flat_plane_rounded_endpoint_retained hx hY).2
  have hh : (Y.hi : ℝ) < 1 := by exact_mod_cast hhi
  linarith only [hmem,hh]

/-- Reflection sends a sector's owner by -i-2. The switch offset -i-1
fails on the actual labelled owner already at i=0. -/
theorem reflection_switch_offset_fails_sector_owner :
    reflectionPerm (nextSite (0 : Fin 9))=nextSite (-(0 : Fin 9)-2) ∧
    reflectionPerm (nextSite (0 : Fin 9))≠nextSite (-(0 : Fin 9)-1) := by
  constructor
  · exact reflection_sector_owner 0
  · decide +kernel

theorem equal_p_plane_gradient_cancels (c : ℝ) (q b a : Fin 3 → ℝ) (y : ℝ) :
    planeGradient (fun _ => c) q b a y=planeGradient (fun _ => 0) q b a y := by
  funext i
  fin_cases i <;> simp [planeGradient,faceGradient] <;> ring

/-- Gradient cancellation does not remove the paid constant c*pi. -/
theorem equal_p_envelope_keeps_pi (c : ℝ) (q b a : Fin 3 → ℝ)
    (hsum : (∑ s : Fin 3, a s)=Real.pi) :
    faceEnvelope (fun _ => c) q b a=c*Real.pi+faceEnvelope (fun _ => 0) q b a := by
  rw [← hsum]
  simp only [faceEnvelope,Fin.sum_univ_three,zero_mul,zero_add]
  ring

theorem zero_plane_gradient_can_have_positive_value :
    planeGradient (fun _ => 1) (fun _ => 0) (fun _ => 0)
      (planeAngles (![Real.pi,0] : Fin 2 → ℝ)) 1=(fun _ => 0) ∧
    faceObjective (fun _ => 1) (fun _ => 0) (fun _ => 0)
      (planeAngles (![Real.pi,0] : Fin 2 → ℝ)) 1=Real.pi ∧ 0<Real.pi := by
  refine ⟨?_,?_,Real.pi_pos⟩
  · funext i
    fin_cases i <;> simp [planeGradient,faceGradient,faceQuadraticGradient,planeAngles,next,prev]
  · simp [faceObjective,faceQuadratic,faceLinear,planeAngles,Fin.sum_univ_three,quad]

end N11Formalization.SharedMomentA25CertificateControls
#print axioms N11Formalization.SharedMomentA25CertificateControls.wrong_piLo_prune_discards_boundary
#print axioms N11Formalization.SharedMomentA25CertificateControls.wrong_piLo_strict_prune_discards_boundary
#print axioms N11Formalization.SharedMomentA25CertificateControls.zero_chord_cell_not_gradient_valid
#print axioms N11Formalization.SharedMomentA25CertificateControls.zero_chord_cell_not_positive_certificate
#print axioms N11Formalization.SharedMomentA25CertificateControls.flat_plane_endpoint_mem
#print axioms N11Formalization.SharedMomentA25CertificateControls.flat_plane_rounded_endpoint_retained
#print axioms N11Formalization.SharedMomentA25CertificateControls.inward_radius_rounding_rejected
#print axioms N11Formalization.SharedMomentA25CertificateControls.reflection_switch_offset_fails_sector_owner
#print axioms N11Formalization.SharedMomentA25CertificateControls.equal_p_plane_gradient_cancels
#print axioms N11Formalization.SharedMomentA25CertificateControls.equal_p_envelope_keeps_pi
#print axioms N11Formalization.SharedMomentA25CertificateControls.zero_plane_gradient_can_have_positive_value
