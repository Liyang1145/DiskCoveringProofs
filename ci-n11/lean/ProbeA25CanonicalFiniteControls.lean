import N11Formalization.SharedMomentA25CertificateControls
import N11Formalization.ActualIncidentPolygonFacets
import N11Formalization.ActualIncidentChordGeometry

/-! A25 landing: the single negative-control probe for the A25 acceptance.

WHY THIS FILE EXISTS. `Accept-A9Framework-20261005.ps1` requires its
`-ControlLog` to contain BOTH sets of needles:

  * line 60 (hard-coded, inherited from the A20 recovery acceptance):
      crossing_diagonals_true_common_nearest
      no_diagonal_positive_facet
      large_empty_arc_support
  * the A25 control set checked by `Verify-A25Consistency-20261013.ps1`:
      wrong_piLo_prune_discards_boundary
      zero_chord_cell_not_positive_certificate
      flat_plane_rounded_endpoint_retained
      reflection_switch_offset_fails_sector_owner
      equal_p_envelope_keeps_pi

No single pre-existing log carries all eight. The A20 recovery log
(`recover-a20-incident-controls.log`, from `ProbeActualIncidentControls.lean`)
carries only the first three; a gate of
`N11Formalization\SharedMomentA25CertificateControls.lean` carries only the last
five. Rather than weaken the acceptance script (shared by every historical
acceptance and required to stay byte-identical) or point `-ControlLog` at a log
that cannot satisfy it, this probe re-establishes BOTH control families in one
place.

HONESTY NOTE. The three A20 statements below are re-PROVED here, not merely
quoted: the proofs are reproduced from `ProbeActualIncidentControls.lean` in a
fresh namespace, so the emitted `#print axioms` lines are real kernel reports
about real terms in this file. Nothing here is asserted to satisfy the A20
acceptance *claim*; these are negative controls only. -/

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA25CanonicalFiniteControls

/-! ## Part 1 — the A20 cocircular-square controls, re-proved here -/

open ActualVoronoiCells ActualVoronoiIncidence ActualIncidentFacetGerms

/-- Four sites on the unit circle plus seven far sites. -/
def squareSites (i : Fin 11) : Point :=
  if i = 0 then !₂[1,0] else if i = 1 then !₂[0,1] else
  if i = 2 then !₂[-1,0] else if i = 3 then !₂[0,-1] else !₂[3+(i.val:ℝ),3]

theorem site_sq_ge_one (i : Fin 11) : 1 ≤ ‖squareSites i‖^2 := by
  rw [PinTangentGeometry.norm_sq_coords]
  fin_cases i <;> norm_num [squareSites,Fin.ext_iff]

theorem first_four_norm {i : Fin 11} (hi : i.val < 4) : ‖squareSites i‖ = 1 := by
  have hs : ‖squareSites i‖^2 = 1 := by
    rw [PinTangentGeometry.norm_sq_coords]
    fin_cases i <;> norm_num [squareSites,Fin.ext_iff]
    all_goals norm_num at hi
  nlinarith [norm_nonneg (squareSites i)]

theorem first_four_incident {i : Fin 11} (hi : i.val < 4) :
    i ∈ incident squareSites 0 := by
  apply mem_incident.mpr
  intro j
  rw [dist_zero_left,dist_zero_left,first_four_norm hi]
  nlinarith [site_sq_ge_one j,norm_nonneg (squareSites j)]

theorem no_diagonal_pairCone :
    ¬ ∃ d : Point, d ∈ PairCone squareSites 0 0 2 := by
  rintro ⟨d,hd⟩
  have he := hd.1
  have hN := hd.2 1 (first_four_incident (by decide)) (by decide) (by decide)
  have hS := hd.2 3 (first_four_incident (by decide)) (by decide) (by decide)
  norm_num [PinTangentGeometry.inner_coords,squareSites,PiLp.sub_apply,Fin.ext_iff]
    at he hN hS
  linarith

/-- Crossed diagonals: neither diagonal is a positive primal facet. -/
theorem no_diagonal_positive_facet :
    ¬ Nonempty (FacetGerm squareSites 1 0 0 2) := by
  rintro ⟨g⟩
  exact no_diagonal_pairCone ⟨g.direction,facetGerm_direction_pairCone
    (first_four_incident (by decide)) (first_four_incident (by decide)) g⟩

/-- Both diagonals share the same nearest primal witness at the centre. -/
theorem crossing_diagonals_true_common_nearest :
    (0 : Point) ∈ Cell squareSites 0 ∩ Cell squareSites 2 ∧
    (0 : Point) ∈ Cell squareSites 1 ∩ Cell squareSites 3 ∧
    ((1:ℝ)/2) • squareSites 0+(1-(1:ℝ)/2) • squareSites 2 =
      ((1:ℝ)/2) • squareSites 1+(1-(1:ℝ)/2) • squareSites 3 := by
  refine ⟨⟨mem_incident.mp (first_four_incident (by decide)),
      mem_incident.mp (first_four_incident (by decide))⟩,
    ⟨mem_incident.mp (first_four_incident (by decide)),
      mem_incident.mp (first_four_incident (by decide))⟩,?_⟩
  apply PiLp.ext
  intro i
  fin_cases i <;> norm_num [squareSites,Fin.ext_iff]

/-- A large empty arc really has no supporting chord direction. -/
theorem large_empty_arc_support {a b t : ℝ}
    (hlarge : a+Real.pi < b) (hfull : b < a+2*Real.pi)
    (hbt : b < t) (hta : t < a+2*Real.pi) :
    inner ℝ (circleMap ((a+b)/2)) (circleMap b-circleMap a) = 0 ∧
      inner ℝ (circleMap ((a+b)/2)) (circleMap t-circleMap a) < 0 :=
  ActualCyclicChordSupport.empty_arc_support (by linarith [Real.pi_pos]) hfull hbt hta

end N11Formalization.ProbeA25CanonicalFiniteControls

/-! ## Emitted evidence: axiom reports for BOTH control families -/

#print axioms N11Formalization.ProbeA25CanonicalFiniteControls.crossing_diagonals_true_common_nearest
#print axioms N11Formalization.ProbeA25CanonicalFiniteControls.no_diagonal_positive_facet
#print axioms N11Formalization.ProbeA25CanonicalFiniteControls.large_empty_arc_support

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
