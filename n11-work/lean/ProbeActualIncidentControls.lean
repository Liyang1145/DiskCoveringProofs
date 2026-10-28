import N11Formalization.ActualIncidentPolygonFacets
import N11Formalization.ActualIncidentChordGeometry

/-! Genuine cocircular-square negative controls: both diagonals have the
same nearest primal witness, yet neither is a positive primal facet.
Thus crossed_edges_same_primal_vertex cannot replace coherent refinement. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeActualIncidentControls
open ActualVoronoiCells ActualVoronoiIncidence ActualIncidentFacetGerms

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

theorem no_diagonal_positive_facet :
    ¬ Nonempty (FacetGerm squareSites 1 0 0 2) := by
  rintro ⟨g⟩
  exact no_diagonal_pairCone ⟨g.direction,facetGerm_direction_pairCone
    (first_four_incident (by decide)) (first_four_incident (by decide)) g⟩

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

theorem large_empty_arc_support {a b t : ℝ}
    (hlarge : a+Real.pi < b) (hfull : b < a+2*Real.pi)
    (hbt : b < t) (hta : t < a+2*Real.pi) :
    inner ℝ (circleMap ((a+b)/2)) (circleMap b-circleMap a) = 0 ∧
      inner ℝ (circleMap ((a+b)/2)) (circleMap t-circleMap a) < 0 :=
  ActualCyclicChordSupport.empty_arc_support (by linarith [Real.pi_pos]) hfull hbt hta

end N11Formalization.ProbeActualIncidentControls
#check @N11Formalization.ProbeActualIncidentControls.crossing_diagonals_true_common_nearest
#check @N11Formalization.ProbeActualIncidentControls.no_diagonal_positive_facet
#print axioms N11Formalization.ProbeActualIncidentControls.crossing_diagonals_true_common_nearest
#print axioms N11Formalization.ProbeActualIncidentControls.no_diagonal_positive_facet
#print axioms N11Formalization.ProbeActualIncidentControls.large_empty_arc_support
