import N11Formalization.ActualHubEdgeGeometry

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubEdgeControls
open ActualVoronoiCells ActualHubEdgeGeometry

def east : Point := !₂[1,0]
def north : Point := !₂[0,1]
def crossSites (i : Fin 11) : Point :=
  if i = 9 then east else if i = 10 then -east else if i = 1 then -north else north

theorem site_sq (i : Fin 11) : ‖crossSites i‖^2 = 1 := by
  rw [PinTangentGeometry.norm_sq_coords]
  fin_cases i <;> norm_num [crossSites,east,north,Fin.ext_iff]

theorem site_norm (i : Fin 11) : ‖crossSites i‖ = 1 := by
  nlinarith [site_sq i,norm_nonneg (crossSites i)]

theorem hubs_distinct : crossSites 9 ≠ crossSites 10 := by
  intro h
  have hh := congrArg (fun x : Point => x 0) h
  norm_num [crossSites,east,Fin.ext_iff] at hh

theorem zero_common : (0 : Point) ∈ Cell crossSites 9 ∩ Cell crossSites 10 := by
  constructor <;> intro i <;> rw [dist_zero_left,dist_zero_left,site_norm,site_norm]

theorem common_only_zero {x : Point} (hx : x ∈ Cell crossSites 9 ∩ Cell crossSites 10) :
    x = 0 := by
  have hA := (dist_le_iff_halfspace x (crossSites 9) (crossSites 10)).mp (hx.1 10)
  have hB := (dist_le_iff_halfspace x (crossSites 10) (crossSites 9)).mp (hx.2 9)
  have hC := (dist_le_iff_halfspace x (crossSites 9) (crossSites 0)).mp (hx.1 0)
  have hD := (dist_le_iff_halfspace x (crossSites 9) (crossSites 1)).mp (hx.1 1)
  rw [site_sq,site_sq] at hA hB hC hD
  norm_num [PinTangentGeometry.inner_coords,crossSites,east,north,PiLp.sub_apply,Fin.ext_iff]
    at hA hB hC hD
  apply PiLp.ext
  intro i
  fin_cases i
  · change x 0 = 0
    linarith
  · change x 1 = 0
    linarith

/-- Common nearest point plus distinct hubs does NOT imply a positive edge. -/
theorem common_without_edge : (Cell crossSites 9 ∩ Cell crossSites 10).Nonempty ∧
    crossSites 9 ≠ crossSites 10 ∧ ¬ HubEdge crossSites := by
  refine ⟨⟨0,zero_common⟩,hubs_distinct,?_⟩
  rintro ⟨x,y,hx,hy,hxy⟩
  exact hxy ((common_only_zero hx).trans (common_only_zero hy).symm)

theorem not_small_cover : ¬ Covers crossSites (19/50) := by
  intro hc
  obtain ⟨i,hi⟩ := hc 0 zero_mem_unitDisk
  rw [dist_zero_left,site_norm] at hi
  norm_num at hi

end N11Formalization.ActualHubEdgeControls
#check @N11Formalization.ActualHubEdgeControls.common_without_edge
#print axioms N11Formalization.ActualHubEdgeControls.common_without_edge
#print axioms N11Formalization.ActualHubEdgeControls.not_small_cover
