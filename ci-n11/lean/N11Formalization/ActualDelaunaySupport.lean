import N11Formalization.ActualHubEdgeEndpointGeometry

/-! True empty-nearest-circle supporting planes and strict radial exposure.
All statements apply to ACTUAL cells and arbitrary degenerate configurations.
This is a producer for polygonal Delaunay faces, not a claim that an arbitrary
global triangulation clips to the required disk complex. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualDelaunaySupport
open ActualVoronoiCells ActualHubEdgeGeometry ActualHubEdgeEndpointGeometry

def lift (p : Point) : Point × ℝ := (p,‖p‖^2)
def support (v : Point) (p : Point × ℝ) : ℝ := p.2-2*inner ℝ v p.1

theorem support_lift (v p : Point) :
    support v (lift p) = dist v p^2-‖v‖^2 := by
  rw [support,lift,dist_eq_norm,norm_sub_sq_real]
  ring

theorem nearest_support {c : Fin 11 → Point} {v : Point} {i : Fin 11}
    (hi : v ∈ Cell c i) (j : Fin 11) : support v (lift (c i)) ≤ support v (lift (c j)) := by
  rw [support_lift,support_lift]
  have hd := hi j
  nlinarith [dist_nonneg (x := v) (y := c i),dist_nonneg (x := v) (y := c j)]

theorem support_combo (v : Point) (p q : Point × ℝ) (a b : ℝ) :
    support v (a • p+b • q) = a*support v p+b*support v q := by
  change a*p.2+b*q.2-2*inner ℝ v (a • p.1+b • q.1) =
    a*(p.2-2*inner ℝ v p.1)+b*(q.2-2*inner ℝ v q.1)
  simp only [inner_add_right,real_inner_smul_right]
  ring

theorem support_halfspace_convex (v : Point) (q : ℝ) :
    Convex ℝ {p : Point × ℝ | q ≤ support v p} := by
  intro x hx y hy a b ha hb hab
  rw [Set.mem_setOf_eq,support_combo]
  have hA := mul_nonneg ha (sub_nonneg.mpr hx)
  have hB := mul_nonneg hb (sub_nonneg.mpr hy)
  have he := congrArg (fun t : ℝ => t*q) hab
  nlinarith

/-- A TRUE nearest point supplies a supporting lower plane of the entire
lifted finite site set. No guessed source face table. -/
theorem convexHull_support {c : Fin 11 → Point} {v : Point} {i : Fin 11}
    (hi : v ∈ Cell c i) :
    convexHull ℝ (Set.range (fun j => lift (c j))) ⊆
      {p : Point × ℝ | support v (lift (c i)) ≤ support v p} := by
  apply convexHull_min _ (support_halfspace_convex _ _)
  rintro _ ⟨j,rfl⟩
  exact nearest_support hi j

theorem strict_radial_exposure {v a b : Point} (hab : a ≠ b)
    (htie : dist v a = dist v b) :
    inner ℝ (a-v) (b-v) < inner ℝ (a-v) (a-v) := by
  have hne : 0 < dist a b := dist_pos.mpr hab
  have ha : ‖a-v‖ = dist v a := by rw [dist_comm,dist_eq_norm]
  have hb : ‖b-v‖ = dist v b := by rw [dist_comm,dist_eq_norm]
  have hsq := norm_sub_sq_real (a-v) (b-v)
  have hdiff : (a-v)-(b-v) = a-b := by abel
  rw [hdiff,ha,hb,← dist_eq_norm,← htie] at hsq
  rw [real_inner_self_eq_norm_sq,ha]
  nlinarith

/-- Every incident ACTUAL site has its own strict maximizing direction on
the incident circle; collinear/tangent zero-sector assumptions are not used. -/
theorem incident_sites_strictly_exposed {c : Fin 11 → Point}
    (hc : Function.Injective c) {v : Point} {i j : Fin 11} (hij : i ≠ j)
    (hi : v ∈ Cell c i) (hj : v ∈ Cell c j) :
    inner ℝ (c i-v) (c j-v) < inner ℝ (c i-v) (c i-v) :=
  strict_radial_exposure (fun he => hij (hc he)) (le_antisymm (hi j) (hj i))

theorem common_nearest_radius_pos {c : Fin 11 → Point} (hc : Function.Injective c)
    {v : Point} {i j : Fin 11} (hij : i ≠ j)
    (hi : v ∈ Cell c i) (hj : v ∈ Cell c j) : 0 < dist v (c i) := by
  apply lt_of_le_of_ne dist_nonneg
  intro he
  have hv : v = c i := dist_eq_zero.mp he.symm
  have heq := le_antisymm (hi j) (hj i)
  have hvj : v = c j := dist_eq_zero.mp (by rw [← heq,he.symm])
  exact hij (hc (hv.symm.trans hvj))

end N11Formalization.ActualDelaunaySupport
#check @N11Formalization.ActualDelaunaySupport.convexHull_support
#check @N11Formalization.ActualDelaunaySupport.incident_sites_strictly_exposed
#print axioms N11Formalization.ActualDelaunaySupport.convexHull_support
#print axioms N11Formalization.ActualDelaunaySupport.incident_sites_strictly_exposed
