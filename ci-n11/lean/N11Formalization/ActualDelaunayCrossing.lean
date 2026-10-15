import N11Formalization.ActualDelaunaySupport

/-! Straight dual crossing control from ACTUAL nearest witnesses.
Two crossed edges at strictly positive convex coefficients must have the
SAME primal witness (a possible degenerate polygon face). Thus distinct
primal faces cannot cross. Coincident-witness polygon diagonals are NOT
declared noncrossing; they still require a coherent polygon triangulation. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualDelaunayCrossing
open ActualDelaunaySupport ActualVoronoiCells ActualHubEdgeEndpointGeometry

theorem weighted_support_same_projection (v : Point) (a b k l : Point)
    (s t : ℝ) (hpoint : s • a+(1-s) • b = t • k+(1-t) • l) :
    (s*support v (lift a)+(1-s)*support v (lift b))-
      (t*support v (lift k)+(1-t)*support v (lift l)) =
    (s*‖a‖^2+(1-s)*‖b‖^2)-(t*‖k‖^2+(1-t)*‖l‖^2) := by
  have hi := congrArg (fun p : Point => inner ℝ v p) hpoint
  simp only [inner_add_right,real_inner_smul_right] at hi
  dsimp [support,lift]
  nlinarith

theorem support_eq_iff_dist_eq (v a b : Point) :
    support v (lift a) = support v (lift b) ↔ dist v a = dist v b := by
  rw [support_lift,support_lift]
  constructor
  · intro he
    nlinarith [dist_nonneg (x := v) (y := a),dist_nonneg (x := v) (y := b)]
  · intro he
    rw [he]

theorem crossing_forces_incidence {c : Fin 11 → Point} {u v : Point}
    {i j k l : Fin 11}
    (hui : u ∈ Cell c i) (huj : u ∈ Cell c j)
    (hvk : v ∈ Cell c k) (hvl : v ∈ Cell c l)
    {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hpoint : s • c i+(1-s) • c j = t • c k+(1-t) • c l) :
    u ∈ Cell c k ∩ Cell c l ∧ v ∈ Cell c i ∩ Cell c j := by
  let qU := support u (lift (c i))
  let qV := support v (lift (c k))
  have hUj : support u (lift (c j)) = qU :=
    (support_eq_iff_dist_eq _ _ _).mpr (le_antisymm (huj i) (hui j))
  have hVl : support v (lift (c l)) = qV :=
    (support_eq_iff_dist_eq _ _ _).mpr (le_antisymm (hvl k) (hvk l))
  have hUk : qU ≤ support u (lift (c k)) := nearest_support hui k
  have hUl : qU ≤ support u (lift (c l)) := nearest_support hui l
  have hVi : qV ≤ support v (lift (c i)) := nearest_support hvk i
  have hVj : qV ≤ support v (lift (c j)) := nearest_support hvk j
  have hweightU : qU ≤ t*support u (lift (c k))+(1-t)*support u (lift (c l)) := by
    nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr hUk),
      mul_nonneg (by linarith : 0 ≤ 1-t) (sub_nonneg.mpr hUl)]
  have hweightV : qV ≤ s*support v (lift (c i))+(1-s)*support v (lift (c j)) := by
    nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hVi),
      mul_nonneg (by linarith : 0 ≤ 1-s) (sub_nonneg.mpr hVj)]
  have hU := weighted_support_same_projection u (c i) (c j) (c k) (c l) s t hpoint
  have hV := weighted_support_same_projection v (c i) (c j) (c k) (c l) s t hpoint
  rw [hUj] at hU
  change (s*qU+(1-s)*qU)-(t*support u (lift (c k))+(1-t)*support u (lift (c l))) = _ at hU
  rw [hVl] at hV
  change (s*support v (lift (c i))+(1-s)*support v (lift (c j)))-(t*qV+(1-t)*qV) = _ at hV
  have hsumU : t*support u (lift (c k))+(1-t)*support u (lift (c l)) = qU := by linarith
  have hsumV : s*support v (lift (c i))+(1-s)*support v (lift (c j)) = qV := by linarith
  have hUkEq : support u (lift (c k)) = qU := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) (sub_nonneg.mpr hUl)]
  have hUlEq : support u (lift (c l)) = qU := by
    nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr hUk)]
  have hViEq : support v (lift (c i)) = qV := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-s) (sub_nonneg.mpr hVj)]
  have hVjEq : support v (lift (c j)) = qV := by
    nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hVi)]
  have huKdist := (support_eq_iff_dist_eq _ _ _).mp hUkEq
  have huLdist := (support_eq_iff_dist_eq _ _ _).mp hUlEq
  have hvIdist := (support_eq_iff_dist_eq _ _ _).mp hViEq
  have hvJdist := (support_eq_iff_dist_eq _ _ _).mp hVjEq
  exact ⟨⟨fun a => by rw [huKdist]; exact hui a,
      fun a => by rw [huLdist]; exact hui a⟩,
    ⟨fun a => by rw [hvIdist]; exact hvk a,fun a => by rw [hvJdist]; exact hvk a⟩⟩

theorem crossed_edges_same_primal_vertex {c : Fin 11 → Point} (hc : Function.Injective c)
    {u v : Point} {i j k l : Fin 11} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hui : u ∈ Cell c i) (huj : u ∈ Cell c j)
    (hvk : v ∈ Cell c k) (hvl : v ∈ Cell c l)
    {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hpoint : s • c i+(1-s) • c j = t • c k+(1-t) • c l) : u = v := by
  obtain ⟨huKL,hvIJ⟩ := crossing_forces_incidence hui huj hvk hvl hs0 hs1 ht0 ht1 hpoint
  by_contra huv
  rcases two_points_three_sites (fun he => hij (hc he)) huv
    (le_antisymm (hui j) (huj i)) (le_antisymm (hvIJ.1 j) (hvIJ.2 i))
    (le_antisymm (huKL.1 i) (hui k)) (le_antisymm (hvk i) (hvIJ.1 k)) with he | he
  · exact hki (hc he)
  · exact hkj (hc he)

end N11Formalization.ActualDelaunayCrossing
#check @N11Formalization.ActualDelaunayCrossing.crossed_edges_same_primal_vertex
#print axioms N11Formalization.ActualDelaunayCrossing.crossed_edges_same_primal_vertex
