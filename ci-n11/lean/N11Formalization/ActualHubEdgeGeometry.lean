import N11Formalization.ActualVoronoiRadialExit

/-! A common hub nearest point strictly separated from all ring sites
produces a genuine nontrivial hub segment. The degenerate one-point case
therefore has an active ring tie. No general-position assumption is used. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubEdgeGeometry
open ActualVoronoiCells ActualVoronoiRadialExit DSHTopologyInterior

def HubEdge (c : Fin 11 → Point) : Prop :=
  ∃ x y : Point, x ∈ Cell c 9 ∩ Cell c 10 ∧ y ∈ Cell c 9 ∩ Cell c 10 ∧ x ≠ y

def StrictRing (c : Fin 11 → Point) : Set Point :=
  {x | ∀ i : Fin 9, dist x (c 9) < dist x (c ⟨i.val, by omega⟩)}

theorem strictRing_open (c : Fin 11 → Point) : IsOpen (StrictRing c) := by
  have he : StrictRing c = ⋂ i : Fin 9,
      {x : Point | dist x (c 9) < dist x (c ⟨i.val, by omega⟩)} := by
    ext x
    simp only [StrictRing, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) (by fun_prop)

def perp (p : Point) : Point := !₂[-p 1, p 0]

theorem perp_ne {p : Point} (hp : p ≠ 0) : perp p ≠ 0 := by
  intro h
  apply hp
  apply PiLp.ext
  intro i
  fin_cases i
  · have hh := congrArg (fun q : Point => q 1) h
    simpa [perp] using hh
  · have hh := congrArg (fun q : Point => q 0) h
    simpa [perp] using hh

theorem perp_inner (p : Point) : inner ℝ (perp p) p = 0 := by
  rw [PinTangentGeometry.inner_coords]
  simp only [perp, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem square_difference (x a b : Point) :
    dist x a^2-dist x b^2 = ‖a‖^2-‖b‖^2+2*inner ℝ x (b-a) := by
  simp only [dist_eq_norm, norm_sub_sq_real, inner_sub_right]
  ring

theorem shifted_equidistant {x a b v : Point} {t : ℝ}
    (hx : dist x a = dist x b) (hv : inner ℝ v (b-a) = 0) :
    dist (x+t • v) a = dist (x+t • v) b := by
  have h0 := square_difference x a b
  rw [hx, sub_self] at h0
  have h1 := square_difference (x+t • v) a b
  rw [inner_add_left, real_inner_smul_left, hv, mul_zero, add_zero] at h1
  nlinarith [dist_nonneg (x := x+t • v) (y := a), dist_nonneg (x := x+t • v) (y := b)]

theorem edge_of_strict_ring {c : Fin 11 → Point} (hne : c 9 ≠ c 10)
    {x : Point} (hx : x ∈ Cell c 9 ∩ Cell c 10) (hs : x ∈ StrictRing c) : HubEdge c := by
  let v := perp (c 10-c 9)
  have hvne : v ≠ 0 := perp_ne (sub_ne_zero.mpr hne.symm)
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp (strictRing_open c) x hs
  let t := eps/(2*‖v‖)
  have ht : 0 < t := div_pos heps (by linarith)
  let y := x+t • v
  have hdist : dist y x = eps/2 := by
    change dist (ray x v t) x = eps/2
    rw [dist_eq_norm, ray, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp
    <;> ring
  have hys : y ∈ StrictRing c := hball (Metric.mem_ball.mpr (by rw [hdist]; linarith))
  have hxy : x ≠ y := by
    intro he
    have hzero : t • v = 0 := add_left_cancel (by simpa only [y, add_zero] using he.symm)
    rcases smul_eq_zero.mp hzero with h | h
    · exact ht.ne' h
    · exact hvne h
  have hxeq : dist x (c 9) = dist x (c 10) := le_antisymm (hx.1 10) (hx.2 9)
  have hyeq : dist y (c 9) = dist y (c 10) :=
    shifted_equidistant hxeq (perp_inner (c 10-c 9))
  have hy9 : y ∈ Cell c 9 := by
    intro i
    by_cases hi : i.val < 9
    · exact (hys ⟨i.val,hi⟩).le
    · have hic : i = (9 : Fin 11) ∨ i = 10 := by
        have hv := i.isLt
        have : i.val = 9 ∨ i.val = 10 := by omega
        exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
      rcases hic with rfl | rfl
      · exact le_rfl
      · exact hyeq.le
  have hy10 : y ∈ Cell c 10 := by
    intro i
    rw [← hyeq]
    exact hy9 i
  exact ⟨x,y,hx,⟨hy9,hy10⟩,hxy⟩

theorem ring_tie_of_no_edge {c : Fin 11 → Point} (hne : c 9 ≠ c 10)
    (hno : ¬ HubEdge c) {x : Point} (hx : x ∈ Cell c 9 ∩ Cell c 10) :
    ∃ i : Fin 11, i.val < 9 ∧ dist x (c i) = dist x (c 9) := by
  by_contra hnone
  apply hno
  apply edge_of_strict_ring hne hx
  intro i
  by_contra hnot
  have heq : dist x (c ⟨i.val,by omega⟩) = dist x (c 9) :=
    le_antisymm (le_of_not_gt hnot) (hx.1 ⟨i.val,by omega⟩)
  exact hnone ⟨⟨i.val,by omega⟩,i.isLt,heq⟩

end N11Formalization.ActualHubEdgeGeometry
#check @N11Formalization.ActualHubEdgeGeometry.edge_of_strict_ring
#check @N11Formalization.ActualHubEdgeGeometry.ring_tie_of_no_edge
#print axioms N11Formalization.ActualHubEdgeGeometry.edge_of_strict_ring
#print axioms N11Formalization.ActualHubEdgeGeometry.ring_tie_of_no_edge
