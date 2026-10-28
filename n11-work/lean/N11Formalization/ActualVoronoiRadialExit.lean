import N11Formalization.ActualVoronoiCells

/-! Exact radial facet selection for finite nearest-site cells.
The selected bisector is derived by a finite minimum, not assumed from
a polygon drawing or from an unproved first-exit theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualVoronoiRadialExit
open ActualVoronoiCells DSHTopologyInterior ActualHubEssentiality

def ray (p u : Point) (t : ℝ) : Point := p + t • u

theorem ray_difference (p q u : Point) (t : ℝ) :
    dist (ray p u t) q ^ 2 - dist (ray p u t) p ^ 2 =
      ‖q-p‖^2 - 2*t*inner ℝ u (q-p) := by
  simp only [ray, dist_eq_norm, norm_sub_sq_real, norm_add_sq_real,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm]
  ring

theorem ray_dist (p u : Point) (t : ℝ) (hu : ‖u‖ = 1) :
    dist (ray p u t) p = |t| := by
  rw [ray, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs]

theorem ray_cell_iff (c : Fin 11 → Point) (j : Fin 11) (u : Point) (t : ℝ) :
    ray (c j) u t ∈ Cell c j ↔
      ∀ i : Fin 11, 2*t*inner ℝ u (c i-c j) ≤ ‖c i-c j‖^2 := by
  constructor
  · intro hx i
    have hi := hx i
    have he := ray_difference (c j) (c i) u t
    nlinarith [dist_nonneg (x := ray (c j) u t) (y := c j),
      dist_nonneg (x := ray (c j) u t) (y := c i)]
  · intro hx i
    have hi := hx i
    have he := ray_difference (c j) (c i) u t
    nlinarith [dist_nonneg (x := ray (c j) u t) (y := c j),
      dist_nonneg (x := ray (c j) u t) (y := c i)]

structure Exit (c : Fin 11 → Point) (j : Fin 11) (u : Point) (r : ℝ) where
  time : ℝ
  site : Fin 11
  positive : 0 < time
  radius : time ≤ r
  different : site ≠ j
  forward : 0 < inner ℝ u (c site-c j)
  nearest : ray (c j) u time ∈ Cell c j
  active : 2*time*inner ℝ u (c site-c j) = ‖c site-c j‖^2

theorem exists_radial_exit {c : Fin 11 → Point} {j : Fin 11} {u : Point} {r : ℝ}
    (hu : ‖u‖ = 1) (hr : 0 ≤ r)
    (hne : ∀ i : Fin 11, i ≠ j → c i ≠ c j)
    (hbound : Cell c j ⊆ Metric.closedBall (c j) r) :
    Nonempty (Exit c j u r) := by
  classical
  let A : Finset (Fin 11) := Finset.univ.filter (fun i => 0 < inner ℝ u (c i-c j))
  have hA : A.Nonempty := by
    by_contra hnone
    have hall (i : Fin 11) : inner ℝ u (c i-c j) ≤ 0 := by
      by_contra hi
      have hm : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ i, lt_of_not_ge hi⟩
      exact hnone ⟨i, hm⟩
    have hx : ray (c j) u (r+1) ∈ Cell c j := by
      apply (ray_cell_iff c j u (r+1)).mpr
      intro i
      exact (mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2*(r+1))
        (hall i)).trans (sq_nonneg _)
    have hd := Metric.mem_closedBall.mp (hbound hx)
    rw [ray_dist _ _ _ hu, abs_of_nonneg (by linarith : 0 ≤ r+1)] at hd
    linarith
  let T : Fin 11 → ℝ := fun i => ‖c i-c j‖^2/(2*inner ℝ u (c i-c j))
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image A T hA
  have hai : 0 < inner ℝ u (c i-c j) := (Finset.mem_filter.mp hi).2
  have hij : i ≠ j := by
    intro he
    subst i
    simpa only [sub_self, inner_zero_right, lt_self_iff_false] using hai
  have hn : 0 < ‖c i-c j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne i hij))
  have ht : 0 < T i := div_pos (sq_pos_of_pos hn) (by linarith)
  have hcell : ray (c j) u (T i) ∈ Cell c j := by
    apply (ray_cell_iff c j u (T i)).mpr
    intro k
    by_cases hk : 0 < inner ℝ u (c k-c j)
    · have hle := hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)
      have hs := (le_div_iff₀ (by linarith : 0 < 2*inner ℝ u (c k-c j))).mp hle
      nlinarith
    · exact (mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2*T i)
        (le_of_not_gt hk)).trans (sq_nonneg _)
  have hrad := Metric.mem_closedBall.mp (hbound hcell)
  rw [ray_dist _ _ _ hu, abs_of_pos ht] at hrad
  have hactive : 2*T i*inner ℝ u (c i-c j) = ‖c i-c j‖^2 := by
    dsimp [T]
    field_simp
    <;> ring
  exact ⟨⟨T i, i, ht, hrad, hij, hai, hcell, hactive⟩⟩

theorem exit_equidistant {c : Fin 11 → Point} {j : Fin 11} {u : Point} {r : ℝ}
    (e : Exit c j u r) :
    dist (ray (c j) u e.time) (c e.site) = dist (ray (c j) u e.time) (c j) := by
  have he := ray_difference (c j) (c e.site) u e.time
  rw [e.active] at he
  nlinarith [dist_nonneg (x := ray (c j) u e.time) (y := c e.site),
    dist_nonneg (x := ray (c j) u e.time) (y := c j)]

/-- Radius enlargement is applied AFTER selecting an actual-r bisector.
The centres are not changed. -/
theorem enlarged_ray_covered {c : Fin 11 → Point} {j : Fin 11} {u : Point} {r R : ℝ}
    (e : Exit c j u r) (hu : ‖u‖ = 1) (hR : r ≤ R) :
    dist (ray (c j) u R) (c e.site) ≤ R := by
  have hR0 : 0 < R := e.positive.trans_le (e.radius.trans hR)
  have hd := ray_difference (c j) (c e.site) u R
  rw [ray_dist _ _ _ hu, abs_of_pos hR0] at hd
  have hm : 2*e.time*inner ℝ u (c e.site-c j) ≤
      2*R*inner ℝ u (c e.site-c j) :=
    mul_le_mul_of_nonneg_right (by linarith [e.radius]) e.forward.le
  rw [e.active] at hm
  nlinarith [dist_nonneg (x := ray (c j) u R) (y := c e.site)]

end N11Formalization.ActualVoronoiRadialExit
#check @N11Formalization.ActualVoronoiRadialExit.exists_radial_exit
#check @N11Formalization.ActualVoronoiRadialExit.enlarged_ray_covered
#print axioms N11Formalization.ActualVoronoiRadialExit.exists_radial_exit
#print axioms N11Formalization.ActualVoronoiRadialExit.enlarged_ray_covered
