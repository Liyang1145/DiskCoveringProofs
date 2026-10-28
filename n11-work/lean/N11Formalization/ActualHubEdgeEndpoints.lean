import N11Formalization.ActualHubEdgeEndpointGeometry
import N11Formalization.ActualVoronoiRadialExit

/-! Two genuine distinct hub/ring nearest vertices from an ACTUAL cover.
Their ring labels are produced, NOT assumed to be canonical0/4.
Metric/two-fan classification is still required before that relabeling. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubEdgeEndpoints
open ActualVoronoiCells ActualHubEdgeGeometry ActualHubEdgeEndpointGeometry
open ActualVoronoiRadialExit ActualCoverStructuralReduction ActualRingDirectionOrder

theorem common_of_ring_le {c : Fin 11 → Point} {z : Point}
    (heq : dist z (c 9) = dist z (c 10))
    (hring : ∀ i : Fin 9, dist z (c 9) ≤ dist z (c (ringSite i))) :
    z ∈ Cell c 9 ∩ Cell c 10 := by
  have h9 : z ∈ Cell c 9 := by
    intro i
    by_cases hi : i.val < 9
    · exact hring ⟨i.val,hi⟩
    · have hcases : i = (9 : Fin 11) ∨ i = 10 := by
        have hv := i.isLt
        have : i.val = 9 ∨ i.val = 10 := by omega
        exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
      rcases hcases with rfl | rfl
      · exact le_rfl
      · exact heq.le
  refine ⟨h9,?_⟩
  intro i
  rw [← heq]
  exact h9 i

theorem moving_gap (z u a b : Point) (t : ℝ) :
    dist (ray z u t) b^2-dist (ray z u t) a^2 =
      (dist z b^2-dist z a^2)-2*t*inner ℝ u (b-a) := by
  rw [square_difference (ray z u t) b a,square_difference z b a]
  simp only [ray,inner_add_left,real_inner_smul_left,inner_sub_right]
  ring

structure RingExit (c : Fin 11 → Point) (z u : Point) where
  time : ℝ
  ring : Fin 9
  positive : 0 < time
  nearest : ray z u time ∈ Cell c 9 ∩ Cell c 10
  ring_tie : dist (ray z u time) (c (ringSite ring)) = dist (ray z u time) (c 9)

theorem exists_ring_exit {c : Fin 11 → Point} {r : ℝ} (h : Representative c r)
    {z u : Point} (hz : z ∈ Cell c 9 ∩ Cell c 10) (hs : z ∈ StrictRing c)
    (hu : ‖u‖ = 1) (horth : inner ℝ u (c 10-c 9) = 0) :
    Nonempty (RingExit c z u) := by
  classical
  let G : Fin 9 → ℝ := fun i => dist z (c (ringSite i))^2-dist z (c 9)^2
  let B : Fin 9 → ℝ := fun i => inner ℝ u (c (ringSite i)-c 9)
  have hG (i : Fin 9) : 0 < G i := by
    have hi := hs i
    change dist z (c 9) < dist z (c (ringSite i)) at hi
    dsimp [G]
    nlinarith [dist_nonneg (x := z) (y := c (ringSite i)),dist_nonneg (x := z) (y := c 9)]
  have heq : dist z (c 9) = dist z (c 10) := le_antisymm (hz.1 10) (hz.2 9)
  have halong (t : ℝ) (ht : ∀ i : Fin 9, 2*t*B i ≤ G i) :
      ray z u t ∈ Cell c 9 ∩ Cell c 10 := by
    apply common_of_ring_le (shifted_equidistant heq horth)
    intro i
    have hdiff := moving_gap z u (c 9) (c (ringSite i)) t
    have hi := ht i
    change 2*t*inner ℝ u (c (ringSite i)-c 9) ≤
      dist z (c (ringSite i))^2-dist z (c 9)^2 at hi
    change dist (ray z u t) (c 9) ≤ dist (ray z u t) (c (ringSite i))
    nlinarith [dist_nonneg (x := ray z u t) (y := c 9),
      dist_nonneg (x := ray z u t) (y := c (ringSite i))]
  let S : Finset (Fin 9) := Finset.univ.filter (fun i => 0 < B i)
  have hS : S.Nonempty := by
    by_contra hnone
    have hB (i : Fin 9) : B i ≤ 0 := by
      by_contra hnot
      exact hnone ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,lt_of_not_ge hnot⟩⟩
    let T := r+dist z (c 9)+1
    have hT : 0 < T := by
      dsimp [T]
      linarith [Covers.nonneg h.cover,dist_nonneg (x := z) (y := c 9)]
    have hw := halong T (fun i =>
      (mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2*T) (hB i)).trans (hG i).le)
    have hrad := Metric.mem_closedBall.mp (h.cells.radius 9 (by decide) hw.1)
    have htri := dist_triangle (ray z u T) (c 9) z
    rw [ray_dist _ _ _ hu,abs_of_pos hT,dist_comm (c 9) z] at htri
    dsimp [T] at htri
    linarith
  let F : Fin 9 → ℝ := fun i => G i/(2*B i)
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image S F hS
  have hBi : 0 < B i := (Finset.mem_filter.mp hi).2
  have ht : 0 < F i := div_pos (hG i) (by linarith)
  have hw := halong (F i) (by
    intro k
    by_cases hk : 0 < B k
    · have hle := hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ k,hk⟩)
      have hm := (le_div_iff₀ (by linarith : 0 < 2*B k)).mp hle
      nlinarith
    · exact (mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2*F i)
        (le_of_not_gt hk)).trans (hG k).le)
  have hactive : 2*F i*B i = G i := by dsimp [F]; field_simp <;> ring
  have hdiff := moving_gap z u (c 9) (c (ringSite i)) (F i)
  change dist (ray z u (F i)) (c (ringSite i))^2-dist (ray z u (F i)) (c 9)^2 =
    G i-2*F i*B i at hdiff
  rw [hactive,sub_self] at hdiff
  have htie : dist (ray z u (F i)) (c (ringSite i)) = dist (ray z u (F i)) (c 9) := by
    nlinarith [dist_nonneg (x := ray z u (F i)) (y := c (ringSite i)),
      dist_nonneg (x := ray z u (F i)) (y := c 9)]
  exact ⟨⟨F i,i,ht,hw,htie⟩⟩

structure HubRingVertex (c : Fin 11 → Point) (r : ℝ) where
  point : Point
  ring : Fin 9
  inside : ‖point‖ < 1
  nearest : point ∈ Cell c 9 ∩ Cell c 10
  ring_tie : dist point (c (ringSite ring)) = dist point (c 9)
  radius : dist point (c 9) ≤ r

def vertex_of_exit {c : Fin 11 → Point} {r : ℝ} (h : Representative c r)
    {z u : Point} (e : RingExit c z u) : HubRingVertex c r :=
  ⟨ray z u e.time,e.ring,h.cells.inside 9 (by decide) _ e.nearest.1,
    e.nearest,e.ring_tie,
    nearest_le_radius h.cover (mem_unitDisk.mpr
      (h.cells.inside 9 (by decide) _ e.nearest.1).le) e.nearest.1⟩

theorem Representative.hub_ring_vertices {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) :
    ∃ v w : HubRingVertex c r, v.point ≠ w.point ∧ v.ring ≠ w.ring := by
  obtain ⟨x,y,hx,hy,hxy⟩ := h.hub_edge
  obtain ⟨hz,hs⟩ := strict_midpoint h hx hy hxy
  let z := ((1:ℝ)/2) • (x+y)
  let u := centerDir (perp (c 10-c 9))
  have hhub : c 9 ≠ c 10 := fun he => (by decide : (9 : Fin 11) ≠ 10) (h.injective he)
  have hperp := perp_ne (sub_ne_zero.mpr hhub.symm)
  have hu : ‖u‖ = 1 := centerDir_norm hperp
  have hu0 : u ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hu]
    norm_num
  have horth : inner ℝ u (c 10-c 9) = 0 := by
    change inner ℝ (‖perp (c 10-c 9)‖⁻¹ • perp (c 10-c 9)) (c 10-c 9) = 0
    rw [real_inner_smul_left,perp_inner,mul_zero]
  obtain ⟨ep⟩ := exists_ring_exit h hz hs hu horth
  obtain ⟨em⟩ := exists_ring_exit h hz hs
    (by rw [norm_neg]; exact hu : ‖-u‖ = 1)
    (by rw [inner_neg_left,horth,neg_zero] : inner ℝ (-u) (c 10-c 9) = 0)
  let v := vertex_of_exit h ep
  let w := vertex_of_exit h em
  have hpoints : v.point ≠ w.point := by
    intro heq
    have hd : ray z u ep.time-ray z (-u) em.time = (ep.time+em.time) • u := by
      simp only [ray,smul_neg,add_smul]
      abel
    have hzero : (ep.time+em.time) • u = 0 := by
      rw [← hd]
      exact sub_eq_zero.mpr heq
    rcases smul_eq_zero.mp hzero with he | he
    · linarith [ep.positive,em.positive]
    · exact hu0 he
  refine ⟨v,w,hpoints,?_⟩
  intro hring
  have hvt := v.ring_tie
  have hwt := w.ring_tie
  rw [← hring] at hwt
  have hvh : dist v.point (c 9) = dist v.point (c 10) :=
    le_antisymm (v.nearest.1 10) (v.nearest.2 9)
  have hwh : dist w.point (c 9) = dist w.point (c 10) :=
    le_antisymm (w.nearest.1 10) (w.nearest.2 9)
  rcases two_points_three_sites hhub hpoints hvh hwh hvt hwt with he | he
  · have hi := h.injective he
    have hv := congrArg (fun j : Fin 11 => j.val) hi
    have hl := v.ring.isLt
    change v.ring.val = 9 at hv
    omega
  · have hi := h.injective he
    have hv := congrArg (fun j : Fin 11 => j.val) hi
    have hl := v.ring.isLt
    change v.ring.val = 10 at hv
    omega

end N11Formalization.ActualHubEdgeEndpoints
#check @N11Formalization.ActualHubEdgeEndpoints.exists_ring_exit
#check @N11Formalization.ActualHubEdgeEndpoints.Representative.hub_ring_vertices
#print axioms N11Formalization.ActualHubEdgeEndpoints.exists_ring_exit
#print axioms N11Formalization.ActualHubEdgeEndpoints.Representative.hub_ring_vertices
