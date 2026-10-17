import N11Formalization.ActualBoundaryTransversality

/-! Every ACTUAL boundary nearest pair starts a positive clipped facet into D.
Transversality and strict third-site separation are derived, not assumed.
No straight-site planar embedding or Delaunay-refinement premise is used. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryFacets
open ActualCoverStructuralReduction ActualBoundaryNeighborTies ActualBoundaryTransversality
open ActualBoundaryNearestPairs ActualRingDirectionOrder ActualBoundaryCyclicOrder
open ActualHubEdgeGeometry ActualVoronoiCells ActualVoronoiRadialExit

def PairStrict (c : Fin 11 → Point) (i j : Fin 11) : Set Point :=
  {x | ∀ k : Fin 11, k ≠ i → k ≠ j → dist x (c i) < dist x (c k)}

theorem pairStrict_open (c : Fin 11 → Point) (i j : Fin 11) : IsOpen (PairStrict c i j) := by
  classical
  have he : PairStrict c i j = ⋂ k : {k : Fin 11 // k ≠ i ∧ k ≠ j},
      {x : Point | dist x (c i) < dist x (c k.val)} := by
    ext x
    simp only [PairStrict,Set.mem_setOf_eq,Set.mem_iInter]
    constructor
    · intro h k
      exact h k.val k.2.1 k.2.2
    · intro h k hki hkj
      exact h ⟨k,hki,hkj⟩
  rw [he]
  exact isOpen_iInter_of_finite fun _ => isOpen_lt (by fun_prop) (by fun_prop)

theorem pair_nearest_of_strict {c : Fin 11 → Point} {i j : Fin 11} {x : Point}
    (heq : dist x (c i) = dist x (c j)) (hs : x ∈ PairStrict c i j) :
    x ∈ Cell c i ∩ Cell c j := by
  have hi : x ∈ Cell c i := by
    intro k
    by_cases hki : k = i
    · rw [hki]
    by_cases hkj : k = j
    · rw [hkj,heq]
    exact (hs k hki hkj).le
  exact ⟨hi,fun k => by rw [← heq]; exact hi k⟩

theorem inner_perp_circle (d : Point) (t : ℝ) :
    inner ℝ (circleMap t) (perp d) = Real.sin t*d 0-Real.cos t*d 1 := by
  rw [PinTangentGeometry.inner_coords]
  simp only [circleMap,perp,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

structure InwardPair (c : Fin 11 → Point) (x : Point) (i j : Fin 11) where
  direction : Point
  unit : ‖direction‖ = 1
  orthogonal : inner ℝ direction (c j-c i) = 0
  inward : inner ℝ x direction < 0

theorem inwardPair_of_neighbor {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (i : Fin 9) (v : NeighborTie c r i) :
    Nonempty (InwardPair c (circleMap v.angle) (ringSite i) (ringSite (nextRing i))) := by
  let d := c (ringSite (nextRing i))-c (ringSite i)
  have hsites : ringSite i ≠ ringSite (nextRing i) := by
    intro he
    exact next_ne i (Fin.ext (congrArg (fun q : Fin 11 => q.val) he))
  have hd : d ≠ 0 := sub_ne_zero.mpr (fun he => hsites.symm (h.injective he))
  have hp := perp_ne hd
  let w := centerDir (perp d)
  have hw : ‖w‖ = 1 := centerDir_norm hp
  have horth : inner ℝ w d = 0 := by
    change inner ℝ (‖perp d‖⁻¹ • perp d) d = 0
    rw [real_inner_smul_left,perp_inner,mul_zero]
  have hproj : inner ℝ (circleMap v.angle) w ≠ 0 := by
    have ht := Representative.neighbor_transverse h i v
    have hn := norm_ne_zero_iff.mpr hp
    intro he
    change inner ℝ (circleMap v.angle) (‖perp d‖⁻¹ • perp d) = 0 at he
    rw [real_inner_smul_right] at he
    have hh := (mul_eq_zero.mp he).resolve_left (inv_ne_zero hn)
    rw [inner_perp_circle] at hh
    apply ht
    dsimp [gapDerivative,d] at hh ⊢
    linarith
  by_cases hwneg : inner ℝ (circleMap v.angle) w < 0
  · exact ⟨⟨w,hw,horth,hwneg⟩⟩
  · refine ⟨⟨-w,by rw [norm_neg]; exact hw,?_,?_⟩⟩
    · rw [inner_neg_left,horth,neg_zero]
    · rw [inner_neg_right]
      have hh : 0 < inner ℝ (circleMap v.angle) w := lt_of_le_of_ne (le_of_not_gt hwneg) hproj.symm
      linarith

structure FacetStart (c : Fin 11 → Point) (x : Point) (i j : Fin 11) where
  direction : Point
  unit : ‖direction‖ = 1
  orthogonal : inner ℝ direction (c j-c i) = 0
  time : ℝ
  positive : 0 < time
  inside : ‖ray x direction time‖ < 1
  nearest : ray x direction time ∈ Cell c i ∩ Cell c j
  strict_others : ray x direction time ∈ PairStrict c i j

theorem facet_start_of_inward {c : Fin 11 → Point} {x : Point} {i j : Fin 11}
    (hx : ‖x‖ = 1) (heq : dist x (c i) = dist x (c j))
    (hs : x ∈ PairStrict c i j) (u : InwardPair c x i j) :
    Nonempty (FacetStart c x i j) := by
  obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp (pairStrict_open c i j) x hs
  let t := min eps (-inner ℝ x u.direction)/2
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (lt_min heps (neg_pos.mpr u.inward)) (by norm_num)
  have hte : t < eps := by
    have hh := min_le_left eps (-inner ℝ x u.direction)
    dsimp [t]
    linarith [lt_min heps (neg_pos.mpr u.inward)]
  have hti : t < -inner ℝ x u.direction := by
    have hh := min_le_right eps (-inner ℝ x u.direction)
    dsimp [t]
    linarith [lt_min heps (neg_pos.mpr u.inward)]
  have hs' : ray x u.direction t ∈ PairStrict c i j := by
    apply hball
    apply Metric.mem_ball.mpr
    rw [ray_dist _ _ _ u.unit,abs_of_pos ht]
    exact hte
  have heq' : dist (ray x u.direction t) (c i) = dist (ray x u.direction t) (c j) :=
    shifted_equidistant heq u.orthogonal
  have hsq : ‖ray x u.direction t‖^2 =
      1+t^2+2*t*inner ℝ x u.direction := by
    rw [ray,norm_add_sq_real,norm_smul,Real.norm_eq_abs,abs_of_pos ht,
      real_inner_smul_right,hx,u.unit]
    ring
  have hinside : ‖ray x u.direction t‖ < 1 := by
    have hprod : t*(t+2*inner ℝ x u.direction) < 0 :=
      mul_neg_of_pos_of_neg ht (by linarith)
    nlinarith [norm_nonneg (ray x u.direction t)]
  exact ⟨⟨u.direction,u.unit,u.orthogonal,t,ht,hinside,
    pair_nearest_of_strict heq' hs',hs'⟩⟩

theorem Representative.boundary_facet_start {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) (v : NeighborTie c r i) :
    Nonempty (FacetStart c (circleMap v.angle) (ringSite i) (ringSite (nextRing i))) := by
  obtain ⟨u⟩ := inwardPair_of_neighbor h i v
  have hsites : ringSite i ≠ ringSite (nextRing i) := by
    intro he
    exact next_ne i (Fin.ext (congrArg (fun q : Fin 11 => q.val) he))
  exact facet_start_of_inward (circleMap_norm v.angle) v.equidistant
    (other_strictly_farther h.cover hr h.labels (circleMap_norm v.angle) hsites
      v.nearest.1 v.nearest.2) u

end N11Formalization.ActualBoundaryFacets
#check @N11Formalization.ActualBoundaryFacets.Representative.boundary_facet_start
#print axioms N11Formalization.ActualBoundaryFacets.Representative.boundary_facet_start
