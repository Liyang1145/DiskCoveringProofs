import N11Formalization.ActualVoronoiLocalFan
import N11Formalization.ActualBoundaryFacets

/-! Exact correspondence between strict supporting incident chords and
positive ACTUAL primal facet germs. A whole positive segment stays insideD,
has exactly the two stated nearest labels, and keeps the originalr bound.
No arbitrary diagonal is mislabeled a positive primal facet. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualIncidentFacetGerms
open ActualVoronoiCells ActualVoronoiIncidence ActualVoronoiLocalFan
open ActualVoronoiRadialExit ActualHubEdgeGeometry ActualBoundaryFacets

def PairCone (c : Fin 11 → Point) (v : Point) (i j : Fin 11) : Set Point :=
  {d | inner ℝ d (c j-c i) = 0 ∧
    ∀ k ∈ incident c v, k ≠ i → k ≠ j → inner ℝ d (c k-c i) < 0}

structure FacetGerm (c : Fin 11 → Point) (r : ℝ) (v : Point) (i j : Fin 11) where
  direction : Point
  nonzero : direction ≠ 0
  time : ℝ
  positive : 0 < time
  inside : ∀ t : ℝ, 0 < t → t ≤ time → ‖ray v direction t‖ < 1
  nearest : ∀ t : ℝ, 0 < t → t ≤ time →
    ray v direction t ∈ Cell c i ∩ Cell c j
  strict_others : ∀ t : ℝ, 0 < t → t ≤ time → ray v direction t ∈ PairStrict c i j
  radius : ∀ t : ℝ, 0 < t → t ≤ time → dist (ray v direction t) (c i) ≤ r

theorem facetGerm_of_pairCone {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) {v d : Point} (hv : ‖v‖ < 1) {i j : Fin 11}
    (hi : i ∈ incident c v) (hj : j ∈ incident c v)
    (hd : d ∈ PairCone c v i j) (hdne : d ≠ 0) :
    Nonempty (FacetGerm c r v i j) := by
  have hopen : IsOpen ({x : Point | ‖x‖ < 1} ∩ OutsideGap c v) :=
    (isOpen_lt continuous_norm continuous_const).inter (outsideGap_open c v)
  obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp hopen v
    ⟨hv,vertex_mem_outsideGap c v⟩
  let tau := eps/(2*(‖d‖+1))
  have hden : 0 < 2*(‖d‖+1) := by positivity
  have htau : 0 < tau := div_pos heps hden
  have hsmall : tau*‖d‖ < eps := by
    have he : tau*(2*(‖d‖+1)) = eps := by dsimp [tau]; field_simp
    nlinarith [norm_nonneg d]
  have hgap (t : ℝ) (ht : 0 < t) (htt : t ≤ tau) :
      ray v d t ∈ {x : Point | ‖x‖ < 1} ∩ OutsideGap c v := by
    apply hball
    apply Metric.mem_ball.mpr
    rw [ray,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_right htt (norm_nonneg d)).trans_lt hsmall
  have heq (t : ℝ) : dist (ray v d t) (c i) = dist (ray v d t) (c j) :=
    shifted_equidistant (le_antisymm ((mem_incident.mp hi) j)
      ((mem_incident.mp hj) i)) hd.1
  have hstrict (t : ℝ) (ht : 0 < t) (htt : t ≤ tau) :
      ray v d t ∈ PairStrict c i j := by
    intro k hki hkj
    by_cases hk : k ∈ incident c v
    · apply (tied_lt_iff (le_antisymm ((mem_incident.mp hi) k)
        ((mem_incident.mp hk) i))).mpr
      rw [ray,add_sub_cancel_left,real_inner_smul_left]
      exact mul_neg_of_pos_of_neg ht (hd.2 k hk hki hkj)
    · exact (hgap t ht htt).2 i hi k hk
  have hnearest (t : ℝ) (ht : 0 < t) (htt : t ≤ tau) :
      ray v d t ∈ Cell c i ∩ Cell c j :=
    pair_nearest_of_strict (heq t) (hstrict t ht htt)
  refine ⟨⟨d,hdne,tau,htau,fun t ht htt => (hgap t ht htt).1,
    hnearest,hstrict,?_⟩⟩
  intro t ht htt
  exact nearest_le_radius hc (mem_unitDisk.mpr (hgap t ht htt).1.le)
    (hnearest t ht htt).1

theorem pairCone_of_strict_pair {c : Fin 11 → Point} {v x : Point} {i j : Fin 11}
    (hi : i ∈ incident c v) (hj : j ∈ incident c v)
    (hx : x ∈ Cell c i ∩ Cell c j) (hs : x ∈ PairStrict c i j) :
    x-v ∈ PairCone c v i j := by
  refine ⟨?_,?_⟩
  · have he := tied_distance_difference (x := x)
      (le_antisymm ((mem_incident.mp hi) j) ((mem_incident.mp hj) i))
    have heq := le_antisymm (hx.1 j) (hx.2 i)
    rw [heq,sub_self] at he
    linarith
  · intro k hk hki hkj
    exact (tied_lt_iff (le_antisymm ((mem_incident.mp hi) k)
      ((mem_incident.mp hk) i))).mp (hs k hki hkj)

theorem facetGerm_direction_pairCone {c : Fin 11 → Point} {r : ℝ} {v : Point}
    {i j : Fin 11} (hi : i ∈ incident c v) (hj : j ∈ incident c v)
    (g : FacetGerm c r v i j) : g.direction ∈ PairCone c v i j := by
  have hcone := pairCone_of_strict_pair hi hj
    (g.nearest g.time g.positive le_rfl) (g.strict_others g.time g.positive le_rfl)
  rw [ray,add_sub_cancel_left] at hcone
  refine ⟨?_,?_⟩
  · have he := hcone.1
    rw [real_inner_smul_left] at he
    exact (mul_eq_zero.mp he).resolve_left g.positive.ne'
  · intro k hk hki hkj
    have he := hcone.2 k hk hki hkj
    rw [real_inner_smul_left] at he
    exact (mul_neg_iff.mp he).resolve_right (by
      intro h
      exact (not_lt_of_ge g.positive.le) h.1) |>.2

theorem facetGerm_iff_supporting_chord {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) {v : Point} (hv : ‖v‖ < 1) {i j : Fin 11}
    (hi : i ∈ incident c v) (hj : j ∈ incident c v) :
    Nonempty (FacetGerm c r v i j) ↔ ∃ d : Point, d ≠ 0 ∧ d ∈ PairCone c v i j := by
  constructor
  · rintro ⟨g⟩
    exact ⟨g.direction,g.nonzero,facetGerm_direction_pairCone hi hj g⟩
  · rintro ⟨d,hdne,hd⟩
    exact facetGerm_of_pairCone hc hv hi hj hd hdne

theorem FacetGerm.exact_incident_pair {c : Fin 11 → Point} {r : ℝ} {v : Point}
    {i j : Fin 11} (g : FacetGerm c r v i j)
    {t : ℝ} (ht : 0 < t) (htt : t ≤ g.time) :
    incident c (ray v g.direction t) = {i,j} := by
  classical
  ext k
  constructor
  · intro hk
    by_cases hki : k = i
    · exact Finset.mem_insert.mpr (Or.inl hki)
    by_cases hkj : k = j
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hkj))
    have hs := g.strict_others t ht htt k hki hkj
    exact (not_lt_of_ge ((mem_incident.mp hk) i)) hs |>.elim
  · intro hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact mem_incident.mpr (g.nearest t ht htt).1
    · have he := Finset.mem_singleton.mp hk
      subst k
      exact mem_incident.mpr (g.nearest t ht htt).2

theorem FacetGerm.positive_segment {c : Fin 11 → Point} {r : ℝ} {v : Point}
    {i j : Fin 11} (g : FacetGerm c r v i j) :
    ray v g.direction (g.time/2) ≠ ray v g.direction g.time := by
  intro he
  have hs : (g.time/2-g.time) • g.direction = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (add_left_cancel he)
  have ht : g.time/2-g.time ≠ 0 := by linarith [g.positive]
  exact (smul_ne_zero ht g.nonzero) hs

end N11Formalization.ActualIncidentFacetGerms
#check @N11Formalization.ActualIncidentFacetGerms.facetGerm_iff_supporting_chord
#check @N11Formalization.ActualIncidentFacetGerms.FacetGerm.exact_incident_pair
#print axioms N11Formalization.ActualIncidentFacetGerms.facetGerm_of_pairCone
#print axioms N11Formalization.ActualIncidentFacetGerms.facetGerm_iff_supporting_chord
#print axioms N11Formalization.ActualIncidentFacetGerms.FacetGerm.positive_segment
