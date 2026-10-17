import N11Formalization.ActualClippedMeshVertices
import N11Formalization.ActualIncidentFacetAdjacency

/-! Exact relative-interior labels of positive ACTUAL clipped facets.
The open segment has exactly two nearest sites and lies strictly insideD;
distinct unordered facets have disjoint open interiors. Endpoint incident
polygon adjacency is PRODUCED from this, not assumed as combinatorial data. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualClippedFacetInterior
open ActualVoronoiCells ActualVoronoiIncidence ActualClippedFacetIntervals
open ActualClippedMeshVertices ActualHubEdgeGeometry ActualHubEdgeEndpointGeometry
open ActualBoundaryFacets ActualIncidentFacetGerms ActualIncidentPolygonOrder
open ActualIncidentFacetAdjacency ActualCoverStructuralReduction ActualVoronoiRadialExit

theorem combo_gap (x y a b : Point) (s t : ℝ) (hst : s+t = 1) :
    dist (s • x+t • y) b^2-dist (s • x+t • y) a^2 =
      s*(dist x b^2-dist x a^2)+t*(dist y b^2-dist y a^2) := by
  have hC := square_difference (s • x+t • y) b a
  have hX := square_difference x b a
  have hY := square_difference y b a
  simp only [inner_add_left,real_inner_smul_left] at hC
  have hs : s = 1-t := by linarith
  rw [hC,hX,hY,hs]
  ring

theorem common_strict_combo {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j) {x y : Point}
    (hx : x ∈ Cell c i ∩ Cell c j) (hy : y ∈ Cell c i ∩ Cell c j) (hxy : x ≠ y)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s+t = 1) :
    s • x+t • y ∈ PairStrict c i j := by
  have hz : s • x+t • y ∈ Cell c i ∩ Cell c j :=
    ((cell_convex c i).inter (cell_convex c j)) hx hy hs.le ht.le hst
  intro k hki hkj
  by_contra hnot
  have hztie : dist (s • x+t • y) (c k) = dist (s • x+t • y) (c i) :=
    le_antisymm (le_of_not_gt hnot) (hz.1 k)
  have hX : 0 ≤ dist x (c k)^2-dist x (c i)^2 := by
    nlinarith [hx.1 k,dist_nonneg (x := x) (y := c k),dist_nonneg (x := x) (y := c i)]
  have hY : 0 ≤ dist y (c k)^2-dist y (c i)^2 := by
    nlinarith [hy.1 k,dist_nonneg (x := y) (y := c k),dist_nonneg (x := y) (y := c i)]
  have hgap := combo_gap x y (c i) (c k) s t hst
  rw [hztie,sub_self] at hgap
  have hXzero : dist x (c k)^2-dist x (c i)^2 = 0 := by
    have hmul : s*(dist x (c k)^2-dist x (c i)^2) = 0 := by
      nlinarith [mul_nonneg ht.le hY,mul_nonneg hs.le hX]
    exact (mul_eq_zero.mp hmul).resolve_left hs.ne'
  have hYzero : dist y (c k)^2-dist y (c i)^2 = 0 := by
    have hmul : t*(dist y (c k)^2-dist y (c i)^2) = 0 := by
      nlinarith [mul_nonneg ht.le hY,mul_nonneg hs.le hX]
    exact (mul_eq_zero.mp hmul).resolve_left ht.ne'
  have hxeq : dist x (c k) = dist x (c i) := by
    nlinarith [hXzero,dist_nonneg (x := x) (y := c k),
      dist_nonneg (x := x) (y := c i)]
  have hyeq : dist y (c k) = dist y (c i) := by
    nlinarith [hYzero,dist_nonneg (x := y) (y := c k),
      dist_nonneg (x := y) (y := c i)]
  rcases two_points_three_sites (fun he => hij (hc he)) hxy
    (le_antisymm (hx.1 j) (hx.2 i)) (le_antisymm (hy.1 j) (hy.2 i))
    hxeq hyeq with he | he
  · exact hki (hc he)
  · exact hkj (hc he)

theorem common_combo_inside {c : Fin 11 → Point} {i j : Fin 11} {x y : Point}
    (hx : x ∈ ClippedCommon c i j) (hy : y ∈ ClippedCommon c i j) (hxy : x ≠ y)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s+t = 1) :
    ‖s • x+t • y‖ < 1 :=
  norm_combo_lt_of_ne (mem_unitDisk.mp hx.1) (mem_unitDisk.mp hy.1) hxy hs ht hst

theorem FacetInterval.endpoints_ne {c : Fin 11 → Point} {i j : Fin 11}
    (f : FacetInterval c i j) (hpos : f.lo < f.hi) :
    ray f.base f.direction f.lo ≠ ray f.base f.direction f.hi := by
  intro he
  have hz : (f.lo-f.hi) • f.direction = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (add_left_cancel he)
  have hd : f.direction ≠ 0 := norm_ne_zero_iff.mp (by rw [f.unit]; norm_num)
  exact smul_ne_zero (sub_ne_zero.mpr hpos.ne) hd hz

theorem FacetInterval.open_point {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j) (f : FacetInterval c i j) {t : ℝ}
    (hlt : f.lo < t) (hth : t < f.hi) :
    ‖ray f.base f.direction t‖ < 1 ∧
      ray f.base f.direction t ∈ PairStrict c i j ∧
      ray f.base f.direction t ∈ ClippedCommon c i j := by
  let b := (t-f.lo)/(f.hi-f.lo)
  have hden : 0 < f.hi-f.lo := sub_pos.mpr (hlt.trans hth)
  have hb : 0 < b := div_pos (sub_pos.mpr hlt) hden
  have hb1 : b < 1 := (div_lt_one hden).mpr (by linarith)
  have he : ray f.base f.direction t =
      (1-b) • ray f.base f.direction f.lo+b • ray f.base f.direction f.hi := by
    have hbt : b*(f.hi-f.lo) = t-f.lo := by dsimp [b]; field_simp
    have hscalar : (1-b)*f.lo+b*f.hi = t := by nlinarith
    unfold ray
    match_scalars <;> dsimp [b] at hscalar ⊢ <;> linarith [hscalar]
  have hne := FacetInterval.endpoints_ne f (hlt.trans hth)
  have hinside := common_combo_inside f.left_mem f.right_mem hne
    (by linarith : 0 < 1-b) hb (by ring : (1-b)+b = 1)
  have hstrict := common_strict_combo hc hij f.left_mem.2 f.right_mem.2 hne
    (by linarith : 0 < 1-b) hb (by ring : (1-b)+b = 1)
  have hmem : ray f.base f.direction t ∈ ClippedCommon c i j := by
    rw [f.points]
    exact ⟨t,⟨hlt.le,hth.le⟩,rfl⟩
  rw [← he] at hinside hstrict
  exact ⟨hinside,hstrict,hmem⟩

theorem FacetInterval.open_incident {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j) (f : FacetInterval c i j) {t : ℝ}
    (hlt : f.lo < t) (hth : t < f.hi) :
    incident c (ray f.base f.direction t) = {i,j} := by
  classical
  have hx := FacetInterval.open_point hc hij f hlt hth
  ext k
  constructor
  · intro hk
    by_cases hki : k = i
    · exact Finset.mem_insert.mpr (Or.inl hki)
    by_cases hkj : k = j
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hkj))
    exact (not_lt_of_ge ((mem_incident.mp hk) i) (hx.2.1 k hki hkj)).elim
  · intro hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact mem_incident.mpr hx.2.2.2.1
    · have he := Finset.mem_singleton.mp hk
      subst k
      exact mem_incident.mpr hx.2.2.2.2

theorem facet_open_intersection_labels {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j k l : Fin 11} (hij : i ≠ j) (hkl : k ≠ l)
    (f : FacetInterval c i j) (g : FacetInterval c k l) {s t : ℝ}
    (hfs : f.lo < s) (hsf : s < f.hi) (hgt : g.lo < t) (htg : t < g.hi)
    (he : ray f.base f.direction s = ray g.base g.direction t) :
    ({i,j} : Finset (Fin 11)) = {k,l} := by
  rw [← FacetInterval.open_incident hc hij f hfs hsf,
    ← FacetInterval.open_incident hc hkl g hgt htg,he]

theorem FacetInterval.endpoint_polygon_adjacent {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} {i j : Fin 11} (hij : i ≠ j)
    (f : FacetInterval c i j) (hpos : f.lo < f.hi)
    (F : InteriorFace c r) (o : OrderedCircle c r F)
    (hendpoint : F.point = ray f.base f.direction f.lo ∨
      F.point = ray f.base f.direction f.hi)
    {a b : Fin (incident c F.point).card}
    (ha : (o.order a).val = i) (hb : (o.order b).val = j) :
    b = finRotate (incident c F.point).card a ∨
      a = finRotate (incident c F.point).card b := by
  let t := (f.lo+f.hi)/2
  have htlo : f.lo < t := by dsimp [t]; linarith
  have hthi : t < f.hi := by dsimp [t]; linarith
  have hx := FacetInterval.open_point hc hij f htlo hthi
  have hI : i ∈ incident c F.point := by rw [← ha]; exact (o.order a).property
  have hJ : j ∈ incident c F.point := by rw [← hb]; exact (o.order b).property
  have hcone := pairCone_of_strict_pair hI hJ hx.2.2.2 hx.2.1
  have hab : a ≠ b := by
    intro he
    apply hij
    rw [← ha,← hb,he]
  apply OrderedCircle.pairCone_adjacent o hc hab
  simpa only [ha,hb] using hcone

end N11Formalization.ActualClippedFacetInterior
#check @N11Formalization.ActualClippedFacetInterior.FacetInterval.open_incident
#check @N11Formalization.ActualClippedFacetInterior.facet_open_intersection_labels
#check @N11Formalization.ActualClippedFacetInterior.FacetInterval.endpoint_polygon_adjacent
#print axioms N11Formalization.ActualClippedFacetInterior.FacetInterval.open_incident
#print axioms N11Formalization.ActualClippedFacetInterior.facet_open_intersection_labels
#print axioms N11Formalization.ActualClippedFacetInterior.FacetInterval.endpoint_polygon_adjacent
