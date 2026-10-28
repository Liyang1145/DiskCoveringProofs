import N11Formalization.ActualIncidentFacetAdjacency

/-! Constructive local ACTUAL3/4/5-gon fan refinement. There are exactly
n-2 nondegenerate selected triangles; they cover the incident polygon hull,
retain every positive primal side, and each keeps the same original nearest
vertex and all three originalr distance bounds. Global disk assembly remains
separate; no canonical eleven-face table is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualIncidentFanRefinement
open ActualVoronoiCells ActualVoronoiIncidence ActualIncidentPolygonOrder
open ActualIncidentPolygonConvexity ActualIncidentPolygonFacets ActualIncidentFacetGerms
open ActualIncidentFacetAdjacency ActualIncidentChordGeometry FlashTiling

def FanIndex {n : ℕ} (k : Fin n) : Prop := 0 < k.val ∧ k.val+1 < n
instance {n : ℕ} (k : Fin n) : Decidable (FanIndex k) := by unfold FanIndex; infer_instance

def fanIndices (n : ℕ) : Finset (Fin n) := Finset.univ.filter FanIndex

def indexTriangle {n : ℕ} (hn : 0 < n) (k : Fin n) : Finset (Fin n) :=
  {⟨0,hn⟩,k,finRotate n k}

theorem fan_indices_card {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    (fanIndices n).card = n-2 := by interval_cases n <;> decide

theorem side_in_selected_triangle {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    ∀ i : Fin n, ∃ k : Fin n, FanIndex k ∧
      indexTriangle (by omega : 0 < n) i ⊆ indexTriangle (by omega : 0 < n) k := by
  interval_cases n <;> decide +revert

theorem fan_index_bounds {n : ℕ} (hn3 : 3 ≤ n) {k : Fin n} (hk : FanIndex k) :
    (⟨0,by omega⟩ : Fin n) < k ∧ k < finRotate n k := by
  cases n with
  | zero => omega
  | succ m =>
    have hlast : k ≠ Fin.last m := by
      intro he
      have hh := congrArg Fin.val he
      have hb := hk.2
      change k.val = m at hh
      omega
    exact ⟨hk.1,(lt_finRotate_iff_ne_last k).mpr hlast⟩

def apex {c : Fin 11 → Point} {r : ℝ} {f : InteriorFace c r}
    (o : OrderedCircle c r f) : Fin (incident c f.point).card :=
  ⟨0,by have h := f.at_least_three; omega⟩

def triangleLabels {c : Fin 11 → Point} {r : ℝ} {f : InteriorFace c r}
    (o : OrderedCircle c r f) (k : Fin (incident c f.point).card) : Fin 3 → Fin 11 :=
  ![(o.order (apex o)).val,(o.order k).val,
    (o.order (finRotate (incident c f.point).card k)).val]

def TriangleHull {c : Fin 11 → Point} {r : ℝ} {f : InteriorFace c r}
    (o : OrderedCircle c r f) (k : Fin (incident c f.point).card) : Set Point :=
  convexHull ℝ ({c (o.order (apex o)).val,c (o.order k).val,
    c (o.order (finRotate (incident c f.point).card k)).val} : Set Point)

theorem OrderedCircle.selected_nearest {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f)
    (k : Fin (incident c f.point).card) (v : Fin 3) :
    f.point ∈ Cell c (triangleLabels o k v) ∧
      dist f.point (c (triangleLabels o k v)) ≤ r := by
  have hi : triangleLabels o k v ∈ incident c f.point := by
    fin_cases v <;> simp only [triangleLabels,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two] <;> exact (o.order _).property
  exact ⟨mem_incident.mp hi,f.radius _ hi⟩

theorem OrderedCircle.selected_positive_area {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f)
    {k : Fin (incident c f.point).card} (hk : FanIndex k) :
    0 < orient (c (triangleLabels o k 0)) (c (triangleLabels o k 1))
      (c (triangleLabels o k 2)) := by
  obtain ⟨h0,hnext⟩ := fan_index_bounds f.at_least_three hk
  exact OrderedCircle.increasing_triple_orientation o h0 hnext

theorem OrderedCircle.hull_selected_cover {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) {p : Point}
    (hp : p ∈ convexHull ℝ (Set.range (fun i => c (o.order i).val))) :
    ∃ k : Fin (incident c f.point).card, FanIndex k ∧ p ∈ TriangleHull o k := by
  obtain ⟨i,hi⟩ := OrderedCircle.hull_fan o (c (o.order (apex o)).val) hp
  obtain ⟨k,hk,hsub⟩ := side_in_selected_triangle f.at_least_three f.at_most_five i
  refine ⟨k,hk,?_⟩
  apply convexHull_mono ?_ hi
  intro x hx
  have hlabel : ∃ j ∈ indexTriangle (by have h := f.at_least_three; omega) i,
      c (o.order j).val = x := by
    rcases hx with he | he | he
    · exact ⟨apex o,by simp [indexTriangle,apex],he.symm⟩
    · exact ⟨i,by simp [indexTriangle],he.symm⟩
    · exact ⟨finRotate (incident c f.point).card i,by simp [indexTriangle],he.symm⟩
  obtain ⟨j,hj,rfl⟩ := hlabel
  have hJ := hsub hj
  rcases Finset.mem_insert.mp hJ with he | hJ
  · have haj : j = apex o := he
    rw [haj]
    simp
  rcases Finset.mem_insert.mp hJ with he | hJ
  · rw [he]
    simp
  have he := Finset.mem_singleton.mp hJ
  rw [he]
  simp

theorem OrderedCircle.side_retained {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f)
    (i : Fin (incident c f.point).card) :
    ∃ k : Fin (incident c f.point).card, FanIndex k ∧
      (o.order i).val ∈ Set.range (triangleLabels o k) ∧
      (o.order (finRotate (incident c f.point).card i)).val ∈ Set.range (triangleLabels o k) := by
  obtain ⟨k,hk,hsub⟩ := side_in_selected_triangle f.at_least_three f.at_most_five i
  have hlabel (j : Fin (incident c f.point).card)
      (hj : j ∈ indexTriangle (by have h := f.at_least_three; omega) k) :
      (o.order j).val ∈ Set.range (triangleLabels o k) := by
    rcases Finset.mem_insert.mp hj with he | hj
    · exact ⟨0,congrArg (fun x => (o.order x).val) he.symm⟩
    rcases Finset.mem_insert.mp hj with he | hj
    · exact ⟨1,congrArg (fun x => (o.order x).val) he.symm⟩
    have he := Finset.mem_singleton.mp hj
    exact ⟨2,congrArg (fun x => (o.order x).val) he.symm⟩
  exact ⟨k,hk,hlabel i (hsub (by simp [indexTriangle])),
    hlabel _ (hsub (by simp [indexTriangle]))⟩

theorem OrderedCircle.positive_facet_retained {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) (hc : Function.Injective c)
    {i j : Fin (incident c f.point).card} (hij : i ≠ j)
    (g : FacetGerm c r f.point (o.order i).val (o.order j).val) :
    ∃ k : Fin (incident c f.point).card, FanIndex k ∧
      (o.order i).val ∈ Set.range (triangleLabels o k) ∧
      (o.order j).val ∈ Set.range (triangleLabels o k) := by
  rcases OrderedCircle.positive_facet_adjacent o hc hij g with hj | hi
  · obtain ⟨k,hk,h1,h2⟩ := OrderedCircle.side_retained o i
    exact ⟨k,hk,h1,by rwa [hj]⟩
  · obtain ⟨k,hk,h1,h2⟩ := OrderedCircle.side_retained o j
    exact ⟨k,hk,by rwa [hi],h1⟩

theorem OrderedCircle.fan_spokes_non_crossing {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) (hc : Function.Injective c)
    {i j : Fin (incident c f.point).card} (hi : i ≠ apex o) (hj : j ≠ apex o)
    {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (he : s • c (o.order (apex o)).val+(1-s) • c (o.order i).val =
      t • c (o.order (apex o)).val+(1-t) • c (o.order j).val) : i = j := by
  have hh := fan_spokes_no_internal_crossing hc
    (fun he => hi (OrderedCircle.label_injective o he).symm)
    (fun he => hj (OrderedCircle.label_injective o he))
    (o.order (apex o)).property (o.order i).property (o.order j).property
    hs0 hs1 ht0 ht1 he
  exact (OrderedCircle.label_injective o hh).symm

end N11Formalization.ActualIncidentFanRefinement
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.hull_selected_cover
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.selected_nearest
#print axioms N11Formalization.ActualIncidentFanRefinement.OrderedCircle.hull_selected_cover
#print axioms N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#print axioms N11Formalization.ActualIncidentFanRefinement.OrderedCircle.fan_spokes_non_crossing
