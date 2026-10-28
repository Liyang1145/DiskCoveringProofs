import N11Formalization.ActualDelaunayPolygonSeparation

/-! Coherent local fan triangle interiors are disjoint, including4/5-site
degenerate nearest polygons. A fan diagonal through the apex separates each
earlier triangle from each later triangle. Combined with distinct primal
polygon plane separation, the selected triangles do not overlap internally. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualIncidentFanInteriors
open ActualVoronoiIncidence ActualIncidentPolygonOrder ActualIncidentPolygonConvexity
open ActualIncidentFacetAdjacency ActualIncidentFanRefinement ActualDelaunayPolygonSeparation
open ActualHubEdgeGeometry FlashTiling

theorem orient_gap (a b x : Point) :
    orient a b x = gap (perp (b-a)) (-inner ℝ (perp (b-a)) a) x := by
  rw [← perp_inner_orient]
  rw [inner_sub_right,gap]
  ring

theorem orient_nonpos_convex (a b : Point) :
    Convex ℝ {x : Point | orient a b x ≤ 0} := by
  have he : {x : Point | orient a b x ≤ 0} =
      {x : Point | gap (perp (b-a)) (-inner ℝ (perp (b-a)) a) x ≤ 0} := by
    ext x
    change orient a b x ≤ 0 ↔ gap (perp (b-a)) (-inner ℝ (perp (b-a)) a) x ≤ 0
    rw [orient_gap]
  rw [he]
  exact gap_nonpos_convex _ _

theorem interior_orient_negative {a b : Point} (hab : a ≠ b) {x : Point}
    (hx : x ∈ interior {p : Point | orient a b p ≤ 0}) : orient a b x < 0 := by
  let n := perp (b-a)
  have hn : -n ≠ 0 := neg_ne_zero.mpr (perp_ne (sub_ne_zero.mpr hab.symm))
  have he : {p : Point | orient a b p ≤ 0} =
      {p : Point | 0 ≤ gap (-n) (inner ℝ n a) p} := by
    ext p
    change orient a b p ≤ 0 ↔ 0 ≤ gap (-n) (inner ℝ n a) p
    rw [orient_gap]
    dsimp [gap,n]
    rw [inner_neg_left]
    constructor <;> intro h <;> linarith
  rw [he] at hx
  have hh := interior_gap_positive hn hx
  rw [orient_gap]
  dsimp [gap,n] at hh ⊢
  rw [inner_neg_left] at hh
  linarith

theorem fan_next_le {n : ℕ} {k l : Fin n} (hk : FanIndex k) (hkl : k < l) :
    finRotate n k ≤ l := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ m =>
    have hlast : k ≠ Fin.last m := by
      intro he
      have hh := congrArg Fin.val he
      have hb := hk.2
      change k.val = m at hh
      omega
    have hval := coe_finRotate_of_ne_last hlast
    change (finRotate (m+1) k).val ≤ l.val
    have hklt : k.val < l.val := hkl
    omega

theorem OrderedCircle.ordered_triangles_separated {c : Fin 11 → Point} {r : ℝ}
    {F : InteriorFace c r} (o : OrderedCircle c r F)
    {k l : Fin (incident c F.point).card} (hk : FanIndex k) (hl : FanIndex l)
    (hkl : k < l) :
    let a := c (o.order (apex o)).val
    let b := c (o.order (finRotate (incident c F.point).card k)).val
    TriangleHull o k ⊆ {p : Point | orient a b p ≤ 0} ∧
      TriangleHull o l ⊆ {p : Point | 0 ≤ orient a b p} := by
  dsimp only
  have hkbound := fan_index_bounds F.at_least_three hk
  have hlbound := fan_index_bounds F.at_least_three hl
  have h0next : apex o < finRotate (incident c F.point).card k :=
    hkbound.1.trans hkbound.2
  have hnextle := fan_next_le hk hkl
  constructor
  · apply convexHull_min ?_ (orient_nonpos_convex _ _)
    intro p hp
    change orient (c (o.order (apex o)).val)
      (c (o.order (finRotate (incident c F.point).card k)).val) p ≤ 0
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    ·
      simp [orient,det2]
    · rw [orient_swap]
      exact (neg_neg_of_pos (OrderedCircle.selected_positive_area o hk)).le
    · simp [orient,det2_self]
  · apply convexHull_min ?_ (convex_orient_nonneg _ _)
    intro p hp
    change 0 ≤ orient (c (o.order (apex o)).val)
      (c (o.order (finRotate (incident c F.point).card k)).val) p
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    ·
      simp [orient,det2]
    ·
      rcases lt_or_eq_of_le hnextle with hlt | heq
      · exact (OrderedCircle.increasing_triple_orientation o h0next hlt).le
      · rw [← heq]
        simp [orient,det2_self]
    ·
      exact (OrderedCircle.increasing_triple_orientation o h0next
        (hnextle.trans_lt hlbound.2)).le

theorem OrderedCircle.ordered_triangle_interiors_disjoint {c : Fin 11 → Point} {r : ℝ}
    {F : InteriorFace c r} (o : OrderedCircle c r F)
    {k l : Fin (incident c F.point).card} (hk : FanIndex k) (hl : FanIndex l)
    (hkl : k < l) :
    Disjoint (interior (TriangleHull o k)) (TriangleHull o l) := by
  have hsep := OrderedCircle.ordered_triangles_separated o hk hl hkl
  have hchord : c (o.order (apex o)).val ≠
      c (o.order (finRotate (incident c F.point).card k)).val := by
    intro he
    have hp := OrderedCircle.selected_positive_area o hk
    change 0 < orient (c (o.order (apex o)).val) (c (o.order k).val)
      (c (o.order (finRotate (incident c F.point).card k)).val) at hp
    rw [← he] at hp
    simp [orient,det2] at hp
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hstrict := interior_orient_negative hchord (interior_mono hsep.1 hx)
  exact not_lt_of_ge (hsep.2 hy) hstrict

theorem OrderedCircle.selected_interiors_disjoint {c : Fin 11 → Point} {r : ℝ}
    {F : InteriorFace c r} (o : OrderedCircle c r F)
    {k l : Fin (incident c F.point).card} (hk : FanIndex k) (hl : FanIndex l)
    (hkl : k ≠ l) :
    Disjoint (interior (TriangleHull o k)) (interior (TriangleHull o l)) := by
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · exact (OrderedCircle.ordered_triangle_interiors_disjoint o hk hl hlt).mono_right interior_subset
  · exact ((OrderedCircle.ordered_triangle_interiors_disjoint o hl hk hgt).mono_right interior_subset).symm

/-- Both cases of coherent refinement: same polygon and different true
primal vertices. No additional noncrossing assumption. -/
theorem selected_triangles_coherent {c : Fin 11 → Point} {r : ℝ}
    {F G : InteriorFace c r} (o : OrderedCircle c r F) (p : OrderedCircle c r G)
    {k : Fin (incident c F.point).card} {l : Fin (incident c G.point).card}
    (hFG : F.point ≠ G.point) :
    Disjoint (interior (TriangleHull o k)) (interior (TriangleHull p l)) :=
  (distinct_primal_triangles_disjoint o p hFG k l).mono_right interior_subset

end N11Formalization.ActualIncidentFanInteriors
#check @N11Formalization.ActualIncidentFanInteriors.OrderedCircle.selected_interiors_disjoint
#check @N11Formalization.ActualIncidentFanInteriors.selected_triangles_coherent
#print axioms N11Formalization.ActualIncidentFanInteriors.OrderedCircle.selected_interiors_disjoint
#print axioms N11Formalization.ActualIncidentFanInteriors.selected_triangles_coherent
