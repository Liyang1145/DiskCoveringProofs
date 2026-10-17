import N11Formalization.ActualIncidentFanRefinement
import N11Formalization.ActualDelaunayCrossing

/-! Distinct ACTUAL nearest polygons have disjoint interiors. The affine
difference of their two genuine lifted supporting planes separates the whole
projected polygon hulls. Hence selected triangles from different primal
witnesses cannot overlap internally, even when one/both polygons are4/5-gons.
This supplies polygon/triangle coherence, not a global disk covering theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualDelaunayPolygonSeparation
open ActualVoronoiCells ActualVoronoiIncidence ActualDelaunaySupport
open ActualIncidentPolygonOrder ActualIncidentFanRefinement ActualHubEdgeGeometry
open ActualVoronoiRadialExit

def PolygonHull (c : Fin 11 → Point) (v : Point) : Set Point :=
  convexHull ℝ (c '' (incident c v : Set (Fin 11)))

def gap (n : Point) (b : ℝ) (p : Point) : ℝ := inner ℝ n p+b

theorem gap_nonneg_convex (n : Point) (b : ℝ) :
    Convex ℝ {p : Point | 0 ≤ gap n b p} := by
  intro x hx y hy a d ha hd had
  change 0 ≤ inner ℝ n (a • x+d • y)+b
  simp only [inner_add_right,real_inner_smul_right]
  change 0 ≤ inner ℝ n x+b at hx
  change 0 ≤ inner ℝ n y+b at hy
  have hA := mul_nonneg ha hx
  have hB := mul_nonneg hd hy
  have he : (a+d)*b = b := by rw [had,one_mul]
  nlinarith [he]

theorem gap_nonpos_convex (n : Point) (b : ℝ) :
    Convex ℝ {p : Point | gap n b p ≤ 0} := by
  intro x hx y hy a d ha hd had
  change inner ℝ n (a • x+d • y)+b ≤ 0
  simp only [inner_add_right,real_inner_smul_right]
  change inner ℝ n x+b ≤ 0 at hx
  change inner ℝ n y+b ≤ 0 at hy
  have hA := mul_nonpos_of_nonneg_of_nonpos ha hx
  have hB := mul_nonpos_of_nonneg_of_nonpos hd hy
  have he : (a+d)*b = b := by rw [had,one_mul]
  nlinarith [he]

theorem interior_gap_positive {n : Point} (hn : n ≠ 0) {b : ℝ} {x : Point}
    (hx : x ∈ interior {p : Point | 0 ≤ gap n b p}) : 0 < gap n b x := by
  have hle := interior_subset hx
  change 0 ≤ gap n b x at hle
  by_contra hnot
  have heq : gap n b x = 0 := le_antisymm (le_of_not_gt hnot) hle
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hnorm : 0 < ‖n‖ := norm_pos_iff.mpr hn
  let t := eps/(2*‖n‖)
  have ht : 0 < t := div_pos heps (by linarith)
  let y := x+t • (-n)
  have hdist : dist y x = eps/2 := by
    rw [dist_eq_norm]
    dsimp only [y]
    rw [add_sub_cancel_left]
    rw [norm_smul,norm_neg,Real.norm_eq_abs,abs_of_pos ht]
    dsimp [t]
    field_simp
    <;> ring
  have hy := hball (Metric.mem_ball.mpr (by rw [hdist]; linarith : dist y x < eps))
  change 0 ≤ gap n b y at hy
  have hchange : gap n b y = gap n b x-t*‖n‖^2 := by
    dsimp [gap,y]
    rw [inner_add_right,real_inner_smul_right,inner_neg_right,real_inner_self_eq_norm_sq]
    ring
  rw [hchange,heq] at hy
  nlinarith [mul_pos ht (sq_pos_of_pos hnorm)]

theorem polygon_planes_separate {c : Fin 11 → Point} {u v : Point} {i j : Fin 11}
    (hi : u ∈ Cell c i) (hj : v ∈ Cell c j) :
    let n := (2:ℝ) • (u-v)
    let b := support u (lift (c i))-support v (lift (c j))
    PolygonHull c u ⊆ {p : Point | 0 ≤ gap n b p} ∧
      PolygonHull c v ⊆ {p : Point | gap n b p ≤ 0} := by
  dsimp only
  constructor
  · apply convexHull_min ?_ (gap_nonneg_convex _ _)
    rintro p ⟨k,hk,rfl⟩
    have hnear := mem_incident.mp hk
    have heq : support u (lift (c k)) = support u (lift (c i)) :=
      (ActualDelaunayCrossing.support_eq_iff_dist_eq _ _ _).mpr
        (le_antisymm (hnear i) (hi k))
    have hle := nearest_support hj k
    dsimp [support,lift] at heq hle
    dsimp [gap,support,lift]
    rw [real_inner_smul_left,inner_sub_left]
    linarith
  · apply convexHull_min ?_ (gap_nonpos_convex _ _)
    rintro p ⟨k,hk,rfl⟩
    have hnear := mem_incident.mp hk
    have heq : support v (lift (c k)) = support v (lift (c j)) :=
      (ActualDelaunayCrossing.support_eq_iff_dist_eq _ _ _).mpr
        (le_antisymm (hnear j) (hj k))
    have hle := nearest_support hi k
    dsimp [support,lift] at heq hle
    dsimp [gap,support,lift]
    rw [real_inner_smul_left,inner_sub_left]
    linarith

theorem distinct_polygon_interior_disjoint {c : Fin 11 → Point} {u v : Point}
    (huv : u ≠ v) : Disjoint (interior (PolygonHull c u)) (PolygonHull c v) := by
  obtain ⟨i,hi⟩ := exists_nearest c u
  obtain ⟨j,hj⟩ := exists_nearest c v
  have hsep := polygon_planes_separate hi hj
  have hn : (2:ℝ) • (u-v) ≠ 0 := smul_ne_zero (by norm_num) (sub_ne_zero.mpr huv)
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hstrict := interior_gap_positive hn (interior_mono hsep.1 hp)
  exact not_lt_of_ge (hsep.2 hq) hstrict

theorem OrderedCircle.triangle_subset_polygon {c : Fin 11 → Point} {r : ℝ}
    {F : InteriorFace c r} (o : OrderedCircle c r F)
    (k : Fin (incident c F.point).card) : TriangleHull o k ⊆ PolygonHull c F.point := by
  apply convexHull_mono
  intro p hp
  rcases hp with he | he | he
  · exact ⟨(o.order (apex o)).val,(o.order (apex o)).property,he.symm⟩
  · exact ⟨(o.order k).val,(o.order k).property,he.symm⟩
  · exact ⟨(o.order (finRotate (incident c F.point).card k)).val,
      (o.order (finRotate (incident c F.point).card k)).property,he.symm⟩

theorem distinct_primal_triangles_disjoint {c : Fin 11 → Point} {r : ℝ}
    {F G : InteriorFace c r} (o : OrderedCircle c r F) (p : OrderedCircle c r G)
    (hFG : F.point ≠ G.point)
    (i : Fin (incident c F.point).card) (j : Fin (incident c G.point).card) :
    Disjoint (interior (TriangleHull o i)) (TriangleHull p j) :=
  (distinct_polygon_interior_disjoint hFG).mono
    (interior_mono (OrderedCircle.triangle_subset_polygon o i))
    (OrderedCircle.triangle_subset_polygon p j)

end N11Formalization.ActualDelaunayPolygonSeparation
#check @N11Formalization.ActualDelaunayPolygonSeparation.distinct_polygon_interior_disjoint
#check @N11Formalization.ActualDelaunayPolygonSeparation.distinct_primal_triangles_disjoint
#print axioms N11Formalization.ActualDelaunayPolygonSeparation.distinct_polygon_interior_disjoint
#print axioms N11Formalization.ActualDelaunayPolygonSeparation.distinct_primal_triangles_disjoint
