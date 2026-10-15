import N11Formalization.ActualIncidentPolygonFacets
import N11Formalization.FlashTilingFan

/-! The true ordered incident circle is a strictly convex polygon, and its
hull is covered by a fan with an arbitrary chosen apex. All convexity and
covering premises are produced from the actual incident circle; no candidate
ring convexity or unverified polygon drawing is imported as a premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualIncidentPolygonConvexity
open ActualVoronoiIncidence ActualIncidentPolygonOrder ActualCyclicChordSupport
open ActualIncidentPolygonFacets FlashTiling

theorem chord_det_identity (a b : ℝ) (p : Point) :
    det2 (circleMap b-circleMap a) p =
      -2*Real.sin ((b-a)/2)*inner ℝ (circleMap ((a+b)/2)) p := by
  rw [det2,PinTangentGeometry.inner_coords]
  simp only [PiLp.sub_apply,circleMap_apply_zero,circleMap_apply_one]
  rw [Real.cos_sub_cos,Real.sin_sub_sin]
  have he : (b+a)/2 = (a+b)/2 := by ring
  rw [he]
  ring

theorem circle_orient_strict {a b t : ℝ} (hab : a < b)
    (hba : b < a+2*Real.pi) (hbt : b < t) (hta : t < a+2*Real.pi) :
    0 < orient (circleMap a) (circleMap b) (circleMap t) := by
  have hs := (empty_arc_support hab hba hbt hta).2
  have hsin : 0 < Real.sin ((b-a)/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [orient,chord_det_identity]
  exact mul_pos_of_neg_of_neg (by linarith) hs

theorem ordered_circle_strict_convex {m : ℕ} (hm : 0 < m)
    (theta : Fin (m+1) → ℝ) (hs : StrictMono theta)
    (hb : ∀ i, -Real.pi < theta i ∧ theta i ≤ Real.pi) :
    RingConvex (fun i => circleMap (theta i)) (finRotate (m+1)) := by
  intro i k hki hkn
  obtain ⟨t,ht,hbt,hta⟩ := complement_lift theta hs hb i k hki hkn
  obtain ⟨hab,hba⟩ := gap_bounds hm theta hs hb i
  have hh := circle_orient_strict hab hba hbt hta
  rwa [ht,nextAngle_circleMap] at hh

theorem orient_translate_scale (v a b k : Point) (rho : ℝ) :
    orient (v+rho • a) (v+rho • b) (v+rho • k) = rho^2*orient a b k := by
  have h1 : (v+rho • b)-(v+rho • a) = rho • (b-a) := by module
  have h2 : (v+rho • k)-(v+rho • a) = rho • (k-a) := by module
  rw [orient,h1,h2,det2_smul_left,det2_smul]
  change rho*(rho*orient a b k) = rho^2*orient a b k
  ring

theorem circle_polygon_strict_convex {n : ℕ} (hn : 1 < n)
    (theta : Fin n → ℝ) (hs : StrictMono theta)
    (hb : ∀ i, -Real.pi < theta i ∧ theta i ≤ Real.pi) :
    ∀ i k : Fin n, k ≠ i → k ≠ finRotate n i →
      0 < orient (circleMap (theta i)) (circleMap (theta (finRotate n i)))
        (circleMap (theta k)) := by
  cases n with
  | zero => omega
  | succ m =>
    exact ordered_circle_strict_convex (by omega) theta hs hb

theorem OrderedCircle.strict_convex_polygon {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) :
    ∀ i k : Fin (incident c f.point).card, k ≠ i →
      k ≠ finRotate (incident c f.point).card i →
      0 < orient (c (o.order i).val)
        (c (o.order (finRotate (incident c f.point).card i)).val) (c (o.order k).val) := by
  intro i k hki hkn
  have hh := circle_polygon_strict_convex (by have h := f.at_least_three; omega)
    (fun j => siteAngle c f.point (o.order j).val) o.sorted
    (fun j => OrderedCircle.angle_bounds o j) i k hki hkn
  rw [o.coordinates i,o.coordinates (finRotate (incident c f.point).card i),
    o.coordinates k,orient_translate_scale]
  exact mul_pos (sq_pos_of_pos o.positive) hh

theorem strict_polygon_hull_fan {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5)
    (q : Fin n → Point)
    (hcv : ∀ i k : Fin n, k ≠ i → k ≠ finRotate n i →
      0 < orient (q i) (q (finRotate n i)) (q k))
    (x : Point) {p : Point} (hp : p ∈ convexHull ℝ (Set.range q)) :
    ∃ i : Fin n, p ∈ convexHull ℝ ({x,q i,q (finRotate n i)} : Set Point) := by
  cases n with
  | zero => omega
  | succ m =>
    have hmlo : 2 ≤ m := by omega
    have hmhi : m ≤ 4 := by omega
    have hss : ∀ i : Fin (m+1),
        finRotate (m+1) ((finRotate (m+1)).symm i) = i :=
      (finRotate (m+1)).apply_symm_apply
    have hne1 : ∀ i : Fin (m+1), finRotate (m+1) i ≠ i := by
      interval_cases m <;> intro i <;> fin_cases i <;> decide
    have hne2 : ∀ i : Fin (m+1),
        finRotate (m+1) i ≠ (finRotate (m+1)).symm i := by
      interval_cases m <;> intro i <;> fin_cases i <;> decide
    have hne3 : ∀ i : Fin (m+1), finRotate (m+1) (finRotate (m+1) i) ≠ i := by
      interval_cases m <;> intro i <;> fin_cases i <;> decide
    have hcl : SumClosed q (finRotate (m+1)) := by
      simp only [SumClosed,Finset.sum_sub_distrib]
      have hsum : (∑ i, q (finRotate (m+1) i)) = ∑ i, q i := by
        exact Fintype.sum_equiv (finRotate (m+1)) _ _ (fun _ => rfl)
      rw [hsum,sub_self]
    have hpoly : ∀ i : Fin (m+1), 0 ≤ phi q (finRotate (m+1)) i p := by
      intro i
      apply convexHull_subset_orient_nonneg q (q i) (q (finRotate (m+1) i)) ?_ hp
      intro k
      by_cases hki : k = i
      · subst k
        simp [orient,det2]
      by_cases hkn : k = finRotate (m+1) i
      · subst k
        change 0 ≤ det2 (q (finRotate (m+1) i)-q i) (q (finRotate (m+1) i)-q i)
        rw [det2_self]
      exact (hcv i k hki hkn).le
    exact fan_dart hss hne1 hne2 hne3 hcv hcl hpoly

theorem OrderedCircle.hull_fan {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) (x : Point) {p : Point}
    (hp : p ∈ convexHull ℝ (Set.range (fun i => c (o.order i).val))) :
    ∃ i : Fin (incident c f.point).card,
      p ∈ convexHull ℝ ({x,c (o.order i).val,
        c (o.order (finRotate (incident c f.point).card i)).val} : Set Point) :=
  strict_polygon_hull_fan f.at_least_three f.at_most_five _
    (OrderedCircle.strict_convex_polygon o) x hp

end N11Formalization.ActualIncidentPolygonConvexity
#check @N11Formalization.ActualIncidentPolygonConvexity.OrderedCircle.strict_convex_polygon
#check @N11Formalization.ActualIncidentPolygonConvexity.OrderedCircle.hull_fan
#print axioms N11Formalization.ActualIncidentPolygonConvexity.OrderedCircle.strict_convex_polygon
#print axioms N11Formalization.ActualIncidentPolygonConvexity.OrderedCircle.hull_fan
