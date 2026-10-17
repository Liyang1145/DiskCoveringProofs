import N11Formalization.ActualIncidentPolygonConvexity
import N11Formalization.ActualIncidentChordGeometry

/-! Positive ACTUAL primal facets connect consecutive vertices of their
true incident polygon. This is the reverse of adjacent_facets, and excludes
artificial diagonals from positive-primal-edge data. The finite3/4/5-gon
index classification is kernel-decide only; metric geometry is proved overR. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualIncidentFacetAdjacency
open ActualVoronoiIncidence ActualIncidentPolygonOrder ActualIncidentPolygonConvexity
open ActualIncidentPolygonFacets ActualIncidentFacetGerms ActualHubEdgeGeometry
open ActualIncidentChordGeometry FlashTiling

def CyclicTriple {n : ℕ} (i j k : Fin n) : Prop :=
  (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)

instance {n : ℕ} (i j k : Fin n) : Decidable (CyclicTriple i j k) := by
  unfold CyclicTriple
  infer_instance

theorem finite_pair_classification {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    ∀ i j : Fin n, i ≠ j →
      j = finRotate n i ∨ i = finRotate n j ∨
        ∃ k l : Fin n, k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧
          CyclicTriple i j k ∧ CyclicTriple i l j := by
  interval_cases n <;> decide

theorem orient_cycle (a b k : Point) : orient a b k = orient b k a := by
  simp only [orient,det2,PiLp.sub_apply]
  ring

theorem orient_swap (a b k : Point) : orient a b k = -orient a k b := by
  simp only [orient,det2,PiLp.sub_apply]
  ring

theorem OrderedCircle.increasing_triple_orientation {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f)
    {i j k : Fin (incident c f.point).card} (hij : i < j) (hjk : j < k) :
    0 < orient (c (o.order i).val) (c (o.order j).val) (c (o.order k).val) := by
  have hab := o.sorted hij
  have hbt := o.sorted hjk
  have hI := OrderedCircle.angle_bounds o i
  have hJ := OrderedCircle.angle_bounds o j
  have hK := OrderedCircle.angle_bounds o k
  have hba : siteAngle c f.point (o.order j).val <
      siteAngle c f.point (o.order i).val+2*Real.pi := by linarith
  have hta : siteAngle c f.point (o.order k).val <
      siteAngle c f.point (o.order i).val+2*Real.pi := by linarith
  have hh := circle_orient_strict hab hba hbt hta
  rw [o.coordinates i,o.coordinates j,o.coordinates k,orient_translate_scale]
  exact mul_pos (sq_pos_of_pos o.positive) hh

theorem OrderedCircle.cyclic_triple_orientation {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f)
    {i j k : Fin (incident c f.point).card} (hijk : CyclicTriple i j k) :
    0 < orient (c (o.order i).val) (c (o.order j).val) (c (o.order k).val) := by
  rcases hijk with hij | hjk | hki
  · exact OrderedCircle.increasing_triple_orientation o hij.1 hij.2
  · rw [orient_cycle]
    exact OrderedCircle.increasing_triple_orientation o hjk.1 hjk.2
  · rw [orient_cycle,orient_cycle]
    exact OrderedCircle.increasing_triple_orientation o hki.1 hki.2

theorem perp_inner_orient (a b k : Point) :
    inner ℝ (perp (b-a)) (k-a) = orient a b k := by
  rw [PinTangentGeometry.inner_coords]
  simp only [perp,Matrix.cons_val_zero,Matrix.cons_val_one,orient,det2,PiLp.sub_apply]
  ring

theorem supporting_chord_no_straddle {c : Fin 11 → Point} {v d : Point}
    {i j k l : Fin 11} (hij : c i ≠ c j)
    (hd : d ∈ PairCone c v i j)
    (hk : k ∈ incident c v) (hl : l ∈ incident c v)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (hpos : 0 < orient (c i) (c j) (c k))
    (hneg : orient (c i) (c j) (c l) < 0) : False := by
  have hchord : c j-c i ≠ 0 := sub_ne_zero.mpr hij.symm
  obtain ⟨t,ht⟩ := parallel_of_orthogonal (perp_ne hchord) hchord
    (perp_inner (c j-c i)) hd.1
  have hK := hd.2 k hk hki hkj
  have hL := hd.2 l hl hli hlj
  rw [ht,real_inner_smul_left,perp_inner_orient] at hK hL
  have htneg : t < 0 := by
    by_contra hnot
    exact not_lt_of_ge (mul_nonneg (le_of_not_gt hnot) hpos.le) hK
  exact not_lt_of_ge (mul_pos_of_neg_of_neg htneg hneg).le hL

theorem OrderedCircle.label_injective {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) :
    Function.Injective (fun i => (o.order i).val) := by
  intro i j he
  exact o.order.injective (Subtype.ext he)

theorem OrderedCircle.pairCone_adjacent {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) (hc : Function.Injective c)
    {i j : Fin (incident c f.point).card} (hij : i ≠ j) {d : Point}
    (hd : d ∈ PairCone c f.point (o.order i).val (o.order j).val) :
    j = finRotate (incident c f.point).card i ∨
      i = finRotate (incident c f.point).card j := by
  rcases finite_pair_classification f.at_least_three f.at_most_five i j hij with
    hn | hn | ⟨k,l,hki,hkj,hli,hlj,hcycK,hcycL⟩
  · exact Or.inl hn
  · exact Or.inr hn
  · have hK := OrderedCircle.cyclic_triple_orientation o hcycK
    have hL := OrderedCircle.cyclic_triple_orientation o hcycL
    have hneg : orient (c (o.order i).val) (c (o.order j).val) (c (o.order l).val) < 0 := by
      rw [orient_swap]
      exact neg_neg_of_pos hL
    exact (supporting_chord_no_straddle
      (fun he => hij (OrderedCircle.label_injective o (hc he))) hd
      (o.order k).property (o.order l).property
      (fun he => hki (OrderedCircle.label_injective o he))
      (fun he => hkj (OrderedCircle.label_injective o he))
      (fun he => hli (OrderedCircle.label_injective o he))
      (fun he => hlj (OrderedCircle.label_injective o he)) hK hneg).elim

theorem OrderedCircle.positive_facet_adjacent {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) (hc : Function.Injective c)
    {i j : Fin (incident c f.point).card} (hij : i ≠ j)
    (g : FacetGerm c r f.point (o.order i).val (o.order j).val) :
    j = finRotate (incident c f.point).card i ∨
      i = finRotate (incident c f.point).card j :=
  OrderedCircle.pairCone_adjacent o hc hij
    (facetGerm_direction_pairCone (o.order i).property (o.order j).property g)

end N11Formalization.ActualIncidentFacetAdjacency
#check @N11Formalization.ActualIncidentFacetAdjacency.OrderedCircle.positive_facet_adjacent
#print axioms N11Formalization.ActualIncidentFacetAdjacency.finite_pair_classification
#print axioms N11Formalization.ActualIncidentFacetAdjacency.OrderedCircle.pairCone_adjacent
#print axioms N11Formalization.ActualIncidentFacetAdjacency.OrderedCircle.positive_facet_adjacent
