import N11Formalization.ActualVoronoiIncidence
import N11Formalization.ActualClippedCellPartition

/-! Exact local normal fans at ACTUAL nearest vertices. Nonincident sites
are excluded uniformly in a neighborhood, so all local cell membership is
determined by the incident polygon's homogeneous inequalities. Every incident
site has a nonempty OPEN strict sector, including cocircular4/5-site faces.
No cyclic polygon ordering, triangulation or embedded disk is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualVoronoiLocalFan
open ActualVoronoiCells ActualVoronoiIncidence ActualDelaunaySupport
open ActualHubEdgeGeometry ActualVoronoiRadialExit ActualClippedCellPartition

def NormalCone (c : Fin 11 → Point) (v : Point) (i : Fin 11) : Set Point :=
  {d | ∀ j ∈ incident c v, inner ℝ d (c j-c i) ≤ 0}

def StrictNormalCone (c : Fin 11 → Point) (v : Point) (i : Fin 11) : Set Point :=
  {d | ∀ j ∈ incident c v, j ≠ i → inner ℝ d (c j-c i) < 0}

def OutsideGap (c : Fin 11 → Point) (v : Point) : Set Point :=
  {x | ∀ i ∈ incident c v, ∀ j ∉ incident c v, dist x (c i) < dist x (c j)}

theorem outsideGap_open (c : Fin 11 → Point) (v : Point) :
    IsOpen (OutsideGap c v) := by
  classical
  have he : OutsideGap c v =
      ⋂ i : {i : Fin 11 // i ∈ incident c v},
      ⋂ j : {j : Fin 11 // j ∉ incident c v},
      {x : Point | dist x (c i.val) < dist x (c j.val)} := by
    ext x
    simp only [OutsideGap,Set.mem_setOf_eq,Set.mem_iInter]
    constructor
    · intro h i j
      exact h i.val i.property j.val j.property
    · intro h i hi j hj
      exact h ⟨i,hi⟩ ⟨j,hj⟩
  rw [he]
  exact isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ =>
    isOpen_lt (by fun_prop) (by fun_prop)

theorem vertex_mem_outsideGap (c : Fin 11 → Point) (v : Point) :
    v ∈ OutsideGap c v := by
  intro i hi j hj
  have hI := mem_incident.mp hi
  apply lt_of_le_of_ne (hI j)
  intro he
  apply hj
  apply mem_incident.mpr
  intro k
  rw [← he]
  exact hI k

theorem tied_distance_difference {v x a b : Point} (he : dist v a = dist v b) :
    dist x a^2-dist x b^2 = 2*inner ℝ (x-v) (b-a) := by
  have hV := square_difference v a b
  have hX := square_difference x a b
  rw [he,sub_self] at hV
  rw [inner_sub_left]
  linarith

theorem tied_le_iff {v x a b : Point} (he : dist v a = dist v b) :
    dist x a ≤ dist x b ↔ inner ℝ (x-v) (b-a) ≤ 0 := by
  have hdiff := tied_distance_difference (x := x) he
  constructor <;> intro h <;>
    nlinarith [dist_nonneg (x := x) (y := a),dist_nonneg (x := x) (y := b)]

theorem tied_lt_iff {v x a b : Point} (he : dist v a = dist v b) :
    dist x a < dist x b ↔ inner ℝ (x-v) (b-a) < 0 := by
  have hdiff := tied_distance_difference (x := x) he
  constructor <;> intro h <;>
    nlinarith [dist_nonneg (x := x) (y := a),dist_nonneg (x := x) (y := b)]

theorem cell_iff_normalCone {c : Fin 11 → Point} {v x : Point} {i : Fin 11}
    (hi : i ∈ incident c v) (hx : x ∈ OutsideGap c v) :
    x ∈ Cell c i ↔ x-v ∈ NormalCone c v i := by
  constructor
  · intro h j hj
    exact (tied_le_iff (le_antisymm ((mem_incident.mp hi) j)
      ((mem_incident.mp hj) i))).mp (h j)
  · intro h j
    by_cases hj : j ∈ incident c v
    · exact (tied_le_iff (le_antisymm ((mem_incident.mp hi) j)
        ((mem_incident.mp hj) i))).mpr (h j hj)
    · exact (hx i hi j hj).le

theorem strictCell_iff_strictNormalCone {c : Fin 11 → Point} {v x : Point} {i : Fin 11}
    (hi : i ∈ incident c v) (hx : x ∈ OutsideGap c v) :
    x ∈ StrictCell c i ↔ x-v ∈ StrictNormalCone c v i := by
  constructor
  · intro h j hj hji
    exact (tied_lt_iff (le_antisymm ((mem_incident.mp hi) j)
      ((mem_incident.mp hj) i))).mp (h j hji)
  · intro h j hji
    by_cases hj : j ∈ incident c v
    · exact (tied_lt_iff (le_antisymm ((mem_incident.mp hi) j)
        ((mem_incident.mp hj) i))).mpr (h j hj hji)
    · exact hx i hi j hj

/-- A uniform neighborhood for ALL incident labels, not one radius per label. -/
theorem local_normal_fan (c : Fin 11 → Point) (v : Point) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ x : Point, dist x v < eps →
      (∀ i ∈ incident c v, x ∈ Cell c i ↔ x-v ∈ NormalCone c v i) ∧
      (∀ i ∈ incident c v,
        x ∈ StrictCell c i ↔ x-v ∈ StrictNormalCone c v i) ∧
      incident c x ⊆ incident c v := by
  obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp (outsideGap_open c v)
    v (vertex_mem_outsideGap c v)
  refine ⟨eps,heps,fun x hx => ?_⟩
  have hgap := hball (Metric.mem_ball.mpr hx)
  refine ⟨fun i hi => cell_iff_normalCone hi hgap,
    fun i hi => strictCell_iff_strictNormalCone hi hgap,?_⟩
  intro j hj
  by_contra hjnot
  obtain ⟨i,hi⟩ := exists_nearest c v
  have hstrict := hgap i (mem_incident.mpr hi) j hjnot
  exact (not_lt_of_ge ((mem_incident.mp hj) i)) hstrict

theorem normalCone_convex (c : Fin 11 → Point) (v : Point) (i : Fin 11) :
    Convex ℝ (NormalCone c v i) := by
  intro x hx y hy a b ha hb _ j hj
  simp only [inner_add_left,real_inner_smul_left]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx j hj))
    (mul_nonpos_of_nonneg_of_nonpos hb (hy j hj))

theorem strictNormalCone_open (c : Fin 11 → Point) (v : Point) (i : Fin 11) :
    IsOpen (StrictNormalCone c v i) := by
  classical
  have he : StrictNormalCone c v i =
      ⋂ j : {j : Fin 11 // j ∈ incident c v ∧ j ≠ i},
      {d : Point | inner ℝ d (c j.val-c i) < 0} := by
    ext d
    simp only [StrictNormalCone,Set.mem_setOf_eq,Set.mem_iInter]
    constructor
    · intro h j
      exact h j.val j.property.1 j.property.2
    · intro h j hj hji
      exact h ⟨j,hj,hji⟩
  rw [he]
  exact isOpen_iInter_of_finite fun _ => isOpen_lt (by fun_prop) continuous_const

theorem strictNormalCone_smul {c : Fin 11 → Point} {v d : Point} {i : Fin 11}
    (hd : d ∈ StrictNormalCone c v i) {t : ℝ} (ht : 0 < t) :
    t • d ∈ StrictNormalCone c v i := by
  intro j hj hji
  rw [real_inner_smul_left]
  exact mul_neg_of_pos_of_neg ht (hd j hj hji)

/-- Strict radial exposure pays an actual open angular sector at every site. -/
theorem radial_mem_strictNormalCone {c : Fin 11 → Point}
    (hc : Function.Injective c) {v : Point} {i : Fin 11} (hi : i ∈ incident c v) :
    c i-v ∈ StrictNormalCone c v i := by
  intro j hj hji
  have hex := incident_sites_strictly_exposed hc hji.symm
    (mem_incident.mp hi) (mem_incident.mp hj)
  have he : c j-c i = (c j-v)-(c i-v) := by abel
  rw [he,inner_sub_right]
  linarith

theorem normal_fan_cover (c : Fin 11 → Point) (v d : Point) :
    ∃ i ∈ incident c v, d ∈ NormalCone c v i := by
  classical
  obtain ⟨i,hi⟩ := exists_nearest c v
  have hn : (incident c v).Nonempty := ⟨i,mem_incident.mpr hi⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (incident c v)
    (fun k => inner ℝ d (c k)) hn
  refine ⟨j,hj,?_⟩
  intro k hk
  rw [inner_sub_right]
  exact sub_nonpos.mpr (hmax k hk)

theorem strict_sectors_disjoint {c : Fin 11 → Point} {v : Point} {i j : Fin 11}
    (hi : i ∈ incident c v) (hj : j ∈ incident c v) (hij : i ≠ j) :
    Disjoint (StrictNormalCone c v i) (StrictNormalCone c v j) := by
  apply Set.disjoint_left.mpr
  intro d hI hJ
  have h1 := hI j hj hij.symm
  have h2 := hJ i hi hij
  simp only [inner_sub_right] at h1 h2
  linarith

/-- Every incident cell really occupies a positive sector INSIDE D.
The witness and its radius bound belong to the original cover and original r. -/
theorem incident_positive_clipped_sector {c : Fin 11 → Point} {r : ℝ}
    (hc : Function.Injective c) (hcover : Covers c r) {v : Point}
    (hv : ‖v‖ < 1) {i : Fin 11} (hi : i ∈ incident c v) :
    ∃ t : ℝ, 0 < t ∧
      ray v (c i-v) t ∈ interior (ClippedCell c i) ∧
      dist (ray v (c i-v) t) (c i) ≤ r := by
  have hopen : IsOpen ({x : Point | ‖x‖ < 1} ∩ OutsideGap c v) :=
    (isOpen_lt continuous_norm continuous_const).inter (outsideGap_open c v)
  obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp hopen v
    ⟨hv,vertex_mem_outsideGap c v⟩
  let d := c i-v
  let t := eps/(2*(‖d‖+1))
  have hden : 0 < 2*(‖d‖+1) := by positivity
  have ht : 0 < t := div_pos heps hden
  have hte : t*‖d‖ < eps := by
    have he : t*(2*(‖d‖+1)) = eps := by dsimp [t]; field_simp
    nlinarith [norm_nonneg d]
  have hx : ray v d t ∈ {x : Point | ‖x‖ < 1} ∩ OutsideGap c v := by
    apply hball
    apply Metric.mem_ball.mpr
    rw [ray,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact hte
  have hstrict : ray v d t ∈ StrictCell c i := by
    apply (strictCell_iff_strictNormalCone hi hx.2).mpr
    rw [ray,add_sub_cancel_left]
    exact strictNormalCone_smul (radial_mem_strictNormalCone hc hi) ht
  have hint : ray v d t ∈ interior (ClippedCell c i) := by
    rw [ClippedCell,interior_inter]
    refine ⟨?_,?_⟩
    · apply interior_mono (show {x : Point | ‖x‖ < 1} ⊆ unitDisk from
        fun x h => mem_unitDisk.mpr h.le)
      rw [(isOpen_lt continuous_norm continuous_const).interior_eq]
      exact hx.1
    · apply interior_mono (strictCell_subset c i)
      rw [(strictCell_open c i).interior_eq]
      exact hstrict
  exact ⟨t,ht,hint,nearest_le_radius hcover (mem_unitDisk.mpr hx.1.le)
    (strictCell_subset c i hstrict)⟩

end N11Formalization.ActualVoronoiLocalFan
#check @N11Formalization.ActualVoronoiLocalFan.local_normal_fan
#check @N11Formalization.ActualVoronoiLocalFan.incident_positive_clipped_sector
#print axioms N11Formalization.ActualVoronoiLocalFan.local_normal_fan
#print axioms N11Formalization.ActualVoronoiLocalFan.normal_fan_cover
#print axioms N11Formalization.ActualVoronoiLocalFan.incident_positive_clipped_sector
