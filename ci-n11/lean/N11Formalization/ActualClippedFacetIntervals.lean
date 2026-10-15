import N11Formalization.ActualIncidentFacetGerms

/-! Every nonempty ACTUAL clipped two-cell intersection is an exact compact
line interval. Its endpoints are onS1 or true nearest vertices. Singletons
are retained (not falsely counted as positive facets), and no genericity or
global-unclipped triangulation premise is used. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualClippedFacetIntervals
open ActualVoronoiCells ActualVoronoiIncidence ActualClippedCellPartition
open ActualVoronoiRadialExit ActualHubEdgeGeometry ActualBoundaryFacets

def ClippedCommon (c : Fin 11 → Point) (i j : Fin 11) : Set Point :=
  unitDisk ∩ (Cell c i ∩ Cell c j)

theorem clippedCommon_convex (c : Fin 11 → Point) (i j : Fin 11) :
    Convex ℝ (ClippedCommon c i j) := by
  unfold ClippedCommon
  rw [disk_eq_closedBall]
  exact (convex_closedBall (0 : Point) 1).inter ((cell_convex c i).inter (cell_convex c j))

theorem clippedCommon_closed (c : Fin 11 → Point) (i j : Fin 11) :
    IsClosed (ClippedCommon c i j) := by
  unfold ClippedCommon
  rw [disk_eq_closedBall]
  exact Metric.isClosed_closedBall.inter ((cell_closed c i).inter (cell_closed c j))

theorem triple_mem_vertices {c : Fin 11 → Point} {x : Point} {i j k : Fin 11}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hi : x ∈ Cell c i) (hj : x ∈ Cell c j) (hk : x ∈ Cell c k) :
    x ∈ Vertices c := by
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨j,
    Set.mem_iUnion.mpr ⟨k,hij,hki,hkj,⟨hi,hj⟩,hk⟩⟩⟩

theorem endpoint_circle_or_vertex {c : Fin 11 → Point} {i j : Fin 11}
    (hij : i ≠ j) {y u : Point} (hy : y ∈ ClippedCommon c i j)
    (hu : ‖u‖ = 1) (horth : inner ℝ u (c j-c i) = 0)
    (hstop : ∀ t : ℝ, 0 < t → ray y u t ∉ ClippedCommon c i j) :
    ‖y‖ = 1 ∨ y ∈ ClippedVertices c := by
  by_cases hy1 : ‖y‖ = 1
  · exact Or.inl hy1
  right
  have hyinside : ‖y‖ < 1 := lt_of_le_of_ne (mem_unitDisk.mp hy.1) hy1
  by_cases hthird : ∃ k : Fin 11, k ≠ i ∧ k ≠ j ∧ dist y (c k) = dist y (c i)
  · obtain ⟨k,hki,hkj,htie⟩ := hthird
    have hk : y ∈ Cell c k := by intro l; rw [htie]; exact hy.2.1 l
    exact ⟨hy.1,triple_mem_vertices hij hki hkj hy.2.1 hy.2.2 hk⟩
  · have hs : y ∈ PairStrict c i j := by
      intro k hki hkj
      apply lt_of_le_of_ne (hy.2.1 k)
      intro he
      exact hthird ⟨k,hki,hkj,he.symm⟩
    have hopen : IsOpen ({x : Point | ‖x‖ < 1} ∩ PairStrict c i j) :=
      (isOpen_lt continuous_norm continuous_const).inter (pairStrict_open c i j)
    obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp hopen y ⟨hyinside,hs⟩
    have ht : 0 < eps/2 := by linarith
    have hz : ray y u (eps/2) ∈ {x : Point | ‖x‖ < 1} ∩ PairStrict c i j := by
      apply hball
      apply Metric.mem_ball.mpr
      rw [ray_dist _ _ _ hu,abs_of_pos ht]
      linarith
    have heq := shifted_equidistant (le_antisymm (hy.2.1 j) (hy.2.2 i)) horth
      (t := eps/2)
    exact (hstop (eps/2) ht
      ⟨mem_unitDisk.mpr hz.1.le,pair_nearest_of_strict heq hz.2⟩).elim

structure FacetInterval (c : Fin 11 → Point) (i j : Fin 11) where
  base : Point
  direction : Point
  unit : ‖direction‖ = 1
  orthogonal : inner ℝ direction (c j-c i) = 0
  lo : ℝ
  hi : ℝ
  ordered : lo ≤ hi
  points : ClippedCommon c i j = ray base direction '' Set.Icc lo hi
  left_mem : ray base direction lo ∈ ClippedCommon c i j
  right_mem : ray base direction hi ∈ ClippedCommon c i j
  left_endpoint : ‖ray base direction lo‖ = 1 ∨
    ray base direction lo ∈ ClippedVertices c
  right_endpoint : ‖ray base direction hi‖ = 1 ∨
    ray base direction hi ∈ ClippedVertices c

theorem clippedCommon_interval {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j) (hne : (ClippedCommon c i j).Nonempty) :
    Nonempty (FacetInterval c i j) := by
  obtain ⟨x,hx⟩ := hne
  let d := c j-c i
  have hd : d ≠ 0 := sub_ne_zero.mpr (fun he => hij (hc he).symm)
  let u := centerDir (perp d)
  have hp := perp_ne hd
  have hu : ‖u‖ = 1 := centerDir_norm hp
  have hune : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have horth : inner ℝ u d = 0 := by
    change inner ℝ (‖perp d‖⁻¹ • perp d) d = 0
    rw [real_inner_smul_left,perp_inner,mul_zero]
  let S : Set ℝ := {t | ray x u t ∈ ClippedCommon c i j}
  have hRay : Continuous (ray x u) := by unfold ray; fun_prop
  have hclosed : IsClosed S := (clippedCommon_closed c i j).preimage hRay
  have hsub : S ⊆ Set.Icc (-2) 2 := by
    intro t ht
    have htri := dist_le_norm_add_norm (ray x u t) x
    rw [ray_dist _ _ _ hu] at htri
    have hy := mem_unitDisk.mp ht.1
    have hxn := mem_unitDisk.mp hx.1
    have habs : |t| ≤ 2 := by linarith
    exact abs_le.mp habs
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed hsub
  have h0 : (0 : ℝ) ∈ S := by simpa [S,ray] using hx
  have hconvex : Convex ℝ S := by
    intro t ht s hs a b ha hb hab
    have he : ray x u (a*t+b*s) = a • ray x u t+b • ray x u s := by
      have ha' : a = 1-b := by linarith
      rw [ha']
      unfold ray
      module
    change ray x u (a • t+b • s) ∈ ClippedCommon c i j
    simp only [smul_eq_mul]
    rw [he]
    exact clippedCommon_convex c i j ht hs ha hb hab
  obtain ⟨lo,hlo,hmin⟩ := hcompact.exists_isMinOn ⟨0,h0⟩ continuousOn_id
  obtain ⟨hi,hhi,hmax⟩ := hcompact.exists_isMaxOn ⟨0,h0⟩ continuousOn_id
  have horder : lo ≤ hi := hmin hhi
  have hS : S = Set.Icc lo hi := by
    apply Set.Subset.antisymm
    · exact fun t ht => ⟨hmin ht,hmax ht⟩
    · exact hconvex.ordConnected.out hlo hhi
  have hpoints : ClippedCommon c i j = ray x u '' Set.Icc lo hi := by
    ext y
    constructor
    · intro hy
      have hxeq := le_antisymm (hx.2.1 j) (hx.2.2 i)
      have hyeq := le_antisymm (hy.2.1 j) (hy.2.2 i)
      have hX := ActualBoundaryTieUniqueness.bisector_equation hxeq
      have hY := ActualBoundaryTieUniqueness.bisector_equation hyeq
      have hyorth : inner ℝ (y-x) d = 0 := by
        rw [inner_sub_left]
        change 2*inner ℝ x d = _ at hX
        change 2*inner ℝ y d = _ at hY
        linarith
      obtain ⟨t,ht⟩ := parallel_of_orthogonal hune hd horth hyorth
      have hyparam : ray x u t = y := by rw [ray,← ht]; abel
      have htS : t ∈ S := by change ray x u t ∈ ClippedCommon c i j; rwa [hyparam]
      exact ⟨t,by rwa [← hS],hyparam⟩
    · rintro ⟨t,ht,rfl⟩
      exact (show t ∈ S by rwa [hS])
  have hrightStop : ∀ t : ℝ, 0 < t → ray (ray x u hi) u t ∉ ClippedCommon c i j := by
    intro t ht hmem
    have he : ray (ray x u hi) u t = ray x u (hi+t) := by
      rw [ray,ray,ray,add_smul]
      abel
    rw [he] at hmem
    have hle := hmax (show hi+t ∈ S from hmem)
    change hi+t ≤ hi at hle
    linarith
  have hleftStop : ∀ t : ℝ, 0 < t → ray (ray x u lo) (-u) t ∉ ClippedCommon c i j := by
    intro t ht hmem
    have he : ray (ray x u lo) (-u) t = ray x u (lo-t) := by
      rw [ray,ray,ray,sub_smul,smul_neg]
      abel
    rw [he] at hmem
    have hle := hmin (show lo-t ∈ S from hmem)
    change lo ≤ lo-t at hle
    linarith
  have hleft := endpoint_circle_or_vertex hij hlo
    (by rw [norm_neg]; exact hu : ‖-u‖ = 1)
    (by rw [inner_neg_left,horth,neg_zero] : inner ℝ (-u) (c j-c i) = 0) hleftStop
  have hright := endpoint_circle_or_vertex hij hhi hu horth hrightStop
  exact ⟨⟨x,u,hu,horth,lo,hi,horder,hpoints,hlo,hhi,hleft,hright⟩⟩

theorem FacetInterval.positive_iff {c : Fin 11 → Point} {i j : Fin 11}
    (f : FacetInterval c i j) :
    f.lo < f.hi ↔ ∃ x ∈ ClippedCommon c i j, ∃ y ∈ ClippedCommon c i j, x ≠ y := by
  constructor
  · intro hlt
    refine ⟨ray f.base f.direction f.lo,f.left_mem,
      ray f.base f.direction f.hi,f.right_mem,?_⟩
    intro he
    have hz : (f.lo-f.hi) • f.direction = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr (add_left_cancel he)
    have hdne : f.direction ≠ 0 := norm_ne_zero_iff.mp (by rw [f.unit]; norm_num)
    exact smul_ne_zero (sub_ne_zero.mpr hlt.ne) hdne hz
  · rintro ⟨x,hx,y,hy,hxy⟩
    by_contra hnot
    have he : f.lo = f.hi := le_antisymm f.ordered (le_of_not_gt hnot)
    rw [f.points] at hx hy
    obtain ⟨s,hs,rfl⟩ := hx
    obtain ⟨t,ht,rfl⟩ := hy
    have hslo : s = f.lo := by rw [← he] at hs; exact le_antisymm hs.2 hs.1
    have htlo : t = f.lo := by rw [← he] at ht; exact le_antisymm ht.2 ht.1
    exact hxy (by rw [hslo,htlo])

end N11Formalization.ActualClippedFacetIntervals
#check @N11Formalization.ActualClippedFacetIntervals.clippedCommon_interval
#check @N11Formalization.ActualClippedFacetIntervals.FacetInterval.positive_iff
#print axioms N11Formalization.ActualClippedFacetIntervals.endpoint_circle_or_vertex
#print axioms N11Formalization.ActualClippedFacetIntervals.clippedCommon_interval
#print axioms N11Formalization.ActualClippedFacetIntervals.FacetInterval.positive_iff
