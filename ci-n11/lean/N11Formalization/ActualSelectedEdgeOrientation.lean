import N11Formalization.ActualHubNeighborCoverage

/-! Real planar orientation across every selected shared edge.
Opposite sides are derived from genuine nearest support planes, or from
the coherent local fan when the primal witnesses coincide. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSelectedEdgeOrientation
open ActualVoronoiCells ActualVoronoiIncidence ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementSideMultiplicity
open ActualIncidentChordGeometry ActualIncidentFacetAdjacency
open ActualDelaunayPolygonSeparation ActualHubEdgeGeometry ActualHubEdgeEndpointGeometry
open ActualIncidentFanRefinement ActualIncidentPolygonOrder
open FlashTiling

theorem selected_triple_orient_ne {c : Fin 11 → Point} (hc : Function.Injective c)
    {r : ℝ} (R : Refinement c r) {a : R.Index} {i j k : Fin 11}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hi : i ∈ labelSet R a) (hj : j ∈ labelSet R a) (hk : k ∈ labelSet R a) :
    orient (c i) (c j) (c k) ≠ 0 := by
  have hh := incident_chord_noncollinear hc hij hki hkj
    (mem_incident.mpr (nearest_of_label_mem R hi))
    (mem_incident.mpr (nearest_of_label_mem R hj))
    (mem_incident.mpr (nearest_of_label_mem R hk))
  rwa [real_inner_comm,perp_inner_orient] at hh

theorem distinct_witness_edge_opposite {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} (R : Refinement c r)
    {a b : R.Index} (hw : R.witness a ≠ R.witness b)
    {i j k l : Fin 11} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j)
    (hai : i ∈ labelSet R a) (haj : j ∈ labelSet R a) (hak : k ∈ labelSet R a)
    (hbi : i ∈ labelSet R b) (hbj : j ∈ labelSet R b) (hbl : l ∈ labelSet R b) :
    orient (c i) (c j) (c k) * orient (c i) (c j) (c l) < 0 := by
  let u := R.witness a
  let v := R.witness b
  let n := (2:ℝ) • (u-v)
  let d := ActualDelaunaySupport.support u (ActualDelaunaySupport.lift (c i)) -
    ActualDelaunaySupport.support v (ActualDelaunaySupport.lift (c i))
  have hnearU := nearest_of_label_mem R hai
  have hnearV := nearest_of_label_mem R hbi
  have hsep := polygon_planes_separate hnearU hnearV
  have hmemU (t : Fin 11) (ht : t ∈ labelSet R a) : c t ∈ PolygonHull c u :=
    subset_convexHull ℝ _ ⟨t,mem_incident.mpr (nearest_of_label_mem R ht),rfl⟩
  have hmemV (t : Fin 11) (ht : t ∈ labelSet R b) : c t ∈ PolygonHull c v :=
    subset_convexHull ℝ _ ⟨t,mem_incident.mpr (nearest_of_label_mem R ht),rfl⟩
  have hzeroI : gap n d (c i) = 0 :=
    le_antisymm (hsep.2 (hmemV i hbi)) (hsep.1 (hmemU i hai))
  have hzeroJ : gap n d (c j) = 0 :=
    le_antisymm (hsep.2 (hmemV j hbj)) (hsep.1 (hmemU j haj))
  have hn : n ≠ 0 := smul_ne_zero (by norm_num) (sub_ne_zero.mpr hw)
  have hedge : c j-c i ≠ 0 := sub_ne_zero.mpr (hc.ne hij.symm)
  have horth : inner ℝ n (c j-c i) = 0 := by
    dsimp [gap] at hzeroI hzeroJ
    rw [inner_sub_right]
    linarith
  obtain ⟨t,ht⟩ := parallel_of_orthogonal (perp_ne hedge) hedge
    (perp_inner (c j-c i)) horth
  have htne : t ≠ 0 := by
    intro he
    rw [he,zero_smul] at ht
    exact hn ht
  have hgap (p : Point) : gap n d p = t*orient (c i) (c j) p := by
    calc
      gap n d p = inner ℝ n (p-c i) := by
        dsimp [gap] at hzeroI ⊢
        rw [inner_sub_right]
        linarith
      _ = t*orient (c i) (c j) p := by
        rw [ht,real_inner_smul_left,perp_inner_orient]
  have hk := hsep.1 (hmemU k hak)
  have hl := hsep.2 (hmemV l hbl)
  change 0 ≤ gap n d (c k) at hk
  change gap n d (c l) ≤ 0 at hl
  rw [hgap] at hk hl
  have hkne := selected_triple_orient_ne hc R hij hki hkj hai haj hak
  have hlne := selected_triple_orient_ne hc R hij hli hlj hbi hbj hbl
  rcases lt_or_gt_of_ne htne with htneg | htpos
  · have hkneg : orient (c i) (c j) (c k) < 0 := by
      rcases lt_or_gt_of_ne hkne with hh | hh
      · exact hh
      · exact (not_lt_of_ge hk (mul_neg_of_neg_of_pos htneg hh)).elim
    have hlpos : 0 < orient (c i) (c j) (c l) := by
      rcases lt_or_gt_of_ne hlne with hh | hh
      · exact (not_lt_of_ge hl (mul_pos_of_neg_of_neg htneg hh)).elim
      · exact hh
    exact mul_neg_of_neg_of_pos hkneg hlpos
  · have hkpos : 0 < orient (c i) (c j) (c k) := by
      have hh := (mul_nonneg_iff_of_pos_left htpos).mp hk
      exact lt_of_le_of_ne hh (Ne.symm hkne)
    have hlneg : orient (c i) (c j) (c l) < 0 := by
      rcases lt_or_gt_of_ne hlne with hh | hh
      · exact hh
      · exact (not_lt_of_ge hl (mul_pos htpos hh)).elim
    exact mul_neg_of_pos_of_neg hkpos hlneg

theorem fan_next_value {n : ℕ} {a : Fin n} (ha : FanIndex a) :
    (finRotate n a).val = a.val+1 := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ m =>
    have hne : a ≠ Fin.last m := by
      intro he
      have hh := congrArg Fin.val he
      have hb := ha.2
      change a.val = m at hh
      omega
    exact coe_finRotate_of_ne_last hne

theorem shared_fan_edge_contains_zero {a b i j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (hij : i ≠ j)
    (hiA : i=0 ∨ i=a ∨ i=a+1) (hjA : j=0 ∨ j=a ∨ j=a+1)
    (hiB : i=0 ∨ i=b ∨ i=b+1) (hjB : j=0 ∨ j=b ∨ j=b+1) :
    i=0 ∨ j=0 := by omega

theorem finite_fan_shared_edge_opposite {n : ℕ} (hn3 : 3 ≤ n) (_hn5 : n ≤ 5) :
    ∀ a b i j k l : Fin n, FanIndex a → FanIndex b → a ≠ b →
      i ≠ j → k ≠ i → k ≠ j → l ≠ i → l ≠ j →
      i ∈ indexTriangle (by omega : 0 < n) a →
      j ∈ indexTriangle (by omega : 0 < n) a →
      k ∈ indexTriangle (by omega : 0 < n) a →
      i ∈ indexTriangle (by omega : 0 < n) b →
      j ∈ indexTriangle (by omega : 0 < n) b →
      l ∈ indexTriangle (by omega : 0 < n) b →
      (CyclicTriple i j k ∧ CyclicTriple i l j) ∨
        (CyclicTriple i k j ∧ CyclicTriple i j l) := by
  intro a b i j k l ha hb hab hij hki hkj hli hlj hAi hAj hAk hBi hBj hBl
  have hna := fan_next_value ha
  have hnb := fan_next_value hb
  simp only [indexTriangle,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff]
    at hAi hAj hAk hBi hBj hBl
  rw [hna] at hAi hAj hAk
  rw [hnb] at hBi hBj hBl
  simp only [FanIndex] at ha hb
  have habv : a.val ≠ b.val := fun he => hab (Fin.ext he)
  have hijv : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hkiv : k.val ≠ i.val := fun he => hki (Fin.ext he)
  have hkjv : k.val ≠ j.val := fun he => hkj (Fin.ext he)
  have hliv : l.val ≠ i.val := fun he => hli (Fin.ext he)
  have hljv : l.val ≠ j.val := fun he => hlj (Fin.ext he)
  have hz := shared_fan_edge_contains_zero ha.1 hb.1 habv hijv hAi hAj hBi hBj
  simp only [CyclicTriple,Fin.lt_def]
  rcases hz with hz | hz <;> by_cases habv' : a.val < b.val <;> omega

theorem same_witness_edge_opposite {c : Fin 11 → Point}
    {r : ℝ} (R : Refinement c r)
    {a b : R.Index} (hab : a ≠ b) (hw : R.witness a = R.witness b)
    {i j k l : Fin 11} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j)
    (hai : i ∈ labelSet R a) (haj : j ∈ labelSet R a) (hak : k ∈ labelSet R a)
    (hbi : i ∈ labelSet R b) (hbj : j ∈ labelSet R b) (hbl : l ∈ labelSet R b) :
    orient (c i) (c j) (c k) * orient (c i) (c j) (c l) < 0 := by
  have hv : a.1 = b.1 := by
    apply Subtype.ext
    simpa only [Refinement.witness,R.base] using hw
  rcases a with ⟨v,A⟩
  rcases b with ⟨w,B⟩
  dsimp only at hv
  subst w
  have hAB : A.val ≠ B.val := by
    intro he
    exact hab (by rw [Subtype.ext he])
  let o := R.order v
  have hnear (t : Fin 11) (ht : t ∈ labelSet R ⟨v,A⟩ ∨ t ∈ labelSet R ⟨v,B⟩) :
      t ∈ incident c (R.face v).point := by
    rcases ht with ht | ht
    · have hh := @nearest_of_label_mem c r R ⟨v,A⟩ t ht
      change (R.face v).point ∈ Cell c t at hh
      exact mem_incident.mpr hh
    · have hh := @nearest_of_label_mem c r R ⟨v,B⟩ t ht
      change (R.face v).point ∈ Cell c t at hh
      exact mem_incident.mpr hh
  let I := o.order.symm ⟨i,hnear i (Or.inl hai)⟩
  let J := o.order.symm ⟨j,hnear j (Or.inl haj)⟩
  let K := o.order.symm ⟨k,hnear k (Or.inl hak)⟩
  let L := o.order.symm ⟨l,hnear l (Or.inr hbl)⟩
  have hI : (o.order I).val = i := congrArg Subtype.val (o.order.apply_symm_apply _)
  have hJ : (o.order J).val = j := congrArg Subtype.val (o.order.apply_symm_apply _)
  have hK : (o.order K).val = k := congrArg Subtype.val (o.order.apply_symm_apply _)
  have hL : (o.order L).val = l := congrArg Subtype.val (o.order.apply_symm_apply _)
  have hAI := (local_label_mem R v A I).mp (by rwa [hI])
  have hAJ := (local_label_mem R v A J).mp (by rwa [hJ])
  have hAK := (local_label_mem R v A K).mp (by rwa [hK])
  have hBI := (local_label_mem R v B I).mp (by rwa [hI])
  have hBJ := (local_label_mem R v B J).mp (by rwa [hJ])
  have hBL := (local_label_mem R v B L).mp (by rwa [hL])
  have hIJ : I ≠ J := fun he => hij (by rw [← hI,← hJ,he])
  have hKI : K ≠ I := fun he => hki (by rw [← hK,← hI,he])
  have hKJ : K ≠ J := fun he => hkj (by rw [← hK,← hJ,he])
  have hLI : L ≠ I := fun he => hli (by rw [← hL,← hI,he])
  have hLJ : L ≠ J := fun he => hlj (by rw [← hL,← hJ,he])
  have hcases := finite_fan_shared_edge_opposite (R.face v).at_least_three
    (R.face v).at_most_five A.val B.val I J K L A.property B.property hAB
    hIJ hKI hKJ hLI hLJ hAI hAJ hAK hBI hBJ hBL
  rcases hcases with ⟨hk,hl⟩ | ⟨hk,hl⟩
  · have hpos := OrderedCircle.cyclic_triple_orientation o hk
    have hneg := OrderedCircle.cyclic_triple_orientation o hl
    rw [hI,hJ,hK] at hpos
    rw [hI,hL,hJ,orient_swap] at hneg
    exact mul_neg_of_pos_of_neg hpos (by linarith)
  · have hneg := OrderedCircle.cyclic_triple_orientation o hk
    have hpos := OrderedCircle.cyclic_triple_orientation o hl
    rw [hI,hK,hJ,orient_swap] at hneg
    rw [hI,hJ,hL] at hpos
    exact mul_neg_of_neg_of_pos (by linarith) hpos

theorem actual_shared_edge_opposite {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} (R : Refinement c r)
    {a b : R.Index} (hab : a ≠ b)
    {i j k l : Fin 11} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j)
    (hai : i ∈ labelSet R a) (haj : j ∈ labelSet R a) (hak : k ∈ labelSet R a)
    (hbi : i ∈ labelSet R b) (hbj : j ∈ labelSet R b) (hbl : l ∈ labelSet R b) :
    orient (c i) (c j) (c k) * orient (c i) (c j) (c l) < 0 := by
  by_cases hw : R.witness a = R.witness b
  · exact same_witness_edge_opposite R hab hw hij hki hkj hli hlj hai haj hak hbi hbj hbl
  · exact distinct_witness_edge_opposite hc R hw hij hki hkj hli hlj hai haj hak hbi hbj hbl

end N11Formalization.ActualSelectedEdgeOrientation
#check @N11Formalization.ActualSelectedEdgeOrientation.actual_shared_edge_opposite
#print axioms N11Formalization.ActualSelectedEdgeOrientation.distinct_witness_edge_opposite
#print axioms N11Formalization.ActualSelectedEdgeOrientation.same_witness_edge_opposite
#print axioms N11Formalization.ActualSelectedEdgeOrientation.actual_shared_edge_opposite
