import N11Formalization.ActualHubAngleSum

/-! Actual radial cone non-overlap and the real one-turn hub lift.
The local geometric lemmas use the produced triangle interiors, not a
postulated angular packing premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubOneTurn
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualSiteAngleChain ActualAnglePhase ActualMetricAngleAtoms
open ActualFaceCircumradiusAtoms ActualTriangleBoundaryChain
open ActualBoundaryChainConservation ActualHubLinkCycles FlashTiling

/-- Exact two-dimensional Cramer decomposition in the oriented edge basis. -/
theorem cramer_edges (u v d : Point) (hdet : det2 u v ≠ 0) :
    d = (det2 d v / det2 u v) • u + (det2 u d / det2 u v) • v := by
  have hn : u.ofLp 0*v.ofLp 1-u.ofLp 1*v.ofLp 0 ≠ 0 := hdet
  have hn2 : v.ofLp 1*u.ofLp 0-v.ofLp 0*u.ofLp 1 ≠ 0 := by
    convert hn using 1 <;> ring
  ext k
  fin_cases k <;> simp [det2] <;> field_simp [hn,hn2] <;> ring

/-- Positive barycentric coefficients produce a point of the ordinary interior. -/
theorem positive_edges_mem_interior {a u v : Point} (hdet : 0 < det2 u v)
    {p : Point} (hb : 0 < det2 (p-a) v / det2 u v)
    (hc : 0 < det2 u (p-a) / det2 u v)
    (hs : det2 (p-a) v / det2 u v + det2 u (p-a) / det2 u v < 1) :
    p ∈ interior (convexHull ℝ ({a,a+u,a+v} : Set Point)) := by
  let B : Point → ℝ := fun q => det2 (q-a) v / det2 u v
  let C : Point → ℝ := fun q => det2 u (q-a) / det2 u v
  have hB : Continuous B := by
    exact ((det2Snd v).continuous_of_finiteDimensional.comp
      (continuous_id.sub continuous_const)).div_const _
  have hC : Continuous C := by
    exact ((det2Fst u).continuous_of_finiteDimensional.comp
      (continuous_id.sub continuous_const)).div_const _
  let S : Set Point := {q | 0 < B q ∧ 0 < C q ∧ B q+C q < 1}
  have hS : IsOpen S :=
    (isOpen_lt continuous_const hB).inter
      ((isOpen_lt continuous_const hC).inter (isOpen_lt (hB.add hC) continuous_const))
  have hsub : S ⊆ convexHull ℝ ({a,a+u,a+v} : Set Point) := by
    intro q hq
    obtain ⟨hb',hc',hs'⟩ := hq
    have hsum : 0 < B q+C q := add_pos hb' hc'
    have ha : a ∈ convexHull ℝ ({a,a+u,a+v} : Set Point) :=
      subset_convexHull ℝ _ (by simp)
    have hu : a+u ∈ convexHull ℝ ({a,a+u,a+v} : Set Point) :=
      subset_convexHull ℝ _ (by simp)
    have hv : a+v ∈ convexHull ℝ ({a,a+u,a+v} : Set Point) :=
      subset_convexHull ℝ _ (by simp)
    have hmiddle := (convex_convexHull ℝ ({a,a+u,a+v} : Set Point)) hu hv
      (div_nonneg hb'.le hsum.le) (div_nonneg hc'.le hsum.le)
      (by field_simp <;> ring : B q/(B q+C q)+C q/(B q+C q)=1)
    have hfull := (convex_convexHull ℝ ({a,a+u,a+v} : Set Point)) ha hmiddle
      (by linarith : 0 ≤ 1-(B q+C q)) hsum.le (by ring)
    have hcr := cramer_edges u v (q-a) hdet.ne'
    change q-a = B q • u+C q • v at hcr
    have he : (1-(B q+C q)) • a + (B q+C q) •
      ((B q/(B q+C q)) • (a+u)+(C q/(B q+C q)) • (a+v)) = q := by
      rw [smul_add,smul_smul,smul_smul]
      have heB : (B q+C q)*(B q/(B q+C q)) = B q := by field_simp
      have heC : (B q+C q)*(C q/(B q+C q)) = C q := by field_simp
      rw [heB,heC,smul_add,smul_add]
      have ha1 : (1-(B q+C q)) • a+B q • a+C q • a = a := by module
      calc
        _ = ((1-(B q+C q)) • a+B q • a+C q • a)+(B q • u+C q • v) := by abel
        _ = a+(q-a) := by rw [ha1,← hcr]
        _ = q := by abel
    rwa [he] at hfull
  apply interior_mono hsub
  rw [hS.interior_eq]
  exact ⟨hb,hc,hs⟩

/-- A strict radial cone direction enters the actual triangle interior for
all sufficiently small positive scalar parameters. -/
theorem cone_ray_mem_interior {a u v d : Point} (hdet : 0 < det2 u v)
    (hu : 0 < det2 u d) (hv : 0 < det2 d v)
    {t : ℝ} (ht : 0 < t)
    (hsmall : t*(det2 d v / det2 u v + det2 u d / det2 u v) < 1) :
    a+t • d ∈ interior (convexHull ℝ ({a,a+u,a+v} : Set Point)) := by
  apply positive_edges_mem_interior hdet
  · simpa only [add_sub_cancel_left,det2_smul_left,mul_div_assoc] using
      mul_pos ht (div_pos hv hdet)
  · simpa only [add_sub_cancel_left,det2_smul,mul_div_assoc] using
      mul_pos ht (div_pos hu hdet)
  · simpa only [add_sub_cancel_left,det2_smul_left,det2_smul,mul_div_assoc,mul_add]
      using hsmall

/-- Disjoint genuine triangle interiors give disjoint strict radial cones
at any shared apex. This is the geometric producer needed for angle packing. -/
theorem strict_cones_disjoint {a u v x y d : Point}
    (huv : 0 < det2 u v) (hxy : 0 < det2 x y)
    (hdisj : Disjoint (interior (convexHull ℝ ({a,a+u,a+v} : Set Point)))
      (interior (convexHull ℝ ({a,a+x,a+y} : Set Point))))
    (hud : 0 < det2 u d) (hdv : 0 < det2 d v)
    (hxd : 0 < det2 x d) (hdy : 0 < det2 d y) : False := by
  let U : ℝ := det2 d v/det2 u v+det2 u d/det2 u v
  let V : ℝ := det2 d y/det2 x y+det2 x d/det2 x y
  have hU : 0 < U := add_pos (div_pos hdv huv) (div_pos hud huv)
  have hV : 0 < V := add_pos (div_pos hdy hxy) (div_pos hxd hxy)
  let t : ℝ := 1/(U+V+1)
  have ht : 0 < t := by dsimp [t]; positivity
  have htU : t*U < 1 := by
    dsimp [t]
    rw [one_div_mul_eq_div,div_lt_one (by positivity : 0 < U+V+1)]
    linarith
  have htV : t*V < 1 := by
    dsimp [t]
    rw [one_div_mul_eq_div,div_lt_one (by positivity : 0 < U+V+1)]
    linarith
  exact Set.disjoint_left.mp hdisj
    (cone_ray_mem_interior huv hud hdv ht htU)
    (cone_ray_mem_interior hxy hxd hdy ht htV)


/-- In principal endpoint lifts, a positive triangle angle crosses the cut
exactly when the final lift lies below the initial lift. -/
theorem positive_phase_real_lift {alpha a b : ℝ}
    (ha : -Real.pi < a ∧ a ≤ Real.pi) (hb : -Real.pi < b ∧ b ≤ Real.pi)
    (halpha : 0 < alpha ∧ alpha < Real.pi)
    (hphase : (alpha : Real.Angle) = (b : Real.Angle)-(a : Real.Angle)) :
    alpha = b-a + if b<a then 2*Real.pi else 0 := by
  have hz : ((alpha-(b-a) : ℝ) : Real.Angle)=0 := by
    rw [Real.Angle.coe_sub,Real.Angle.coe_sub,hphase,sub_self]
  obtain ⟨n,hn⟩ := Real.Angle.coe_eq_zero_iff.mp hz
  have hn' : (n:ℝ)*(2*Real.pi)=alpha-(b-a) := by
    simpa only [zsmul_eq_mul] using hn
  have hnlo : (-1:ℝ) < (n:ℝ) := by nlinarith [Real.pi_pos]
  have hnhi : (n:ℝ) < 2 := by nlinarith [Real.pi_pos]
  have hnlo' : -1 < n := by exact_mod_cast hnlo
  have hnhi' : n < 2 := by exact_mod_cast hnhi
  have hn01 : n=0 ∨ n=1 := by omega
  by_cases hba : b<a
  · rw [if_pos hba]
    rcases hn01 with rfl | rfl
    · norm_num at hn'
      linarith
    · norm_num at hn'
      linarith
  · rw [if_neg hba]
    have hab : a ≤ b := le_of_not_gt hba
    rcases hn01 with rfl | rfl
    · norm_num at hn'
      linarith
    · norm_num at hn'
      linarith [Real.pi_pos]

/-- Any two positive sectors which wrap the principal cut have a common
strict radial direction, including a start ray with principal angle pi. -/
theorem wrapped_rays_common_direction {u v x y : Point}
    (hu : u≠0) (hv : v≠0) (hx : x≠0) (hy : y≠0)
    (huv : Real.pi < directionAngle u-directionAngle v)
    (hxy : Real.pi < directionAngle x-directionAngle y) :
    ∃ d : Point, 0 < det2 u d ∧ 0 < det2 d v ∧
      0 < det2 x d ∧ 0 < det2 d y := by
  let a := directionAngle u
  let b := directionAngle v
  let c := directionAngle x
  let e := directionAngle y
  have ha : -Real.pi < a ∧ a ≤ Real.pi := circleAngle_mem_Ioc _
  have hb : -Real.pi < b ∧ b ≤ Real.pi := circleAngle_mem_Ioc _
  have hc : -Real.pi < c ∧ c ≤ Real.pi := circleAngle_mem_Ioc _
  have he : -Real.pi < e ∧ e ≤ Real.pi := circleAngle_mem_Ioc _
  have ha0 : 0 < a := by dsimp [a,b] at *; linarith
  have hc0 : 0 < c := by dsimp [c,e] at *; linarith
  have hb0 : b < 0 := by dsimp [a,b] at *; linarith
  have he0 : e < 0 := by dsimp [c,e] at *; linarith
  have hbpi : 0 < b+Real.pi := by linarith
  have hepi : 0 < e+Real.pi := by linarith
  obtain ⟨eps,heps0,heps⟩ := exists_between
    (show 0 < min (min a c) (min (b+Real.pi) (e+Real.pi)) by positivity)
  have hea : eps < a := lt_of_lt_of_le heps ((min_le_left _ _).trans (min_le_left _ _))
  have hec : eps < c := lt_of_lt_of_le heps ((min_le_left _ _).trans (min_le_right _ _))
  have heb : eps < b+Real.pi := lt_of_lt_of_le heps ((min_le_right _ _).trans (min_le_left _ _))
  have hee : eps < e+Real.pi := lt_of_lt_of_le heps ((min_le_right _ _).trans (min_le_right _ _))
  let theta := Real.pi+eps
  have start (z : Point) (hz : z≠0) (hangle : directionAngle z ≤ Real.pi)
      (hepsangle : eps < directionAngle z) : 0 < det2 z (circleMap theta) := by
    rw [direction_representation hz,det2_smul_left,ActualRingShoelacePositive.det_circleMap]
    apply mul_pos (norm_pos_iff.mpr hz)
    apply Real.sin_pos_of_pos_of_lt_pi <;> dsimp [theta] <;> linarith
  have finish (z : Point) (hz : z≠0) (hangle : directionAngle z < 0)
      (hepsangle : eps < directionAngle z+Real.pi) : 0 < det2 (circleMap theta) z := by
    rw [direction_representation hz,det2_smul,ActualRingShoelacePositive.det_circleMap]
    apply mul_pos (norm_pos_iff.mpr hz)
    have hs : Real.sin (directionAngle z-theta) =
        Real.sin (directionAngle z+2*Real.pi-theta) := by
      rw [show directionAngle z+2*Real.pi-theta=(directionAngle z-theta)+2*Real.pi by ring,
        Real.sin_add_two_pi]
    rw [hs]
    apply Real.sin_pos_of_pos_of_lt_pi <;> dsimp [theta] <;> linarith
  exact ⟨circleMap theta,start u hu ha.2 hea,finish v hv hb0 heb,
    start x hx hc.2 hec,finish y hy he0 hee⟩

/-- The indexed actual hull, expressed at any cyclic face slot. -/
theorem actual_hull_at_slot {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    R.hull A = convexHull ℝ ({c (R.labels A s),c (R.labels A (s+1)),
      c (R.labels A (s+2))} : Set Point) := by
  fin_cases s <;>
    simp [Refinement.hull,Refinement.labels,ActualIncidentFanRefinement.TriangleHull,
      ActualIncidentFanRefinement.triangleLabels,Set.insert_comm,Set.pair_comm] <;>
    congr 1 <;> ext p <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto

def slotStart {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) : Point :=
  c (R.labels A (s+1))-c (R.labels A s)

def slotEnd {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) : Point :=
  c (R.labels A (s+2))-c (R.labels A s)

def slotDelta {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) : ℝ :=
  directionAngle (slotEnd R A s)-directionAngle (slotStart R A s)

def Wrapped {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) : Prop :=
  directionAngle (slotEnd R A s)<directionAngle (slotStart R A s)

instance {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (A : R.Index) (s : Fin 3) : Decidable (Wrapped R A s) := Classical.propDecidable _

theorem actual_slot_det_positive {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    0 < det2 (slotStart R A s) (slotEnd R A s) := by
  change 0 < orient (c (R.labels A s)) (c (R.labels A (s+1))) (c (R.labels A (s+2)))
  rw [actual_cyclic_face_orient]
  exact (Refinement.real_triangle R A).2.2

theorem actual_slot_rays_ne_zero {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    slotStart R A s≠0 ∧ slotEnd R A s≠0 := by
  have hp := actual_slot_det_positive R A s
  constructor <;> intro he
  · rw [he,det2_zero_left] at hp
    exact lt_irrefl 0 hp
  · simp [he,det2] at hp

theorem actual_slot_real_lift {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    faceAngle R A s = slotDelta R A s + if Wrapped R A s then 2*Real.pi else 0 := by
  apply positive_phase_real_lift (circleAngle_mem_Ioc _) (circleAngle_mem_Ioc _)
    (actual_face_angle_strict R A s)
  exact actual_face_slot_phase R A s

theorem actual_wrapped_gap {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) (hw : Wrapped R A s) :
    Real.pi < directionAngle (slotStart R A s)-directionAngle (slotEnd R A s) := by
  have he := actual_slot_real_lift R A s
  rw [if_pos hw] at he
  have hp := (actual_face_angle_strict R A s).2
  dsimp [slotDelta] at he
  linarith

/-- The actual disjoint triangles allow at most one wrapped face slot at
any site. This conclusion is produced from actual geometry for any degree. -/
theorem actual_wrapped_slot_unique {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A B : R.Index} {s t : Fin 3}
    (hsite : R.labels A s=R.labels B t)
    (hA : Wrapped R A s) (hB : Wrapped R B t) : A=B ∧ s=t := by
  by_cases hAB : A=B
  · subst B
    exact ⟨rfl,Refinement.labels_injective R A hsite⟩
  · have hdisj := Refinement.triangles_interior_disjoint R hAB
    rw [actual_hull_at_slot R A s,actual_hull_at_slot R B t,← hsite] at hdisj
    have hcone : Disjoint
        (interior (convexHull ℝ ({c (R.labels A s),
          c (R.labels A s)+slotStart R A s,c (R.labels A s)+slotEnd R A s} : Set Point)))
        (interior (convexHull ℝ ({c (R.labels A s),
          c (R.labels A s)+slotStart R B t,c (R.labels A s)+slotEnd R B t} : Set Point))) := by
      simpa only [slotStart,slotEnd,← hsite,add_sub_cancel] using hdisj
    obtain ⟨d,hud,hdv,hxd,hdy⟩ := wrapped_rays_common_direction
      (actual_slot_rays_ne_zero R A s).1 (actual_slot_rays_ne_zero R A s).2
      (actual_slot_rays_ne_zero R B t).1 (actual_slot_rays_ne_zero R B t).2
      (actual_wrapped_gap R A s hA) (actual_wrapped_gap R B t hB)
    exact (strict_cones_disjoint (actual_slot_det_positive R A s)
      (actual_slot_det_positive R B t) hcone hud hdv hxd hdy).elim

theorem real_weighted_triangle_row (t : Fin 3 → Fin 11) (i : Fin 11) (w : Fin 11 → ℝ) :
    (∑ j : Fin 11, triangleBoundary t i j • w j) =
      (if i=t 0 then w (t 1)-w (t 2) else 0) +
      (if i=t 1 then w (t 2)-w (t 0) else 0) +
      (if i=t 2 then w (t 0)-w (t 1) else 0) := by
  simp only [triangleBoundary,add_zsmul,sub_zsmul,Finset.sum_add_distrib,
    ite_and,ite_smul,one_zsmul,zero_zsmul,Finset.sum_ite_irrel]
  simp only [Finset.sum_neg_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_const_zero]
  split_ifs <;> abel

theorem one_face_real_delta {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (i : Fin 11) :
    (∑ s : Fin 3, if R.labels A s=i then slotDelta R A s else 0) =
      -(∑ j : Fin 11, coefficient R A i j • directionAngle (c j-c i)) := by
  simp only [coefficient]
  rw [real_weighted_triangle_row,Fin.sum_univ_three]
  simp only [slotDelta,slotStart,slotEnd,
    eq_comm (a := i) (b := R.labels A 0),eq_comm (a := i) (b := R.labels A 1),
    eq_comm (a := i) (b := R.labels A 2)]
  by_cases h0 : R.labels A 0=i <;> by_cases h1 : R.labels A 1=i <;>
    by_cases h2 : R.labels A 2=i <;> simp [h0,h1,h2] <;> abel

theorem actual_hub_real_delta_zero {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val) :
    (∑ A : R.Index, ∑ s : Fin 3, if R.labels A s=i then slotDelta R A s else 0)=0 := by
  simp_rw [one_face_real_delta]
  rw [Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  have he : (∑ j : Fin 11, ∑ A : R.Index,
        coefficient R A i j • directionAngle (c j-c i)) =
      ∑ j : Fin 11, total R i j • directionAngle (c j-c i) := by
    simp only [total,Finset.sum_smul]
  rw [he]
  have ht (j : Fin 11) : total R i j=0 := by
    apply total_nonboundary_zero h hr R
    intro hb
    have hh := boundary_labels_ring i j hb
    omega
  simp only [ht,zero_zsmul,Finset.sum_const_zero,neg_zero]

def wrappedSlots {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) : Finset (R.Index × Fin 3) := by
  classical
  exact Finset.univ.filter (fun p => R.labels p.1 p.2=i ∧ Wrapped R p.1 p.2)

theorem actual_wrappedSlots_card_le_one {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) : (wrappedSlots R i).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have hA := (Finset.mem_filter.mp ha).2
  have hB := (Finset.mem_filter.mp hb).2
  obtain ⟨hAB,hst⟩ := actual_wrapped_slot_unique R (hA.1.trans hB.1.symm) hA.2 hB.2
  exact Prod.ext hAB hst

theorem actual_hub_sum_eq_wrap_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val) :
    siteFaceSum R i = (wrappedSlots R i).card*(2*Real.pi) := by
  classical
  have hslot (A : R.Index) (s : Fin 3) :
      (if R.labels A s=i then faceAngle R A s else 0) =
      (if R.labels A s=i then slotDelta R A s else 0) +
        (if R.labels A s=i ∧ Wrapped R A s then 2*Real.pi else 0) := by
    rw [actual_slot_real_lift]
    split_ifs <;> simp_all
  unfold siteFaceSum
  simp_rw [hslot]
  simp_rw [Finset.sum_add_distrib]
  rw [actual_hub_real_delta_zero h hr R i hi,zero_add]
  have hc : (∑ A : R.Index, ∑ s : Fin 3,
      if R.labels A s=i ∧ Wrapped R A s then 2*Real.pi else 0) =
      ∑ p : R.Index × Fin 3, if R.labels p.1 p.2=i ∧ Wrapped R p.1 p.2 then 2*Real.pi else 0 := by
    rw [Fintype.sum_prod_type]
  rw [hc]
  change (∑ p : R.Index × Fin 3, if R.labels p.1 p.2=i ∧ Wrapped R p.1 p.2 then 2*Real.pi else 0) =
    ((Finset.univ.filter (fun p : R.Index × Fin 3 => R.labels p.1 p.2=i ∧ Wrapped R p.1 p.2)).card : ℝ)*(2*Real.pi)
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
/-- Exact real angle sum of every actual hub, with no degree restriction. -/
theorem actual_hub_angle_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val) : siteFaceSum R i=2*Real.pi := by
  apply ActualHubAngleSum.hub_sum_eq_two_pi_of_upper h hr R i hi
  rw [actual_hub_sum_eq_wrap_count h hr R i hi]
  have hc : ((wrappedSlots R i).card : ℝ) ≤ 1 := by
    exact_mod_cast actual_wrappedSlots_card_le_one R i
  nlinarith [Real.pi_pos]

end N11Formalization.ActualHubOneTurn
#print axioms N11Formalization.ActualHubOneTurn.strict_cones_disjoint


#print axioms N11Formalization.ActualHubOneTurn.actual_hub_angle_sum


