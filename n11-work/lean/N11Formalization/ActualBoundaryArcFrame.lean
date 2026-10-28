import N11Formalization.ActualRingDirectionOrder

/-! Genuine periodic CLOSED interval representation of every actual ring cap.
No endpoint-lift, interval-cover or private-point premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryArcFrame
open DSHTopologyInterior ActualRingEssentiality ActualRingDirectionOrder

def period : ℝ := 2*Real.pi
def halfWidth (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) : ℝ :=
  capHalfWidth (c (ringSite i)) r
def arcCenter (c : Fin 11 → Point) (i : Fin 9) (n : ℤ) : ℝ :=
  midpointAngle c i+(n:ℝ)*period
def leftEnd (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) (n : ℤ) : ℝ :=
  arcCenter c i n-halfWidth c r i
def rightEnd (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) (n : ℤ) : ℝ :=
  arcCenter c i n+halfWidth c r i
def Arc (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) (n : ℤ) : Set ℝ :=
  Set.Icc (leftEnd c r i n) (rightEnd c r i n)

theorem circleMap_periodic (t : ℝ) (n : ℤ) :
    circleMap (t+(n:ℝ)*period) = circleMap t := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [circleMap,period,Real.cos_add_int_mul_two_pi,Real.sin_add_int_mul_two_pi]

theorem midpoint_direction {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) (i : Fin 9) :
    circleMap (midpointAngle c i) = centerDir (c (ringSite i)) := by
  exact circleMap_circleAngle _ (centerDir_norm
    (ActualInwardNormalization.touching_ne_zero (by linarith) (hR.ring_meets i.isLt)))

theorem cosine_of_lift {t m h : ℝ} (hh0 : 0 ≤ h) (hhpi : h ≤ Real.pi)
    {n : ℤ} (hn : |t-m-(n:ℝ)*period| ≤ h) :
    Real.cos h ≤ Real.cos (t-m) := by
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (abs_nonneg (t-m-(n:ℝ)*period)) hhpi hn
  change Real.cos h ≤ Real.cos |t-m-(n:ℝ)*(2*Real.pi)| at hcos
  rw [Real.cos_abs,Real.cos_sub_int_mul_two_pi] at hcos
  exact hcos

theorem cap_iff_lift {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (i : Fin 9) (t : ℝ) :
    dist (circleMap t) (c (ringSite i)) ≤ r ↔ ∃ n : ℤ, t ∈ Arc c r i n := by
  have hr1 : r < 1 := by linarith
  have hmeet : MeetsCircle c r (ringSite i) := hR.ring_meets i.isLt
  have hne := ActualInwardNormalization.touching_ne_zero hr1 hmeet
  have h0 : 0 ≤ halfWidth c r i := capHalfWidth_nonneg _ _
  have hpi : halfWidth c r i ≤ Real.pi :=
    (capHalfWidth_le_arcsin hne (Covers.nonneg hc) hr1).trans
      (by linarith [Real.arcsin_le_pi_div_two r,Real.pi_pos])
  have he := (cap_eq_of_meets hne (Covers.nonneg hc) hr1 hmeet (circleMap_norm t)).1
  have hinner : inner ℝ (circleMap t) (centerDir (c (ringSite i))) =
      Real.cos (t-midpointAngle c i) := by
    rw [← midpoint_direction hc hr hR i,inner_circleMap]
  rw [hinner] at he
  constructor
  · intro hd
    obtain ⟨n,hn⟩ := exists_abs_sub_two_pi_mul_int_le h0 hpi (he.mp hd)
    refine ⟨n,?_⟩
    change midpointAngle c i+(n:ℝ)*period-halfWidth c r i ≤ t ∧
      t ≤ midpointAngle c i+(n:ℝ)*period+halfWidth c r i
    have hb := abs_le.mp hn
    change -halfWidth c r i ≤ t-midpointAngle c i-(n:ℝ)*period ∧
      t-midpointAngle c i-(n:ℝ)*period ≤ halfWidth c r i at hb
    constructor <;> linarith [hb.1,hb.2]
  · rintro ⟨n,hn⟩
    apply he.mpr
    apply cosine_of_lift (n := n) h0 hpi
    apply abs_le.mpr
    change midpointAngle c i+(n:ℝ)*period-halfWidth c r i ≤ t ∧
      t ≤ midpointAngle c i+(n:ℝ)*period+halfWidth c r i at hn
    constructor <;> linarith [hn.1,hn.2]

theorem real_interval_cover {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) (t : ℝ) :
    ∃ (i : Fin 9) (n : ℤ), t ∈ Arc c r i n := by
  obtain ⟨j,hj⟩ := hc (circleMap t) (mem_unitDisk.mpr (circleMap_norm t).le)
  have hring : j.val < 9 := (hR j).mp ⟨circleMap t,circleMap_norm t,hj⟩
  let i : Fin 9 := ⟨j.val,hring⟩
  obtain ⟨n,hn⟩ := (cap_iff_lift hc hr hR i t).mp hj
  exact ⟨i,n,hn⟩

theorem mem_shift_copy {c : Fin 11 → Point} {r : ℝ} {i : Fin 9} {n k : ℤ} {t : ℝ}
    (ht : t ∈ Arc c r i k) :
    t+((n-k:ℤ):ℝ)*period ∈ Arc c r i n := by
  change arcCenter c i k-halfWidth c r i ≤ t ∧ t ≤ arcCenter c i k+halfWidth c r i at ht
  change arcCenter c i n-halfWidth c r i ≤ t+((n-k:ℤ):ℝ)*period ∧
    t+((n-k:ℤ):ℝ)*period ≤ arcCenter c i n+halfWidth c r i
  simp only [arcCenter,Int.cast_sub] at ht ⊢
  constructor <;> nlinarith [ht.1,ht.2]

/-- Every chosen periodic COPY has a private point relative to all other
actual ring caps, not only relative to a finite sampled interval list. -/
theorem private_in_copy {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) (i : Fin 9) (n : ℤ) :
    ∃ t ∈ Arc c r i n, ∀ j : Fin 9, j ≠ i → ∀ k : ℤ, t ∉ Arc c r j k := by
  obtain ⟨x,hx,hself,hother⟩ := private_circle_point hc hr hR i
  let a := circleAngle x
  have hpoint : circleMap a = x := circleMap_circleAngle _ hx
  have hcap : dist (circleMap a) (c (ringSite i)) ≤ r := by rwa [hpoint]
  obtain ⟨k,hk⟩ := (cap_iff_lift hc hr hR i a).mp hcap
  let t := a+((n-k:ℤ):ℝ)*period
  refine ⟨t,mem_shift_copy hk,?_⟩
  intro j hji m hm
  have hd := (cap_iff_lift hc hr hR j t).mpr ⟨m,hm⟩
  have htx : circleMap t = x := by
    change circleMap (a+((n-k:ℤ):ℝ)*period) = x
    rw [circleMap_periodic,hpoint]
  rw [htx] at hd
  have hsites : ringSite j ≠ ringSite i := by
    intro h
    exact hji (Fin.ext (congrArg (fun q : Fin 11 => q.val) h))
  exact not_le_of_gt (hother (ringSite j) hsites) hd

end N11Formalization.ActualBoundaryArcFrame
#check @N11Formalization.ActualBoundaryArcFrame.cap_iff_lift
#check @N11Formalization.ActualBoundaryArcFrame.real_interval_cover
#check @N11Formalization.ActualBoundaryArcFrame.private_in_copy
#print axioms N11Formalization.ActualBoundaryArcFrame.cap_iff_lift
#print axioms N11Formalization.ActualBoundaryArcFrame.private_in_copy
