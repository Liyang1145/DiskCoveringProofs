import N11Formalization.ActualBoundaryOverlapAdjacency
import N11Formalization.EndpointInterval
import N11Formalization.ActualMixedCircleCapacity

/-! Actual ring-intersection -> whole-cap cluster lift.
The large test cap is radius2r about the ACTUAL common point p.
The entire periodic cap copy, not just its midpoint/endpoints, lies in
one large-cap copy. Ordered intermediate complete caps then lie there too.
No short-common-lift premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCapClusterLift
open DSHTopologyInterior ActualRingDirectionOrder ActualBoundaryArcFrame
open ActualBoundaryArcOrder ActualBoundaryOverlapAdjacency
open EndpointIntervalV3

def bigMidpoint (p : Point) : ℝ := circleAngle (centerDir p)
def BigArc (p : Point) (r : ℝ) (n : ℤ) : Set ℝ :=
  Set.Icc (bigMidpoint p+(n:ℝ)*period-capHalfWidth p (2*r))
    (bigMidpoint p+(n:ℝ)*period+capHalfWidth p (2*r))

theorem big_cap_iff {p : Point} {r : ℝ} (hp : p ≠ 0) (hr0 : 0 ≤ r)
    (hr : r < 19/50) (hm : ∃ x : Point, ‖x‖ = 1 ∧ dist x p ≤ 2*r) (t : ℝ) :
    dist (circleMap t) p ≤ 2*r ↔ ∃ n : ℤ, t ∈ BigArc p r n := by
  have he := cap_mem_iff_periodicInterval hp (by linarith : 0 ≤ 2*r)
    (by linarith : 2*r < 1) hm t
  rw [he]
  constructor
  · rintro ⟨n,hL,hR⟩
    refine ⟨n,?_,?_⟩
    · change bigMidpoint p+(n:ℝ)*period-capHalfWidth p (2*r) ≤ t
      change bigMidpoint p-capHalfWidth p (2*r)+(n:ℝ)*period ≤ t at hL
      linarith
    · change t ≤ bigMidpoint p+(n:ℝ)*period+capHalfWidth p (2*r)
      change t ≤ bigMidpoint p+capHalfWidth p (2*r)+(n:ℝ)*period at hR
      linarith
  · rintro ⟨n,hL,hR⟩
    refine ⟨n,?_,?_⟩
    · change bigMidpoint p-capHalfWidth p (2*r)+(n:ℝ)*period ≤ t
      change bigMidpoint p+(n:ℝ)*period-capHalfWidth p (2*r) ≤ t at hL
      linarith
    · change t ≤ bigMidpoint p+capHalfWidth p (2*r)+(n:ℝ)*period
      change t ≤ bigMidpoint p+(n:ℝ)*period+capHalfWidth p (2*r) at hR
      linarith

theorem big_halfWidth_lt {p : Point} {r : ℝ} (hp : p ≠ 0) (hr0 : 0 ≤ r)
    (hr : r < 19/50) : capHalfWidth p (2*r) < 9/10 :=
  (capHalfWidth_le_arcsin hp (by linarith) (by linarith)).trans_lt
    ((Real.arcsin_le_arcsin (show 2*r ≤ (19:ℝ)/25 by linarith)).trans_lt
      ActualMixedCircleCapacity.arcsin_double_R0_lt)

theorem copy_nonempty (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) (n : ℤ) :
    arcCenter c i n ∈ Arc c r i n := by
  change arcCenter c i n-halfWidth c r i ≤ arcCenter c i n ∧
    arcCenter c i n ≤ arcCenter c i n+halfWidth c r i
  have hw : 0 ≤ halfWidth c r i := capHalfWidth_nonneg _ _
  constructor <;> linarith

theorem copy_in_one_big_copy {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {p : Point} {i : Fin 9} (hpi : dist p (c (ringSite i)) ≤ r) (n : ℤ) :
    p ≠ 0 ∧ ∃ m : ℤ, Arc c r i n ⊆ BigArc p r m := by
  have hr0 := Covers.nonneg hc
  have hcap (t : ℝ) (ht : t ∈ Arc c r i n) : dist (circleMap t) p ≤ 2*r := by
    have hi := (cap_iff_lift hc hr hR i t).mpr ⟨n,ht⟩
    have hh := dist_triangle (circleMap t) (c (ringSite i)) p
    rw [dist_comm (c (ringSite i)) p] at hh
    linarith
  let a := arcCenter c i n
  have hma := hcap a (copy_nonempty c r i n)
  have hp : p ≠ 0 := by
    intro hz
    rw [hz,dist_zero_right,circleMap_norm] at hma
    linarith
  have hm : ∃ x : Point, ‖x‖ = 1 ∧ dist x p ≤ 2*r := ⟨circleMap a,circleMap_norm a,hma⟩
  obtain ⟨m,hmA⟩ := (big_cap_iff hp hr0 hr hm a).mp hma
  refine ⟨hp,m,?_⟩
  intro t ht
  obtain ⟨k,hk⟩ := (big_cap_iff hp hr0 hr hm t).mp (hcap t ht)
  have hw := halfWidth_le_small hc hr hR i
  have hbig := big_halfWidth_lt hp hr0 hr
  have hbig0 := capHalfWidth_nonneg p (2*r)
  have hsame : k = m := by
    by_contra hnot
    have hn : k+1 ≤ m ∨ m+1 ≤ k := by omega
    have ht' := ht
    change a-halfWidth c r i ≤ t ∧ t ≤ a+halfWidth c r i at ht'
    change bigMidpoint p+(m:ℝ)*period-capHalfWidth p (2*r) ≤ a ∧
      a ≤ bigMidpoint p+(m:ℝ)*period+capHalfWidth p (2*r) at hmA
    change bigMidpoint p+(k:ℝ)*period-capHalfWidth p (2*r) ≤ t ∧
      t ≤ bigMidpoint p+(k:ℝ)*period+capHalfWidth p (2*r) at hk
    dsimp [period] at hmA hk
    rcases hn with hn | hn
    · have hR' : (k:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast hn
      nlinarith [Real.pi_gt_three,Real.pi_lt_d20,ht'.1,ht'.2,hmA.1,hmA.2,hk.1,hk.2]
    · have hR' : (m:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast hn
      nlinarith [Real.pi_gt_three,Real.pi_lt_d20,ht'.1,ht'.2,hmA.1,hmA.2,hk.1,hk.2]
  rwa [hsame] at hk

theorem ends_in_big {c : Fin 11 → Point} {r : ℝ} {i : Fin 9} {n m : ℤ} {p : Point}
    (hsub : Arc c r i n ⊆ BigArc p r m) :
    bigMidpoint p+(m:ℝ)*period-capHalfWidth p (2*r) ≤ leftEnd c r i n ∧
      rightEnd c r i n ≤ bigMidpoint p+(m:ℝ)*period+capHalfWidth p (2*r) := by
  have hle : leftEnd c r i n ≤ rightEnd c r i n := by
    dsimp [leftEnd,rightEnd]
    have hw : 0 ≤ halfWidth c r i := capHalfWidth_nonneg _ _
    linarith
  exact ⟨(hsub ⟨le_rfl,hle⟩).1,(hsub ⟨hle,le_rfl⟩).2⟩

/-- Every entire intermediate ACTUAL cap is in the same large-cap lift. -/
theorem intermediate_copy_in_big {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j k : Fin 9} (hij : i ≠ j) (hjk : j ≠ k) {n m l b : ℤ} {p : Point}
    (hijc : arcCenter c i n < arcCenter c j m)
    (hjkc : arcCenter c j m < arcCenter c k l)
    (hI : Arc c r i n ⊆ BigArc p r b) (hK : Arc c r k l ⊆ BigArc p r b) :
    Arc c r j m ⊆ BigArc p r b := by
  have heI := ends_in_big hI
  have heK := ends_in_big hK
  have hIJ := endpoints_ordered hc hr hR hij hijc
  have hJK := endpoints_ordered hc hr hR hjk hjkc
  intro t ht
  exact ⟨heI.1.trans (hIJ.1.le.trans ht.1),ht.2.trans (hJK.2.le.trans heK.2)⟩

theorem BigArc.shift {p : Point} {r t : ℝ} {m n : ℤ}
    (ht : t ∈ BigArc p r m) :
    t+(n:ℝ)*period ∈ BigArc p r (m+n) := by
  change bigMidpoint p+(m:ℝ)*period-capHalfWidth p (2*r) ≤ t ∧
    t ≤ bigMidpoint p+(m:ℝ)*period+capHalfWidth p (2*r) at ht
  change bigMidpoint p+((m+n:ℤ):ℝ)*period-capHalfWidth p (2*r) ≤ t+(n:ℝ)*period ∧
    t+(n:ℝ)*period ≤ bigMidpoint p+((m+n:ℤ):ℝ)*period+capHalfWidth p (2*r)
  push_cast
  constructor <;> nlinarith [ht.1,ht.2]

theorem shift_subset_big {c : Fin 11 → Point} {r : ℝ} {i : Fin 9} {p : Point}
    {k n : ℤ} (hsub : Arc c r i 0 ⊆ BigArc p r k) :
    Arc c r i n ⊆ BigArc p r (k+n) := by
  intro t ht
  have hsmall := mem_shift_copy (n := (0:ℤ)) ht
  have hlarge := BigArc.shift (n := n) (hsub hsmall)
  have he : t+((0-n:ℤ):ℝ)*period+(n:ℝ)*period = t := by push_cast; ring
  rwa [he] at hlarge

theorem align_big_copies {c : Fin 11 → Point} {r : ℝ} {i j : Fin 9} {p : Point}
    {m k : ℤ} (hI : Arc c r i 0 ⊆ BigArc p r m) (hJ : Arc c r j 0 ⊆ BigArc p r k) :
    Arc c r i 0 ⊆ BigArc p r m ∧ Arc c r j (m-k) ⊆ BigArc p r m := by
  refine ⟨hI,?_⟩
  have he := shift_subset_big (n := m-k) hJ
  rw [show k+(m-k) = m by omega] at he
  exact he

theorem aligned_shift_range {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) {p : Point} (hp : p ≠ 0)
    {i j : Fin 9} {m n : ℤ}
    (hI : Arc c r i 0 ⊆ BigArc p r m) (hJ : Arc c r j n ⊆ BigArc p r m) :
    n = -1 ∨ n = 0 ∨ n = 1 := by
  have hi := hI (copy_nonempty c r i 0)
  have hj := hJ (copy_nonempty c r j n)
  have hbi := ActualBoundaryCyclicOrder.midpoint_bounds c i
  have hbj := ActualBoundaryCyclicOrder.midpoint_bounds c j
  have hw := big_halfWidth_lt hp (Covers.nonneg hc) hr
  change bigMidpoint p+(m:ℝ)*period-capHalfWidth p (2*r) ≤ arcCenter c i 0 ∧
    arcCenter c i 0 ≤ bigMidpoint p+(m:ℝ)*period+capHalfWidth p (2*r) at hi
  change bigMidpoint p+(m:ℝ)*period-capHalfWidth p (2*r) ≤ arcCenter c j n ∧
    arcCenter c j n ≤ bigMidpoint p+(m:ℝ)*period+capHalfWidth p (2*r) at hj
  simp only [arcCenter,Int.cast_zero,zero_mul,add_zero,period] at hi hj
  by_contra hnot
  have hn : n ≤ -2 ∨ 2 ≤ n := by omega
  rcases hn with hn | hn
  · have hnR : (n:ℝ) ≤ -2 := by exact_mod_cast hn
    nlinarith [hi.1,hi.2,hj.1,hj.2,Real.pi_gt_three]
  · have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    nlinarith [hi.1,hi.2,hj.1,hj.2,Real.pi_gt_three]

end N11Formalization.ActualCapClusterLift
#check @N11Formalization.ActualCapClusterLift.copy_in_one_big_copy
#check @N11Formalization.ActualCapClusterLift.intermediate_copy_in_big
#print axioms N11Formalization.ActualCapClusterLift.copy_in_one_big_copy
