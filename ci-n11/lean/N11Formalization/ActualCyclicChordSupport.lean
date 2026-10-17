import N11Formalization.ActualBoundaryArcFrame

/-! Exact strict support for consecutive sites of a finite angularly ordered
circle. Empty arcs may have width greater thanpi; the wrap is handled by an
actual2pi lift. No convex-position assumption or approximate angle test. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCyclicChordSupport

def nextAngle {m : ℕ} (theta : Fin (m+1) → ℝ) (i : Fin (m+1)) : ℝ :=
  theta (finRotate (m+1) i) + if i = Fin.last m then 2*Real.pi else 0

theorem nextAngle_circleMap {m : ℕ} (theta : Fin (m+1) → ℝ) (i : Fin (m+1)) :
    circleMap (nextAngle theta i) = circleMap (theta (finRotate (m+1) i)) := by
  unfold nextAngle
  split_ifs
  · exact circleMap_add_two_pi _
  · rw [add_zero]

theorem gap_bounds {m : ℕ} (hm : 0 < m) (theta : Fin (m+1) → ℝ)
    (hs : StrictMono theta) (hb : ∀ i, -Real.pi < theta i ∧ theta i ≤ Real.pi)
    (i : Fin (m+1)) :
    theta i < nextAngle theta i ∧ nextAngle theta i < theta i+2*Real.pi := by
  by_cases hi : i = Fin.last m
  · subst i
    simp only [nextAngle,finRotate_last,ite_true]
    have hs0 : theta 0 < theta (Fin.last m) := hs (by
      change 0 < m
      exact hm)
    have h0 := hb 0
    have hlast := hb (Fin.last m)
    constructor <;> linarith
  · simp only [nextAngle,if_neg hi,add_zero]
    have hsnext := hs ((lt_finRotate_iff_ne_last i).mpr hi)
    have hI := hb i
    have hN := hb (finRotate (m+1) i)
    exact ⟨hsnext,by linarith⟩

/-- Every other site has a lift in the strict complement of the empty arc. -/
theorem complement_lift {m : ℕ} (theta : Fin (m+1) → ℝ)
    (hs : StrictMono theta) (hb : ∀ i, -Real.pi < theta i ∧ theta i ≤ Real.pi)
    (i k : Fin (m+1)) (hki : k ≠ i) (hkn : k ≠ finRotate (m+1) i) :
    ∃ t : ℝ, circleMap t = circleMap (theta k) ∧
      nextAngle theta i < t ∧ t < theta i+2*Real.pi := by
  by_cases hi : i = Fin.last m
  · subst i
    have hk0 : (0 : Fin (m+1)) < k := by
      have hkne : k ≠ 0 := by simpa only [finRotate_last] using hkn
      change 0 < k.val
      have hval : k.val ≠ 0 := fun h => hkne (Fin.ext h)
      omega
    have hklt : k < Fin.last m := by
      have hkbound := k.isLt
      have hval : k.val ≠ m := fun h => hki (Fin.ext h)
      change k.val < m
      omega
    refine ⟨theta k+2*Real.pi,circleMap_add_two_pi _,?_,?_⟩
    · simp only [nextAngle,finRotate_last,ite_true]
      linarith [hs hk0]
    · linarith [hs hklt]
  · have hnextval := coe_finRotate_of_ne_last hi
    by_cases hklt : k < i
    · refine ⟨theta k+2*Real.pi,circleMap_add_two_pi _,?_,?_⟩
      · simp only [nextAngle,if_neg hi,add_zero]
        have hK := hb k
        have hN := hb (finRotate (m+1) i)
        linarith
      · linarith [hs hklt]
    · have hnlt : finRotate (m+1) i < k := by
        have hval : k.val ≠ (finRotate (m+1) i).val := fun h => hkn (Fin.ext h)
        have hine : k.val ≠ i.val := fun h => hki (Fin.ext h)
        have hnot : ¬ k.val < i.val := hklt
        change (finRotate (m+1) i).val < k.val
        omega
      refine ⟨theta k,rfl,?_,?_⟩
      · simp only [nextAngle,if_neg hi,add_zero]
        exact hs hnlt
      · have hK := hb k
        have hI := hb i
        linarith

theorem cos_strict_complement {alpha x : ℝ}
    (ha0 : 0 < alpha) (hapi : alpha < Real.pi)
    (hax : alpha < x) (hxa : x < 2*Real.pi-alpha) :
    Real.cos x < Real.cos alpha := by
  by_cases hxpi : x ≤ Real.pi
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi ha0.le hxpi hax
  · have hxpi' : Real.pi < x := lt_of_not_ge hxpi
    have hy0 : 0 ≤ 2*Real.pi-x := by linarith
    have hypi : 2*Real.pi-x ≤ Real.pi := by linarith
    have hlay : alpha < 2*Real.pi-x := by linarith
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi ha0.le hypi hlay
    have he : Real.cos (2*Real.pi-x) = Real.cos x := by
      rw [Real.cos_sub,Real.cos_two_pi,Real.sin_two_pi]
      ring
    rwa [he] at hh

theorem empty_arc_support {a b t : ℝ} (hab : a < b)
    (hba : b < a+2*Real.pi) (hbt : b < t) (hta : t < a+2*Real.pi) :
    inner ℝ (circleMap ((a+b)/2)) (circleMap b-circleMap a) = 0 ∧
      inner ℝ (circleMap ((a+b)/2)) (circleMap t-circleMap a) < 0 := by
  have hma : (a+b)/2-a = (b-a)/2 := by ring
  have hmb : (a+b)/2-b = -((b-a)/2) := by ring
  have hmt : (a+b)/2-t = -(t-(a+b)/2) := by ring
  have ha0 : 0 < (b-a)/2 := by linarith
  have hapi : (b-a)/2 < Real.pi := by linarith
  have hax : (b-a)/2 < t-(a+b)/2 := by linarith
  have hxa : t-(a+b)/2 < 2*Real.pi-(b-a)/2 := by linarith
  constructor
  · rw [inner_sub_right,inner_circleMap,inner_circleMap,hma,hmb,Real.cos_neg,sub_self]
  · rw [inner_sub_right,inner_circleMap,inner_circleMap,hma,hmt,Real.cos_neg]
    exact sub_neg.mpr (cos_strict_complement ha0 hapi hax hxa)

theorem ordered_chord_support {m : ℕ} (hm : 0 < m)
    (theta : Fin (m+1) → ℝ) (hs : StrictMono theta)
    (hb : ∀ i, -Real.pi < theta i ∧ theta i ≤ Real.pi) (i : Fin (m+1)) :
    let d := circleMap ((theta i+nextAngle theta i)/2)
    inner ℝ d (circleMap (theta (finRotate (m+1) i))-circleMap (theta i)) = 0 ∧
      ∀ k : Fin (m+1), k ≠ i → k ≠ finRotate (m+1) i →
        inner ℝ d (circleMap (theta k)-circleMap (theta i)) < 0 := by
  dsimp only
  obtain ⟨hab,hba⟩ := gap_bounds hm theta hs hb i
  have horth : inner ℝ (circleMap ((theta i+nextAngle theta i)/2))
      (circleMap (nextAngle theta i)-circleMap (theta i)) = 0 := by
    rw [inner_sub_right,inner_circleMap,inner_circleMap]
    have he : (theta i+nextAngle theta i)/2-nextAngle theta i =
        -((theta i+nextAngle theta i)/2-theta i) := by ring
    rw [he,Real.cos_neg,sub_self]
  refine ⟨by rwa [nextAngle_circleMap] at horth,?_⟩
  intro k hki hkn
  obtain ⟨t,ht,hbt,hta⟩ := complement_lift theta hs hb i k hki hkn
  have hh := (empty_arc_support hab hba hbt hta).2
  rwa [ht] at hh

end N11Formalization.ActualCyclicChordSupport
#check @N11Formalization.ActualCyclicChordSupport.ordered_chord_support
#print axioms N11Formalization.ActualCyclicChordSupport.complement_lift
#print axioms N11Formalization.ActualCyclicChordSupport.ordered_chord_support
