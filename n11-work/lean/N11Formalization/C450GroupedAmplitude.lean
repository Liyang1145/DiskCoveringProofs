import N11Formalization.C450GroupedGeometry

/-! Exact rational ranges and signed harmonic amplitude soundness.
No actual source packet validity/coverage is assumed paid by this module. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedAmplitude
open C450OuterGeometry C450PolynomialRanges C450QuadraticBounds C450GroupedAnalytic

def p2Q (x : ℚ) : ℚ := 2*x^2-1
def p3Q (x : ℚ) : ℚ := 4*x^3-3*x

theorem p2Q_cast (x : ℚ) : (p2Q x:ℝ) = P2 (x:ℝ) := by simp [p2Q,P2]
theorem p3Q_cast (x : ℚ) : (p3Q x:ℝ) = P3 (x:ℝ) := by simp [p3Q,P3]

def lower2Q (lo hi : ℚ) : ℚ := p2Q (min hi (max lo 0))
def upper2Q (lo hi : ℚ) : ℚ := max (p2Q lo) (p2Q hi)
def lower3Q (lo hi : ℚ) : ℚ :=
  if lo ≤ 1/2 ∧ 1/2 ≤ hi then -1 else min (p3Q lo) (p3Q hi)
def upper3Q (lo hi : ℚ) : ℚ :=
  if lo ≤ -1/2 ∧ -1/2 ≤ hi then 1 else max (p3Q lo) (p3Q hi)

theorem lower2Q_cast (lo hi : ℚ) :
    (lower2Q lo hi:ℝ) = lower2 (lo:ℝ) (hi:ℝ) := by
  simp [lower2Q,lower2,vertex,p2Q,P2,Rat.cast_min,Rat.cast_max]

theorem upper2Q_cast (lo hi : ℚ) :
    (upper2Q lo hi:ℝ) = upper2 (lo:ℝ) (hi:ℝ) := by
  simp only [upper2Q,upper2,Rat.cast_max,p2Q_cast]

theorem lower3Q_cast (lo hi : ℚ) :
    (lower3Q lo hi:ℝ) = lower3 (lo:ℝ) (hi:ℝ) := by
  unfold lower3Q lower3
  have hhalf : ((1/2:ℚ):ℝ) = (1/2:ℝ) := by norm_num
  by_cases h : lo ≤ 1/2 ∧ 1/2 ≤ hi
  · have hr : (lo:ℝ) ≤ 1/2 ∧ 1/2 ≤ (hi:ℝ) := by
      rw [← hhalf]
      exact ⟨Rat.cast_le.mpr h.1,Rat.cast_le.mpr h.2⟩
    rw [if_pos h,if_pos hr]
    norm_num
  · have hr : ¬ ((lo:ℝ) ≤ 1/2 ∧ 1/2 ≤ (hi:ℝ)) := by
      rw [← hhalf]
      intro hh
      exact h ⟨Rat.cast_le.mp hh.1,Rat.cast_le.mp hh.2⟩
    rw [if_neg h,if_neg hr]
    simp only [Rat.cast_min,p3Q_cast]

theorem upper3Q_cast (lo hi : ℚ) :
    (upper3Q lo hi:ℝ) = upper3 (lo:ℝ) (hi:ℝ) := by
  unfold upper3Q upper3
  by_cases h : lo ≤ -1/2 ∧ -1/2 ≤ hi
  · have hr : (lo:ℝ) ≤ -1/2 ∧ -1/2 ≤ (hi:ℝ) := by exact_mod_cast h
    rw [if_pos h,if_pos hr]
    norm_num
  · have hr : ¬ ((lo:ℝ) ≤ -1/2 ∧ -1/2 ≤ (hi:ℝ)) := by exact_mod_cast h
    rw [if_neg h,if_neg hr]
    simp only [Rat.cast_max,p3Q_cast]

def range2Q (I : RatInterval) : RatInterval := ⟨lower2Q I.lo I.hi,upper2Q I.lo I.hi⟩
def range3Q (I : RatInterval) : RatInterval := ⟨lower3Q I.lo I.hi,upper3Q I.lo I.hi⟩

theorem range2_mem (I : RatInterval) {x : ℝ} (hx : RatInterval.Mem I x) :
    RatInterval.Mem (range2Q I) (P2 x) := by
  have hh := range2 (RatInterval.mem_lo_le hx) (RatInterval.mem_le_hi hx)
  change (lower2Q I.lo I.hi:ℝ) ≤ P2 x ∧ P2 x ≤ (upper2Q I.lo I.hi:ℝ)
  rw [lower2Q_cast,upper2Q_cast]
  exact hh

theorem range3_mem (I : RatInterval) {x : ℝ}
    (hlo : -1 ≤ I.lo) (hhi : I.hi ≤ 1) (hx : RatInterval.Mem I x) :
    RatInterval.Mem (range3Q I) (P3 x) := by
  have hl : (-1:ℝ) ≤ (I.lo:ℝ) := by exact_mod_cast hlo
  have hu : (I.hi:ℝ) ≤ (1:ℝ) := by exact_mod_cast hhi
  have hh := range3 hl hu (RatInterval.mem_lo_le hx) (RatInterval.mem_le_hi hx)
  change (lower3Q I.lo I.hi:ℝ) ≤ P3 x ∧ P3 x ≤ (upper3Q I.lo I.hi:ℝ)
  rw [lower3Q_cast,upper3Q_cast]
  exact hh

/-- The legal z/cos-beta intervals are nonnegative. Unlike generic interval
self-multiplication, this retains the exact endpoint square ranges. -/
def squareThird (I : RatInterval) : RatInterval :=
  ⟨(4*I.lo^2-1)/3,(4*I.hi^2-1)/3⟩

theorem squareThird_mem (I : RatInterval) {z : ℝ}
    (hl : 0 ≤ I.lo) (hz : RatInterval.Mem I z) :
    RatInterval.Mem (squareThird I) ((4*z^2-1)/3) := by
  have hln : (0:ℝ) ≤ (I.lo:ℝ) := by exact_mod_cast hl
  have hz0 := RatInterval.mem_lo_le hz
  have hz1 := RatInterval.mem_le_hi hz
  have hs0 : (I.lo:ℝ)^2 ≤ z^2 := by nlinarith
  have hs1 : z^2 ≤ (I.hi:ℝ)^2 := by nlinarith
  change (((4*I.lo^2-1)/3:ℚ):ℝ) ≤ (4*z^2-1)/3 ∧
    (4*z^2-1)/3 ≤ (((4*I.hi^2-1)/3:ℚ):ℝ)
  push_cast
  constructor <;> linarith

def amplitudeInterval (a1 a2 a3 : ℚ) (Z V : RatInterval) : RatInterval :=
  (((RatInterval.ofRat a1).mul V).add
    ((RatInterval.ofRat a2).mul (Z.mul (range2Q V)))).add
    ((RatInterval.ofRat a3).mul ((squareThird Z).mul (range3Q V)))

theorem amplitude_mem (a1 a2 a3 : ℚ) (Z V : RatInterval) {z v : ℝ}
    (hz0 : 0 ≤ Z.lo) (hv0 : -1 ≤ V.lo) (hv1 : V.hi ≤ 1)
    (hz : RatInterval.Mem Z z) (hv : RatInterval.Mem V v) :
    RatInterval.Mem (amplitudeInterval a1 a2 a3 Z V)
      ((a1:ℝ)*v+(a2:ℝ)*z*P2 v+(a3:ℝ)*(4*z^2-1)*P3 v/3) := by
  have h1 := RatInterval.mul_mem (RatInterval.ofRat_mem a1) hv
  have h2 := RatInterval.mul_mem (RatInterval.ofRat_mem a2)
    (RatInterval.mul_mem hz (range2_mem V hv))
  have h3 := RatInterval.mul_mem (RatInterval.ofRat_mem a3)
    (RatInterval.mul_mem (squareThird_mem Z hz0 hz) (range3_mem V hv0 hv1 hv))
  have hh := RatInterval.add_mem (RatInterval.add_mem h1 h2) h3
  have hid : (a1:ℝ)*v+(a2:ℝ)*(z*P2 v)+(a3:ℝ)*(((4*z^2-1)/3)*P3 v) =
      (a1:ℝ)*v+(a2:ℝ)*z*P2 v+(a3:ℝ)*(4*z^2-1)*P3 v/3 := by ring
  rw [hid] at hh
  exact hh

theorem actual_amplitude_le (W : TrigDensity) (a1 a2 a3 p : ℚ)
    (Z V : RatInterval) {z v : ℝ}
    (h1 : W.a1 = (a1:ℝ)) (h2 : W.a2 = (a2:ℝ)) (h3 : W.a3 = (a3:ℝ))
    (hz0 : 0 ≤ Z.lo) (hv0 : -1 ≤ V.lo) (hv1 : V.hi ≤ 1)
    (hz : RatInterval.Mem Z z) (hv : RatInterval.Mem V v)
    (hp : (amplitudeInterval a1 a2 a3 Z V).hi ≤ p) :
    amplitude W z v ≤ (p:ℝ) := by
  have hh := RatInterval.mem_le_hi (amplitude_mem a1 a2 a3 Z V hz0 hv0 hv1 hz hv)
  unfold amplitude
  rw [h1,h2,h3]
  exact hh.trans ((Rat.cast_le (K := ℝ)).mpr hp)

def arcUpper (a p t : ℚ) : ℚ := a*t+sineProductUpper p t

theorem arc_upper (a p t : ℚ) : arc (a:ℝ) (p:ℝ) (t:ℝ) ≤ (arcUpper a p t:ℝ) := by
  have hh := add_le_add (le_refl ((a:ℝ)*(t:ℝ))) (sine_product_upper p t)
  simpa only [arc,arcUpper,Rat.cast_add,Rat.cast_mul] using hh

end N11Formalization.C450GroupedAmplitude
#check @N11Formalization.C450GroupedAmplitude.amplitude_mem
#check @N11Formalization.C450GroupedAmplitude.actual_amplitude_le
#print axioms N11Formalization.C450GroupedAmplitude.range2_mem
#print axioms N11Formalization.C450GroupedAmplitude.range3_mem
#print axioms N11Formalization.C450GroupedAmplitude.squareThird_mem
#print axioms N11Formalization.C450GroupedAmplitude.amplitude_mem
#print axioms N11Formalization.C450GroupedAmplitude.actual_amplitude_le
#print axioms N11Formalization.C450GroupedAmplitude.arc_upper
