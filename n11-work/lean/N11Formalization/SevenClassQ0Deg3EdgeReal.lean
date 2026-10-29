import N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal
import N11Formalization.SevenClassQ0Deg3Cos

/-! Lane A: real derivative form of the q0 degree-three edge bracket.

The finite table uses `edgeUpper b q`.  This module identifies its cast with
the real function `A * sinHiReal q - b*q` and computes the derivative as
`A * cosHiReal q - b`.  Consequently a pointwise derivative-sign estimate on
an interval yields the corresponding decreasing-suffix obligation. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3EdgeReal

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Cos
open SevenClassQ0Deg3Mono
open SevenClassQ0Deg3UpperReductionUnimodal

/-- Real form of the edge upper bracket. -/
def edgeHiReal (b : ℚ) (x : ℝ) : ℝ :=
  (19 / 50 : ℝ) ^ 2 * sinHiReal x - (b : ℝ) * x

theorem hasDerivAt_edgeHiReal (b : ℚ) (x : ℝ) :
    HasDerivAt (edgeHiReal b) ((19 / 50 : ℝ) ^ 2 * cosHiReal x - (b : ℝ)) x := by
  have h1 := (hasDerivAt_sinHiReal x).const_mul ((19 / 50 : ℝ) ^ 2)
  have h2 := (hasDerivAt_id x).const_mul (b : ℝ)
  simpa only [edgeHiReal, cosHiReal, Pi.sub_apply, id_eq] using h1.sub h2

theorem edgeUpper_cast_eq (b q : ℚ) (hq : 0 ≤ q) :
    ((edgeUpper b q : ℚ) : ℝ) = edgeHiReal b q := by
  unfold edgeUpper edgeHiReal sinHiReal
  rw [sinHiNLag_cast]
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rw [abs_of_nonneg hqR]
  push_cast
  ring

/-- A pointwise nonpositive derivative estimate gives a decreasing suffix. -/
theorem edgeHiReal_antitoneOn_of_deriv_nonpos (b : ℚ) {s t : ℝ}
    (hderiv : ∀ x ∈ Set.Ioc s t,
      (19 / 50 : ℝ) ^ 2 * cosHiReal x - (b : ℝ) ≤ 0) :
    AntitoneOn (edgeHiReal b) (Set.Icc s t) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc s t) ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_edgeHiReal b x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_edgeHiReal b x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_edgeHiReal b x).deriv]
    exact hderiv x ⟨hx.1.le, hx.2⟩

/-- A decreasing real edge bracket and a zero peak discharge the corresponding
finite decreasing-suffix obligation. -/
theorem edgeDecFrom_of_antitoneOn (i : Fin 21) (hw : edgeWitness i = 0)
    (hanti : AntitoneOn (edgeHiReal (edgeCoeff i))
      (Set.Icc 0 (RatInterval.piHi : ℝ))) : EdgeDecFrom i := by
  intro k hk
  have hq0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 k := by
    unfold nodeQ
    positivity
  have hq0R : (0 : ℝ) ≤ (nodeQ RatInterval.piHi 2048 k : ℚ) := by
    exact_mod_cast hq0
  have hqhi : (nodeQ RatInterval.piHi 2048 k : ℚ) ≤ RatInterval.piHi := by
    unfold nodeQ
    have hkR : (k.val : ℝ) ≤ 2048 := by exact_mod_cast k.isLt
    have hp : (0 : ℝ) ≤ (RatInterval.piHi : ℝ) := by norm_num [RatInterval.piHi]
    have hqR : ((nodeQ RatInterval.piHi 2048 k : ℚ) : ℝ) ≤ (RatInterval.piHi : ℝ) := by
      unfold nodeQ
      push_cast
      nlinarith
    exact_mod_cast hqR
  have hqhiR : (nodeQ RatInterval.piHi 2048 k : ℚ) ≤ (RatInterval.piHi : ℚ) := hqhi
  have hpi0 : (0 : ℝ) ≤ (RatInterval.piHi : ℝ) := by norm_num [RatInterval.piHi]
  have hanti' : edgeHiReal (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) ≤
      edgeHiReal (edgeCoeff i) 0 := by
    exact hanti ⟨le_rfl, hpi0⟩ ⟨hq0R, by exact_mod_cast hqhiR⟩ hq0R
  apply Rat.cast_le.mp
  rw [edgeUpper_cast_eq (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) hq0]
  rw [hw]
  rw [edgeUpper_cast_eq (edgeCoeff i) 0 (le_refl 0)]
  simpa only [nodeQ, Nat.cast_zero, mul_zero, zero_div] using hanti'

end N11Formalization.SevenClassQ0Deg3EdgeReal
#check @N11Formalization.SevenClassQ0Deg3EdgeReal.hasDerivAt_edgeHiReal
#check @N11Formalization.SevenClassQ0Deg3EdgeReal.edgeDecFrom_of_antitoneOn
#print axioms N11Formalization.SevenClassQ0Deg3EdgeReal.edgeDecFrom_of_antitoneOn
