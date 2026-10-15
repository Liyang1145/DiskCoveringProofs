import N11Formalization.DSHTenBoundaryAcos
import N11Formalization.FlashTenBoundaryCoord

/-!
# DSH-TOPO-C1 — route (a) evaluator bricks

Bricks for discharging `C450PerDiskObligation` (`DSHTenBoundaryData.lean`).  The design (NOTES §10)
reduces each segment to a **one-dimensional** certificate over `ρ = ‖c‖ ∈ [1−R, 1+R]`, using the
*existing* arc-integral closed forms plus rational enclosures, instead of the source's
three-dimensional box tree:

* outer circle: `FlashTenBoundaryArcCases.arc_integral_interval` gives
  `∫_{∂D} 1_{B(c,R)}·W = 2(W.a0·t + W.a1 sin t cos φ + W.a2 sin(2t)cos(2φ)/2 + W.a3 sin(3t)cos(3φ)/3)`
  with `cos t = (1+ρ²−R²)/(2ρ)`;
* hub circle: `FlashTenBoundaryCoord.arc_integral_circle_vform` gives the same shape with `β`,
  `cos β = ℓ/(2R)`, `ℓ = |c − hub|`, and `FlashTenBoundaryCoord.arc_integral_circle_vform_empty`
  gives `0` when `ℓ > 2R`;
* the two free parameters `t` and `β` are bounded by rationals via **antitonicity of `cos`**
  (no monotonicity of `arccos` needed), with the rational brackets of `DSHTenBoundaryAcos.lean`.

Bricks proved here:

1. `z_ge_global` — `z(ρ) = (1+ρ²−R²)/(2ρ) ≥ 9249/10000` for all `ρ > 0` (AM-GM: `z ≥ √(1−R²)`;
   the quadratic `10000ρ² − 18498ρ + 8556` has negative discriminant).  Global, no interval needed.
2. `z_antitone_on` / `z_monotone_on` — the exact factorization
   `z(ρ) − z(ρ') = (ρ−ρ')(ρρ' − (1−R²))/(2ρρ')`, so `z` is antitone while `ρρ' ≤ 1−R²` and
   monotone after.  This is what gives *per-interval* lower bounds for `z`, hence for `t`.
3. `le_of_cos_eq_bracket` — if `cos t = z`, `t ≤ π`, `T ≥ 0` and `cosHiNLag T ≤ z` then `t ≤ T`
   (the reusable "bracket ⇒ bound" step, used for `t` and for `β`).
4. `Tglobal` — a rational `T` with `cosHiNLag T ≤ 9249/10000` (kernel-checked), hence
   `t ≤ Tglobal` for every admissible `ρ`.
5. `outer_integral_le` — **first end-to-end brick**: for a weight with vanishing harmonics
   (`W.a1 = W.a2 = W.a3 = 0`, which is the case for the first five segments of `c450Segs`),
   `∫_{∂D} 1_{B(c,R)}·W ≤ 2·W.a0·Tglobal` for every `c` with `‖c‖ ∈ [1−R, 1+R]`.

**Scope label: module/standalone.** Not root-integrated.
-/

set_option autoImplicit false
noncomputable section

namespace N11Formalization

open scoped Interval
open MeasureTheory

/-! ## 1. The rational quantity `z(ρ)` and its global lower bound -/

/-- `z(ρ) = (1 + ρ² − R²)/(2ρ)`: the cosine of the outer arc half-width. -/
def zOf (ρ : ℝ) : ℝ := (1 + ρ ^ 2 - (19 / 50 : ℝ) ^ 2) / (2 * ρ)

/-- **Global lower bound.**  `z(ρ) ≥ 9249/10000` for every `ρ > 0` (so `t ≤ arccos(9249/10000)`
for *every* admissible centre, without any interval analysis). -/
theorem z_ge_global {ρ : ℝ} (hρ : 0 < ρ) : (9249 : ℝ) / 10000 ≤ zOf ρ := by
  have hden : 0 < 2 * ρ := by linarith
  rw [zOf, le_div_iff₀ hden]
  have hsq : 0 ≤ (100 * ρ - 9249 / 100) ^ 2 := sq_nonneg _
  have hR : ((19 : ℝ) / 50) ^ 2 = 361 / 2500 := by norm_num
  nlinarith [hsq, hR]

/-! ## 2. Monotonicity of `z` by exact factorization -/

/-- `z(ρ) − z(ρ') = (ρ−ρ')(ρρ' − (1−R²))/(2ρρ')` for nonzero `ρ, ρ'`. -/
theorem zOf_sub {ρ ρ' : ℝ} (h0 : ρ ≠ 0) (h0' : ρ' ≠ 0) :
    zOf ρ - zOf ρ' = (ρ - ρ') * (ρ * ρ' - (1 - (19 / 50 : ℝ) ^ 2)) / (2 * ρ * ρ') := by
  unfold zOf
  field_simp
  ring

/-- `z` is antitone while `ρρ' ≤ 1 − R²`. -/
theorem z_antitone_on {ρ ρ' : ℝ} (h0 : 0 < ρ) (h0' : 0 < ρ') (hρρ' : ρ ≤ ρ')
    (hprod : ρ * ρ' ≤ 1 - (19 / 50 : ℝ) ^ 2) : zOf ρ' ≤ zOf ρ := by
  have hden : 0 < 2 * ρ * ρ' := by positivity
  have hnum : 0 ≤ (ρ - ρ') * (ρ * ρ' - (1 - (19 / 50 : ℝ) ^ 2)) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hkey : 0 ≤ zOf ρ - zOf ρ' := by
    rw [zOf_sub (ne_of_gt h0) (ne_of_gt h0')]
    exact div_nonneg hnum hden.le
  linarith

/-- `z` is monotone once `ρρ' ≥ 1 − R²`. -/
theorem z_monotone_on {ρ ρ' : ℝ} (h0 : 0 < ρ) (h0' : 0 < ρ') (hρρ' : ρ ≤ ρ')
    (hprod : 1 - (19 / 50 : ℝ) ^ 2 ≤ ρ * ρ') : zOf ρ ≤ zOf ρ' := by
  have hden : 0 < 2 * ρ * ρ' := by positivity
  have hnum : (ρ - ρ') * (ρ * ρ' - (1 - (19 / 50 : ℝ) ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hkey : zOf ρ - zOf ρ' ≤ 0 := by
    rw [zOf_sub (ne_of_gt h0) (ne_of_gt h0')]
    exact div_nonpos_of_nonpos_of_nonneg hnum hden.le
  linarith

/-! ## 3. Bracket ⇒ bound (the reusable antitonicity step, used for `t` and for `β`) -/

/-- If `cos t = z`, `t ≤ π`, `q ≥ 0`, and the rational upper bracket of `cos` at `q` is below `z`,
then `t ≤ q`.  (`cos` is strictly antitone on `[0,π]`.)  The bracket argument is a `ℚ`, matching
the project's `cosHiNLag` interface. -/
theorem le_of_cos_eq_bracket {t z : ℝ} {q : ℚ} (hq0 : 0 ≤ (q : ℝ)) (htπ : t ≤ Real.pi)
    (hcos : Real.cos t = z) (h : ((cosHiNLag q : ℚ) : ℝ) ≤ z) : t ≤ (q : ℝ) := by
  by_contra hcon
  push Not at hcon
  have hstrict := Real.cos_lt_cos_of_nonneg_of_le_pi hq0 htπ hcon
  rw [hcos] at hstrict
  have h2 : Real.cos (q : ℝ) ≤ ((cosHiNLag q : ℚ) : ℝ) := cos_le_cosHiNLag q
  linarith

/-! ## 4. The global half-width bound `t ≤ Tglobal` -/

/-- The global rational upper bound for the outer half-width.  (True max is `arcsin R ≈ 0.389789`;
`0.3905` keeps `cos T ≤ 9249/10000` with margin `≈ 1e-4`.) -/
def Tglobal : ℚ := 3905 / 10000

/-- Kernel check: `cos Tglobal ≤ 9249/10000`. -/
theorem cosHiNLag_Tglobal : cosHiNLag Tglobal ≤ 9249 / 10000 := by
  norm_num [Tglobal, cosHiNLag, cosTQ, Finset.sum_range_succ]

/-- **`t ≤ Tglobal` for every admissible centre.** -/
theorem t_le_global {ρ t : ℝ} (hρ : 0 < ρ) (htπ : t ≤ Real.pi)
    (hcos : Real.cos t = zOf ρ) : t ≤ (Tglobal : ℝ) := by
  have hq0 : (0 : ℝ) ≤ (Tglobal : ℝ) := by
    have : (0 : ℚ) ≤ Tglobal := by norm_num [Tglobal]
    exact_mod_cast this
  have hz := z_ge_global hρ
  have hb : ((cosHiNLag Tglobal : ℚ) : ℝ) ≤ zOf ρ := by
    have h1 : ((cosHiNLag Tglobal : ℚ) : ℝ) ≤ ((9249 : ℚ) / 10000 : ℝ) := by
      exact_mod_cast cosHiNLag_Tglobal
    have h2 : ((9249 : ℚ) / 10000 : ℝ) ≤ zOf ρ := by
      have hcast : ((9249 : ℚ) / 10000 : ℝ) = (9249 : ℝ) / 10000 := by norm_num
      rw [hcast]; exact hz
    linarith
  exact le_of_cos_eq_bracket hq0 htπ hcos hb

/-! ## 5. First end-to-end brick: the outer arc integral for a harmonic-free weight -/

/-- **Outer integral bound.**  For a weight whose harmonics vanish (`a1 = a2 = a3 = 0`), the arc
integral of the disk `B(c,R)` over the unit circle is at most `2·W.a0·Tglobal`, uniformly over all
centres with `‖c‖ ∈ [1−R, 1+R]`. -/
theorem outer_integral_le (W : TrigDensity) (h1 : W.a1 = 0) (h2 : W.a2 = 0) (h3 : W.a3 = 0)
    {c : Point} (hlo : 1 - 19 / 50 ≤ ‖c‖) (hhi : ‖c‖ ≤ 1 + 19 / 50) :
    (∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) c ≤ (19 / 50 : ℝ) then W.toFun θ else 0))
      ≤ 2 * (W.a0 * (Tglobal : ℝ)) := by
  have hρ : 0 < ‖c‖ := by linarith
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hρ
    exact lt_irrefl 0 hρ
  obtain ⟨φ, hcosφ, hsinφ⟩ := exists_angle_of_point c hcne
  have hwit : (!₂[‖c‖ * Real.cos φ, ‖c‖ * Real.sin φ] : Point) = c :=
    eq_ofLp_of_angle hcne rfl hcosφ hsinφ
  -- `t := arccos (zOf ‖c‖)`
  set t : ℝ := Real.arccos (zOf ‖c‖) with ht
  have ht0 : 0 ≤ t := Real.arccos_nonneg _
  have htπ : t ≤ Real.pi := Real.arccos_le_pi _
  have hz1 : zOf ‖c‖ ≤ 1 := by
    rw [zOf, div_le_one (by linarith : (0 : ℝ) < 2 * ‖c‖)]
    have hR : ((19 : ℝ) / 50) ^ 2 = 361 / 2500 := by norm_num
    nlinarith [hlo, hR]
  have hzm1 : -1 ≤ zOf ‖c‖ := by
    have := z_ge_global hρ
    linarith
  have hcost : Real.cos t = zOf ‖c‖ := Real.cos_arccos hzm1 hz1
  have htT : t ≤ (Tglobal : ℝ) := t_le_global hρ htπ hcost
  have ha0 : 0 ≤ W.a0 := by
    have := W.hnonneg
    rw [h1, h2, h3] at this
    simpa using this
  rw [← hwit]
  rw [arc_integral_interval W hρ (by norm_num : (0 : ℝ) ≤ 19 / 50) ht0 htπ hcost]
  rw [h1, h2, h3]
  nlinarith [htT, ha0]

end N11Formalization

end

#print axioms N11Formalization.z_ge_global
#print axioms N11Formalization.z_antitone_on
#print axioms N11Formalization.z_monotone_on
#print axioms N11Formalization.le_of_cos_eq_bracket
#print axioms N11Formalization.cosHiNLag_Tglobal
#print axioms N11Formalization.t_le_global
#print axioms N11Formalization.outer_integral_le
#check @N11Formalization.outer_integral_le
#check @N11Formalization.t_le_global