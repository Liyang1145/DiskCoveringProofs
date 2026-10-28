import N11Formalization.DSHTenBoundaryEval

/-!
# DSH-TOPO-C1 — reduction of `PerDiskArcBound` to a three-parameter inequality

The per-disk premise of the two-circle capacity argument (`DSHTenBoundaryMain.PerDiskArcBound`)
is an integral statement over two test circles with arbitrary centres.  This file proves that it is
**equivalent to a single three-parameter inequality**, in the source's own normalization
(`M10-038-EXCLUSION.md` §1: "整体旋转不影响D，令h=(e,0)"): put the hub at `(e,0)` and the ring
centre at `ρ·(cos φ, sin φ)`; then

* outer circle `∂D`: `∫ 1_{B(c,R)}·W0 = 2·(a0·t + a1 sin t·v + (a2/2) sin 2t·(2v²−1) + (a3/3) sin 3t·(4v³−3v))`
  with `t = arccos((1+ρ²−R²)/(2ρ))`, `v = cos φ`  (`FlashTenBoundaryArcCases.arc_integral_interval`);
* hub circle `S(h,R)`: the disk `B(c,R)` cut against the test circle centred at the hub with the
  *same* radius `R` — `FlashTenBoundaryCoord.arc_integral_circle_vform` gives the same shape in
  `β = arccos(ℓ/(2R))`, `γ = (ρv − e)/ℓ`, `ℓ = ‖c − h‖`, when `ℓ < 2R`, and
  `FlashTenBoundaryCoord.arc_integral_circle_vform_empty` gives `0` when `2R < ℓ`.

Both closed forms are already in the tree; this file only *instantiates* them at the normalized
parameters (the "v-形" bridges `cos kψ ↔` Chebyshev are part of the cited theorems).

**Scope label: module/standalone.** Not root-integrated.
-/

set_option autoImplicit false
noncomputable section

namespace N11Formalization

open scoped Interval
open MeasureTheory

/-- Hub point of the normalized frame: `h = (e, 0)` with `e = ‖h‖`. -/
def hubPt (e : ℝ) : Point := !₂[e, 0]

/-- Ring centre of the normalized frame: `c = ρ·(cos φ, sin φ)`. -/
def ringPt (ρ φ : ℝ) : Point := !₂[ρ * Real.cos φ, ρ * Real.sin φ]

/-- `ℓ = ‖c − h‖` in the normalized frame: the cancellation-free form `ρ² + e² − 2ρev`. -/
def ellOf (ρ e v : ℝ) : ℝ := Real.sqrt (ρ ^ 2 + e ^ 2 - 2 * ρ * e * v)

/-- `γ = cos ψ`, the cosine of the hub-relative angle. -/
def gammaOf (ρ e v ℓ : ℝ) : ℝ := (ρ * v - e) / ℓ

/-- The **outer** half-quantity `A(W0, t, v)`. -/
def outerHalf (W : TrigDensity) (t v : ℝ) : ℝ :=
  W.a0 * t + W.a1 * Real.sin t * v + W.a2 * Real.sin (2 * t) * (2 * v ^ 2 - 1) / 2
    + W.a3 * Real.sin (3 * t) * (4 * v ^ 3 - 3 * v) / 3

/-- The **inner** half-quantity at half-width `β` and relative cosine `γ` (the hub circle). -/
def innerHalf (W : TrigDensity) (β γ : ℝ) : ℝ :=
  W.a0 * β + W.a1 * Real.sin β * γ + W.a2 * Real.sin (2 * β) * (2 * γ ^ 2 - 1) / 2
    + W.a3 * Real.sin (3 * β) * (4 * γ ^ 3 - 3 * γ) / 3

/-- `hubPt e = e • angPt 0`. -/
theorem hubPt_eq_smul (e : ℝ) : hubPt e = e • angPt 0 := by
  ext i
  fin_cases i <;> simp [hubPt, angPt]

/-- `ringPt ρ φ = ρ • angPt φ`. -/
theorem ringPt_eq_smul (ρ φ : ℝ) : ringPt ρ φ = ρ • angPt φ := by
  ext i
  fin_cases i <;> simp [ringPt, angPt]

/-- `‖hubPt e‖ = |e|`. -/
theorem norm_hubPt (e : ℝ) : ‖hubPt e‖ = |e| := by
  rw [hubPt_eq_smul, norm_smul, norm_angPt, mul_one, Real.norm_eq_abs]

/-- `‖ringPt ρ φ‖ = |ρ|`. -/
theorem norm_ringPt (ρ φ : ℝ) : ‖ringPt ρ φ‖ = |ρ| := by
  rw [ringPt_eq_smul, norm_smul, norm_angPt, mul_one, Real.norm_eq_abs]

/-- `ringPt ρ φ − hubPt e` has coordinates `(ρ cos φ − e, ρ sin φ)`. -/
theorem ringPt_sub_hubPt (ρ e φ : ℝ) :
    ringPt ρ φ - hubPt e = !₂[ρ * Real.cos φ - e, ρ * Real.sin φ] := by
  ext i
  fin_cases i <;> simp [ringPt, hubPt]

/-- **Inner arc integral, active branch** (`ℓ ≤ 2R`, so `arccos(ℓ/(2R))` is defined): the arc
integral of the disk `B(c,R)` on the hub circle `S(h,R)` equals `2·innerHalf W β γ` with
`β = arccos(ℓ/(2R))`, `γ = (c−h)₀/ℓ`, `ℓ = ‖c − h‖`.

The hypothesis `hcos` is exactly `cos β = ℓ/(2R)` for the normalized pair; the reduction layer
discharges it with `β := Real.arccos (ellOf ρ e v / (2 * R))`. -/
theorem inner_integral_active (W : TrigDensity) {ρ e φ t : ℝ} (hρ : 0 < ρ)
    (hne : ringPt ρ φ - hubPt e ≠ 0)
    (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi)
    (hcos : Real.cos t = ‖ringPt ρ φ - hubPt e‖ / (2 * (19 / 50 : ℝ))) :
    (∫ θ in (0)..(2 * Real.pi),
        (if dist (hubPt e + (19 / 50 : ℝ) • angPt θ) (ringPt ρ φ) ≤ (19 / 50 : ℝ)
          then W.toFun θ else 0))
      = 2 * innerHalf W t ((ringPt ρ φ - hubPt e) 0 / ‖ringPt ρ φ - hubPt e‖) := by
  have hq : (0 : ℝ) < 19 / 50 := by norm_num
  set w : Point := (19 / 50 : ℝ)⁻¹ • (ringPt ρ φ - hubPt e) with hwdef
  have hw : w ≠ 0 := by
    intro h0
    exact hne (smul_eq_zero.mp h0 |>.resolve_left (inv_ne_zero (ne_of_gt hq)))
  have hnorm : ‖w‖ = (19 / 50 : ℝ)⁻¹ * ‖ringPt ρ φ - hubPt e‖ := by
    rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq)]
  have hratio : w 0 / ‖w‖ = (ringPt ρ φ - hubPt e) 0 / ‖ringPt ρ φ - hubPt e‖ := by
    rw [hwdef, PiLp.smul_apply, smul_eq_mul, hnorm]
    field_simp
  have hcos' : Real.cos t = (1 + ‖w‖ ^ 2 - ((19 / 50 : ℝ) / (19 / 50 : ℝ)) ^ 2) / (2 * ‖w‖) := by
    have h1 : (19 / 50 : ℝ) / (19 / 50 : ℝ) = 1 := div_self (ne_of_gt hq)
    rw [h1]
    have h2 : ‖w‖ = ‖ringPt ρ φ - hubPt e‖ / (19 / 50 : ℝ) := by
      rw [hnorm]; field_simp
    rw [h2]
    have h3 : ‖ringPt ρ φ - hubPt e‖ / (19 / 50 : ℝ) ≠ 0 :=
      div_ne_zero (norm_ne_zero_iff.mpr hne) (ne_of_gt hq)
    rw [hcos]
    field_simp
    ring
  have key := arc_integral_circle_vform W (hubPt e) hq hw (r := 19 / 50) (t := t)
    (by norm_num) ht0 htπ hcos'
  have hwit : hubPt e + (19 / 50 : ℝ) • w = ringPt ρ φ := by
    rw [hwdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hq), one_smul, add_sub_cancel]
  rw [hwit] at key
  rw [key, hratio]
  rw [innerHalf]

/-- **Inner arc integral, empty branch** (`2R < ℓ`): the hub circle misses the disk `B(c,R)`, so the
arc integral vanishes. -/
theorem inner_integral_empty (W : TrigDensity) {ρ e φ : ℝ} (hρ : 0 < ρ)
    (hne : ringPt ρ φ - hubPt e ≠ 0)
    (hell : (19 / 50 : ℝ) * 2 < ‖ringPt ρ φ - hubPt e‖) :
    (∫ θ in (0)..(2 * Real.pi),
        (if dist (hubPt e + (19 / 50 : ℝ) • angPt θ) (ringPt ρ φ) ≤ (19 / 50 : ℝ)
          then W.toFun θ else 0)) = 0 := by
  have hq : (0 : ℝ) < 19 / 50 := by norm_num
  set w : Point := (19 / 50 : ℝ)⁻¹ • (ringPt ρ φ - hubPt e) with hwdef
  have hw : w ≠ 0 := by
    intro h0
    exact hne (smul_eq_zero.mp h0 |>.resolve_left (inv_ne_zero (ne_of_gt hq)))
  have hnorm : ‖w‖ = (19 / 50 : ℝ)⁻¹ * ‖ringPt ρ φ - hubPt e‖ := by
    rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq)]
  have h2 : 2 < ‖w‖ := by
    rw [hnorm]
    have h50 : (19 / 50 : ℝ)⁻¹ = 50 / 19 := by norm_num
    rw [h50]
    nlinarith
  have h3 : (19 / 50 : ℝ) < (‖w‖ - 1) * (19 / 50 : ℝ) := by
    have : (1 : ℝ) < ‖w‖ - 1 := by linarith
    nlinarith
  have key := arc_integral_circle_vform_empty W (hubPt e) (q := 19 / 50) hq
    (w := w) h2 (r := 19 / 50) h3
  have hwit : hubPt e + (19 / 50 : ℝ) • w = ringPt ρ φ := by
    rw [hwdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hq), one_smul, add_sub_cancel]
  rw [hwit] at key
  exact key

end N11Formalization

end

#print axioms N11Formalization.norm_hubPt
#print axioms N11Formalization.norm_ringPt
#print axioms N11Formalization.inner_integral_active
#print axioms N11Formalization.inner_integral_empty
#check @N11Formalization.inner_integral_active
#check @N11Formalization.inner_integral_empty
#check @N11Formalization.outerHalf
#check @N11Formalization.innerHalf
#check @N11Formalization.ellOf
#check @N11Formalization.gammaOf
