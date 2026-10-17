/-
  G3 first slice, level L5 -- the FIRST complete per-line minorant on recorded data.

  WHAT IS PROVED HERE.  For leaf 4348 of the C921 tree (the leaf with the tightest
  margin, stored - T^2 = 1.64233187582751e-09) and its binding minorant line
  (pair [0, 5], slope 0), the recorded obligation
        for all z in [a,b],  s*z + v  <=  1 - cos z
  is discharged -- with the intercept REPLACED by a rational lower bound `v'`
  recomputed from the root kernel, as required because the recorded intercept is the
  exact minimum (see G3-PLAN.md SS11 E9/E10 and claim C1201).

  THE ROUTE, and why each step is necessary.
   * s = 0 and the shifted interval contains NO critical point (sin t = 0 fails on
     it: it lies strictly inside (-pi/2, 0)), so by L3's exact reduction
         (obligation) <=> (endpoint conditions) AND (critical conditions)
     the critical half is vacuous and the two ENDPOINT conditions suffice.
   * each endpoint condition is an evaluation of cos at an IRRATIONAL point (a + pi).
     It is discharged without arcsin, by four rational steps:
        Real.cos_add_pi        cos z = -cos (z + pi)
        pi brackets            z + pi in [a + piLo, b + piHi]   (rational!)
        Real.abs_cos_sub_cos_le |cos t - cos q| <= |t - q| <= width
        root kernel            cosLoNLag q <= cos q   (N11Formalization)
     giving 1 - cos z >= 1 + cosLoNLag q - width =: v'  ,  purely rational.

  REUSED, NOT RESTATED: L3's `S`, `deriv_S`, `minorant_iff_endpoints_and_critical`
  (in the root cone), and the root kernel `N11Formalization.cosLoNLag_le_cos`.
  This slice adds only the endpoint-case lemma and this one concrete line.

  SCOPE / NEXT.  25184 of the 124130 recorded lines are in this endpoint case; the
  other 98946 have an interior critical point and need the bracket piece
  (unimodality + bisection of sin z = s + L4's s*z <= max(s*x)(s*y)).  This file is
  the first line of the endpoint class, done end to end.

  Discipline: no sorry, no custom axiom, no native_decide, no #eval.
-/
import Mathlib
import N11Formalization.IntervalsHighLag
import N11Formalization.Interval.Taylor19C
import N11Formalization.G3.SliceL3

namespace N11Formalization.G3SliceL5

open N11Formalization.RatInterval (piLo piHi)

/-! ## 1. The endpoint case (general) -/

/-- **If the critical points are exhausted by the endpoints, the endpoints decide.**
Directly from L3's exact reduction: the critical half of the equivalence is the only
thing left over after the two endpoint conditions, so a hypothesis that no critical
point lies strictly inside closes it. -/
theorem minorant_of_no_interior_critical {a b s v : ℝ} (hab : a ≤ b)
    (ha : s * a + v ≤ 1 - Real.cos a) (hb : s * b + v ≤ 1 - Real.cos b)
    (hnc : ∀ z ∈ Set.Icc a b, Real.sin z = s → z = a ∨ z = b) :
    ∀ z ∈ Set.Icc a b, s * z + v ≤ 1 - Real.cos z := by
  refine (N11Formalization.G3SliceL3.minorant_iff_endpoints_and_critical hab).mpr
    ⟨ha, hb, ?_⟩
  intro z hz hsin
  rcases hnc z hz hsin with h | h
  · rw [h]; exact ha
  · rw [h]; exact hb

/-! ## 2. The concrete recorded line: leaf 4348, pair [0, 5] (slope 0) -/

/-- Recorded cell interval of this pair (exact decimal literals from
`cosine_dbm_local920.json`, no hand transcription). -/
def a4348 : ℚ := (-35514359664917871054704081345473016629485657036300966655690225743521047099695851 : ℚ) / (10000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def b4348 : ℚ := (-35485721070021109192682759912063033062754484400754807667441499558621634695578573 : ℚ) / (10000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
/-- The recorded intercept (kept for the comparison below; NOT used as the bound). -/
def v4348recorded : ℚ := (19171832684971432660717738236956326078809538388020541240895034724405837537279783 : ℚ) / (10000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

/-- Rational bracket for the pi-shifted argument `t = z + pi`, using the PROJECT's
20-digit pi brackets (`Trig.lean`): `t in [q4348Lo, q4348Hi]`. -/
def q4348Lo : ℚ := a4348 + piLo
def q4348Hi : ℚ := b4348 + piHi

/-- **The recomputed intercept (SHARP form).**
`v' = 1 + min (cosLoNLag q4348Lo) (cosLoNLag q4348Hi) - (piHi - piLo)`: the kernel
value at the NEAR-SIDE bracket point, minus the *pi-bracket* slack -- NOT the cell
width.  This matters: the first version of this slice used the whole-bracket slack
`q4348Hi - q4348Lo` = the cell width 2.863859e-03, which gates green but leaves a
leaf loss of 3.918e-07, i.e. 239x LARGER than leaf 4348's margin 1.642332e-09, so it
would be useless for the leaf bound.  Each endpoint condition below has its OWN
near-side bracket point, making the slack only `piHi - piLo` = 1e-20; the measured
loss is then 1.105330e-20 and the leaf loss 1.512e-24 -- a factor 1.086e+15 below the
margin (evidence/g3-recon/check_l5_sharp.py).
Purely rational, and a lower bound of the true minimum in both formulations. -/
def v4348 : ℚ :=
  1 + min (N11Formalization.cosLoNLag q4348Lo) (N11Formalization.cosLoNLag q4348Hi)
    - (piHi - piLo)

theorem q4348Lo_mem_window : q4348Lo ∈ Set.Icc (-(39 / 25 : ℚ)) (39 / 25) := by
  unfold q4348Lo a4348 piLo; norm_num

theorem q4348Hi_mem_window : q4348Hi ∈ Set.Icc (-(39 / 25 : ℚ)) (39 / 25) := by
  unfold q4348Hi b4348 piHi; norm_num

theorem q4348Lo_cast : ((q4348Lo : ℚ) : ℝ) = (a4348 : ℝ) + (piLo : ℝ) := by
  unfold q4348Lo; push_cast; ring

theorem q4348Hi_cast : ((q4348Hi : ℚ) : ℝ) = (b4348 : ℝ) + (piHi : ℝ) := by
  unfold q4348Hi; push_cast; ring

theorem a4348_le_b4348 : (a4348 : ℝ) ≤ (b4348 : ℝ) := by
  unfold a4348 b4348; push_cast; norm_num

/-- The project's 20-digit pi brackets, as real inequalities. -/
theorem piLo_le_pi : (piLo : ℝ) ≤ Real.pi :=
  le_of_lt N11Formalization.RatInterval.piLo_lt_pi

theorem pi_le_piHi : Real.pi ≤ (piHi : ℝ) :=
  le_of_lt N11Formalization.RatInterval.pi_lt_piHi

theorem q4348Lo_lt_q4348Hi : q4348Lo < q4348Hi := by
  unfold q4348Lo q4348Hi a4348 b4348 piLo piHi; norm_num

/-- No critical point in the shifted interval: `sin t = 0` fails there because the
bracket sits strictly inside `(-pi/2, 0)`. -/
theorem q4348Hi_lt_zero : q4348Hi < 0 := by
  unfold q4348Hi b4348 piHi; norm_num

/-! ### The two endpoint conditions, each with its own near-side bracket point -/

/-- **Endpoint condition at `a4348`.**  The shifted argument `a + pi` sits within
`pi - piLo` of the rational point `q4348Lo`; the kernel value there minus that slack
is a lower bound of `cos a`. -/
theorem endpoint_a4348 : (0 : ℝ) * (a4348 : ℝ) + (v4348 : ℝ) ≤ 1 - Real.cos (a4348 : ℝ) := by
  have hd : |(a4348 : ℝ) + Real.pi - ((q4348Lo : ℚ) : ℝ)| ≤ (piHi : ℝ) - (piLo : ℝ) := by
    rw [q4348Lo_cast]
    have he : (a4348 : ℝ) + Real.pi - ((a4348 : ℝ) + (piLo : ℝ)) = Real.pi - (piLo : ℝ) :=
      by ring
    rw [he, abs_of_nonneg (by linarith [piLo_le_pi])]
    linarith [pi_le_piHi]
  have hb := le_trans (Real.abs_cos_sub_cos_le ((a4348 : ℝ) + Real.pi) ((q4348Lo : ℚ) : ℝ)) hd
  have hcos : Real.cos (a4348 : ℝ) = -Real.cos ((a4348 : ℝ) + Real.pi) := by
    rw [Real.cos_add_pi]; ring
  have hk := N11Formalization.cosLoNLag_le_cos q4348Lo
  have hmin : ((min (N11Formalization.cosLoNLag q4348Lo) (N11Formalization.cosLoNLag q4348Hi) : ℚ) : ℝ)
      ≤ ((N11Formalization.cosLoNLag q4348Lo : ℚ) : ℝ) :=
    (Rat.cast_le (K := ℝ)).mpr (min_le_left _ _)
  have hv : ((v4348 : ℚ) : ℝ) =
      1 + ((min (N11Formalization.cosLoNLag q4348Lo) (N11Formalization.cosLoNLag q4348Hi) : ℚ) : ℝ)
        - ((piHi : ℝ) - (piLo : ℝ)) := by
    unfold v4348; push_cast; ring
  rw [hcos, hv]
  linarith [(abs_le.mp hb).1]

/-- **Endpoint condition at `b4348`.**  Here the near-side point is `q4348Hi` (the
shifted argument `b + pi` is within `piHi - pi` of it). -/
theorem endpoint_b4348 : (0 : ℝ) * (b4348 : ℝ) + (v4348 : ℝ) ≤ 1 - Real.cos (b4348 : ℝ) := by
  have hd : |(b4348 : ℝ) + Real.pi - ((q4348Hi : ℚ) : ℝ)| ≤ (piHi : ℝ) - (piLo : ℝ) := by
    rw [q4348Hi_cast]
    have he : (b4348 : ℝ) + Real.pi - ((b4348 : ℝ) + (piHi : ℝ)) = Real.pi - (piHi : ℝ) :=
      by ring
    rw [he, abs_of_nonpos (by linarith [pi_le_piHi])]
    linarith [piLo_le_pi]
  have hb := le_trans (Real.abs_cos_sub_cos_le ((b4348 : ℝ) + Real.pi) ((q4348Hi : ℚ) : ℝ)) hd
  have hcos : Real.cos (b4348 : ℝ) = -Real.cos ((b4348 : ℝ) + Real.pi) := by
    rw [Real.cos_add_pi]; ring
  have hk := N11Formalization.cosLoNLag_le_cos q4348Hi
  have hmin : ((min (N11Formalization.cosLoNLag q4348Lo) (N11Formalization.cosLoNLag q4348Hi) : ℚ) : ℝ)
      ≤ ((N11Formalization.cosLoNLag q4348Hi : ℚ) : ℝ) :=
    (Rat.cast_le (K := ℝ)).mpr (min_le_right _ _)
  have hv : ((v4348 : ℚ) : ℝ) =
      1 + ((min (N11Formalization.cosLoNLag q4348Lo) (N11Formalization.cosLoNLag q4348Hi) : ℚ) : ℝ)
        - ((piHi : ℝ) - (piLo : ℝ)) := by
    unfold v4348; push_cast; ring
  rw [hcos, hv]
  linarith [(abs_le.mp hb).1]

/-! ## 3. The obligation for this recorded line -/

/-- **The complete per-line minorant, on recorded data.**  No critical point lies in
`[a4348, b4348]`: the interval sits between `-2pi` and `-pi`, so the shifted point
`z + pi` lies in `(-0.41, -0.40)`, strictly inside `(-pi/2, 0)`, where `sin` is
strictly negative -- while `sin z = 0` would force `sin (z + pi) = 0`. -/
theorem minorant4348 :
    ∀ z ∈ Set.Icc (a4348 : ℝ) (b4348 : ℝ),
      (0 : ℝ) * z + (v4348 : ℝ) ≤ 1 - Real.cos z := by
  refine minorant_of_no_interior_critical (by
    have : (a4348 : ℚ) ≤ b4348 := by unfold a4348 b4348; norm_num
    exact_mod_cast this) endpoint_a4348 endpoint_b4348 ?_
  intro z hz hsin
  have haz : (-3.552 : ℝ) ≤ (a4348 : ℝ) := by unfold a4348; push_cast; norm_num
  have hbz : (b4348 : ℝ) ≤ (-3.548 : ℝ) := by unfold b4348; push_cast; norm_num
  have hzlo : (-3.552 : ℝ) ≤ z := le_trans haz hz.1
  have hzhi : z ≤ (-3.548 : ℝ) := le_trans hz.2 hbz
  have h1 : z + Real.pi < 0 := by
    have hpi := Real.pi_lt_d20
    linarith
  have h2 : -Real.pi < z + Real.pi := by
    have hpi := Real.pi_gt_three
    linarith
  have hneg : Real.sin (z + Real.pi) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt h1 h2
  have hzero : Real.sin (z + Real.pi) = 0 := by
    rw [Real.sin_add_pi, hsin]; ring
  linarith

end N11Formalization.G3SliceL5

/-! ## 4. Axiom profile (read only when this file has 0 errors) -/

#print axioms N11Formalization.G3SliceL5.minorant_of_no_interior_critical
#print axioms N11Formalization.G3SliceL5.q4348Lo_mem_window
#print axioms N11Formalization.G3SliceL5.q4348Hi_mem_window
#print axioms N11Formalization.G3SliceL5.q4348Lo_lt_q4348Hi
#print axioms N11Formalization.G3SliceL5.q4348Hi_lt_zero
#print axioms N11Formalization.G3SliceL5.endpoint_a4348
#print axioms N11Formalization.G3SliceL5.endpoint_b4348
#print axioms N11Formalization.G3SliceL5.minorant4348
