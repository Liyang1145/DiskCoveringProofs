/-
  G3 first slice, level L4 -- the arcsin bracket layer.

  ROLE.  L3 reduced the per-line minorant (124130 recorded lines) to two rational
  endpoint conditions plus, at every critical point z (sin z = s), the condition
          s*z + v - 1 + sqrt (1 - s^2) <= 0 .
  The only transcendental datum left is z.  This slice removes it: a rational
  bracket [x,y] for the critical point, and the consumption rule that replaces s*z
  by its worst case over the bracket.  What remains is a rational comparison.

  WHY A BRACKET SUFFICES.  On the window the critical point is UNIQUE and equals
  arcsin s (strict monotonicity of sin).  So: prove `sin x <= s <= sin y` for
  rational x,y (the consumer does this with the L1/L2 window machinery, since sin at
  a rational point is bracketed by the pi-shift + Taylor route), conclude
  `arcsin s in [x,y]`, and bound `s*z <= max (s*x) (s*y)`.  The latter needs no sign
  case split: for z in [x,y], s*z lies between s*x and s*y, hence below their max.

  API NOTE (probed in probe-L4*.lean): the inverse sine is `Real.arcsin` in this
  revision -- `Real.asin` does NOT exist.  `Real.arcsin_le_iff` and relatives do not
  exist either, so the order lemmas are built from `Real.strictMonoOn_sin` via
  `StrictMonoOn.le_iff_le` / `StrictMonoOn.eq_iff_eq`.

  INDEPENDENCE.  Imports only Mathlib; restates nothing from L0-L3 (L3's
  `critical_condition_algebraic` is an equality about the slack; the bracket lemmas
  here are about arcsin alone, and the consumption lemma is an inequality bounding
  s*z by the bracket endpoints).

  Discipline: no sorry, no custom axiom, no native_decide, no #eval.
-/
import Mathlib

namespace N11Formalization.G3SliceL4

/-! ## 1. The critical point is identified by `arcsin` -/

/-- On the window `[-pi/2, pi/2]`, a point with `sin z = s` is exactly `arcsin s`:
strict monotonicity of `sin` makes the critical point unique. -/
theorem eq_arcsin_of_sin_eq {z s : ℝ}
    (hz : z ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hs : -1 ≤ s) (hs1 : s ≤ 1) (hsin : Real.sin z = s) :
    z = Real.arcsin s := by
  have harc : Real.arcsin s ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    Real.arcsin_mem_Icc s
  have hsin2 : Real.sin z = Real.sin (Real.arcsin s) := by
    rw [hsin, Real.sin_arcsin hs hs1]
  exact (StrictMonoOn.eq_iff_eq Real.strictMonoOn_sin hz harc).mp hsin2

/-! ## 2. Rational brackets for `arcsin s` -/

/-- **Lower bracket**: if `sin x ≤ s` with `x` in the window and `-1 ≤ s ≤ 1`, then
`x ≤ arcsin s`. -/
theorem le_arcsin_of_sin_le {x s : ℝ}
    (hx : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hs : -1 ≤ s) (hs1 : s ≤ 1) (h : Real.sin x ≤ s) :
    x ≤ Real.arcsin s := by
  have harc : Real.arcsin s ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    Real.arcsin_mem_Icc s
  have hsin : Real.sin x ≤ Real.sin (Real.arcsin s) := by
    rw [Real.sin_arcsin hs hs1]; exact h
  exact (StrictMonoOn.le_iff_le Real.strictMonoOn_sin hx harc).mp hsin

/-- **Upper bracket**: if `s ≤ sin y` with `y` in the window and `-1 ≤ s ≤ 1`, then
`arcsin s ≤ y`. -/
theorem arcsin_le_of_sin_le {y s : ℝ}
    (hy : y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hs : -1 ≤ s) (hs1 : s ≤ 1) (h : s ≤ Real.sin y) :
    Real.arcsin s ≤ y := by
  have harc : Real.arcsin s ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    Real.arcsin_mem_Icc s
  have hsin : Real.sin (Real.arcsin s) ≤ Real.sin y := by
    rw [Real.sin_arcsin hs hs1]; exact h
  exact (StrictMonoOn.le_iff_le Real.strictMonoOn_sin harc hy).mp hsin

/-- The two brackets combined. -/
theorem arcsin_bracket {x y s : ℝ}
    (hx : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hy : y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hs : -1 ≤ s) (hs1 : s ≤ 1)
    (hxs : Real.sin x ≤ s) (hsy : s ≤ Real.sin y) :
    Real.arcsin s ∈ Set.Icc x y :=
  ⟨le_arcsin_of_sin_le hx hs hs1 hxs, arcsin_le_of_sin_le hy hs hs1 hsy⟩

/-! ## 3. Consumption: the bracket kills the transcendental datum -/

/-- **The consumption rule.**  If `sin z = s` and `z` lies in the bracket `[x,y]`,
then `s*z` is at most `max (s*x) (s*y)`; hence a bound at the bracket endpoints
bounds the critical condition.  (No sign case split: for `z` in `[x,y]`, `s*z` lies
between `s*x` and `s*y`.) -/
theorem critical_condition_of_bracket {s v z x y : ℝ} (hz : z ∈ Set.Icc x y)
    (hbd : max (s * x) (s * y) + v - 1 + Real.sqrt (1 - s ^ 2) ≤ 0) :
    s * z + v - 1 + Real.sqrt (1 - s ^ 2) ≤ 0 := by
  have hsz : s * z ≤ max (s * x) (s * y) := by
    rcases le_total 0 s with hs | hs
    · exact (mul_le_mul_of_nonneg_left hz.2 hs).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hz.1 hs).trans (le_max_left _ _)
  linarith

/-- The same, stated with the critical point identified as `arcsin s`: the consumer
may either use `eq_arcsin_of_sin_eq` to name the critical point, or pass through the
bracket directly.  Both routes reach a purely rational comparison. -/
theorem critical_condition_of_arcsin_bracket {s v x y : ℝ}
    (hs : -1 ≤ s) (hs1 : s ≤ 1)
    (hx : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hy : y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hxs : Real.sin x ≤ s) (hsy : s ≤ Real.sin y)
    (hbd : max (s * x) (s * y) + v - 1 + Real.sqrt (1 - s ^ 2) ≤ 0) :
    s * Real.arcsin s + v - 1 + Real.sqrt (1 - s ^ 2) ≤ 0 :=
  critical_condition_of_bracket (arcsin_bracket hx hy hs hs1 hxs hsy) hbd

end N11Formalization.G3SliceL4

/-! ## 4. Axiom profile (read only when this file has 0 errors) -/

#print axioms N11Formalization.G3SliceL4.eq_arcsin_of_sin_eq
#print axioms N11Formalization.G3SliceL4.le_arcsin_of_sin_le
#print axioms N11Formalization.G3SliceL4.arcsin_le_of_sin_le
#print axioms N11Formalization.G3SliceL4.arcsin_bracket
#print axioms N11Formalization.G3SliceL4.critical_condition_of_bracket
#print axioms N11Formalization.G3SliceL4.critical_condition_of_arcsin_bracket
