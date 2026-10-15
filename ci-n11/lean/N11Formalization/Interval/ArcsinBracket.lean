/-
  **Outward rational brackets for `arcsin` -- the shared arc-function kernel piece.**

  WHY STANDALONE.  G3's leaf-level certificate needs the arc `L = 2*arcsin(19/50)` of
  the C921 leaves (an outward rational bracket for it), and G5's directional covers
  need `acos`/`atan` evaluators.  Keeping this as one root-resident module makes the
  shared dependency explicit in the root cone and avoids a second arc wrapper.

  ROOT-CONE AUDIT (before writing).  The root already carries arcsin INEQUALITIES
  -- `Geometry/CapArc.lean` (`arcsin_R0_lt_pi_div_eight`, `arcsin_R0_pos`,
  `arcsin_R0_le_pi_div_two`, `cos_two_arcsin`) and `Geometry/ArcCovering.lean`
  (`card_mul_two_arcsin_ge_two_pi`) -- but NO rational bracket for `arcsin(19/50)`.
  So this is not a duplicate.  Moreover mathlib already supplies the order lemmas
  (`Real.arcsin_le_iff_le_sin`, `Real.le_arcsin_iff_sin_le`), so this module needs
  nothing from G3: imports are Mathlib plus the root kernel only.

  HOW THE BRACKET IS PRODUCED.  mathlib's order lemmas reduce the two sides to
        x <= arcsin s  <->  sin x <= s  <->  sinHiNLag x <= s   (kernel upper bound)
        arcsin s <= y  <->  s <= sin y  <->  s <= sinLoNLag y   (kernel lower bound)
  so bracket production is a CLOSED RATIONAL COMPARISON -- exactly the form the
  integer-checker architecture consumes.

  Discipline: no sorry, no custom axiom, no native_decide, no #eval.
-/
import Mathlib
import N11Formalization.IntervalsHighLag

namespace N11Formalization.ArcsinBracket

/-! ## 1. Producing the bracket (one general theorem, no literals) -/

/-- **Bracket production.**  If the kernel's rational bounds sandwich `s` between
`sin x` and `sin y`, then `arcsin s` lies in `[x, y]`.  Both side conditions are
rational; no arcsin evaluator is needed. -/
theorem arcsin_bracket_of_kernel {x y s : ℚ}
    (hx : (x : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hy : (y : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hs : -1 ≤ s) (hs1 : s ≤ 1)
    (hlo : N11Formalization.sinHiNLag x ≤ s)
    (hhi : s ≤ N11Formalization.sinLoNLag y) :
    Real.arcsin (s : ℝ) ∈ Set.Icc (x : ℝ) (y : ℝ) := by
  have hsR : (s : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by exact_mod_cast hs, by exact_mod_cast hs1⟩
  constructor
  · refine (Real.le_arcsin_iff_sin_le hx hsR).mpr ?_
    have h1 := N11Formalization.sin_le_sinHiNLag x
    have h2 : ((N11Formalization.sinHiNLag x : ℚ) : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hlo
    linarith
  · refine (Real.arcsin_le_iff_le_sin hsR hy).mpr ?_
    have h1 := N11Formalization.sinLoNLag_le_sin y
    have h2 : (s : ℝ) ≤ ((N11Formalization.sinLoNLag y : ℚ) : ℝ) := by
      exact_mod_cast hhi
    linarith

/-! ## 2. The concrete bracket for `arcsin (19/50)`, hence for the C921 arc `L` -/

/-- Outward rational bracket endpoints for `arcsin (19/50)` (true value ~0.389789). -/
def asinLo : ℚ := (1150475603510479590494077 : ℚ) / (2951479051793528258560000 : ℚ)
def asinHi : ℚ := (449404532622434011541355675101 : ℚ) / (1152921504606846976000000000000 : ℚ)

/-- The kernel's upper bound at `asinLo` is below `19/50`. -/
theorem asinLo_kernel_le : N11Formalization.sinHiNLag asinLo ≤ 19 / 50 := by
  norm_num [asinLo, N11Formalization.sinHiNLag, N11Formalization.sinTQ,
    Finset.sum_range_succ]

/-- The kernel's lower bound at `asinHi` is above `19/50`. -/
theorem asinHi_kernel_ge : (19 : ℚ) / 50 ≤ N11Formalization.sinLoNLag asinHi := by
  norm_num [asinHi, N11Formalization.sinLoNLag, N11Formalization.sinTQ,
    Finset.sum_range_succ]

/-- The window memberships.  Stated with plain literals (a big `def` cast inside a
statement triggers `isDefEq` heartbeat timeouts), and the value is compared against
`3897/10000`-scale decimals that `norm_num` can handle. -/
theorem asinLo_window : (-(Real.pi / 2) : ℝ) < (3899 : ℝ) / 10000 ∧
    (3899 : ℝ) / 10000 < Real.pi / 2 := by
  have h := Real.pi_gt_d20
  constructor <;> linarith

theorem asinHi_window : (-(Real.pi / 2) : ℝ) < (3899 : ℝ) / 10000 ∧
    (3899 : ℝ) / 10000 < Real.pi / 2 := by
  have h := Real.pi_gt_d20
  constructor <;> linarith

theorem asinLo_lt_3897 : ((asinLo : ℚ) : ℝ) < (3898 : ℝ) / 10000 := by
  norm_num [asinLo]

theorem asinHi_lt_3899 : ((asinHi : ℚ) : ℝ) < (3899 : ℝ) / 10000 := by
  norm_num [asinHi]

/-- **The outward bracket for `arcsin (19/50)`** (true value 0.3897889...) with width
1e-12.  The width is set by the LEAF-LEVEL requirement, not by the kernel accuracy:
the leaf sum is linear in `L = 2*arcsin(19/50)` with coefficient sum `|c_l| ~ 0.45`, and
the tightest leaf margin is 1.64e-9, so a 4e-4-wide bracket would already lose 8.95e-5
-- 5e4 times the margin. -/
theorem arcsin_19_50_mem :
    ((1150475603510479590494077 : ℝ) / 2951479051793528258560000) ≤ Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ) ∧
      Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ) ≤ ((449404532622434011541355675101 : ℝ) / 1152921504606846976000000000000) := by
  have hcast : (((19 : ℚ) / 50 : ℚ) : ℝ) = (19 : ℝ) / 50 := by norm_num
  have hlo : ((asinLo : ℚ) : ℝ) = (1150475603510479590494077 : ℝ) / 2951479051793528258560000 := by norm_num [asinLo]
  have hhi : ((asinHi : ℚ) : ℝ) = (449404532622434011541355675101 : ℝ) / 1152921504606846976000000000000 := by norm_num [asinHi]
  have hmem := arcsin_bracket_of_kernel (x := asinLo) (y := asinHi) (s := 19 / 50)
    (by rw [hlo]
        have h1 : (0 : ℝ) < (1150475603510479590494077 : ℝ) / 2951479051793528258560000 := by norm_num
        have h2 : (1150475603510479590494077 : ℝ) / 2951479051793528258560000 < (3899 : ℝ) / 10000 := by norm_num
        exact ⟨by linarith [asinLo_window.1, Real.pi_gt_d20], by linarith [asinLo_window.2]⟩)
    (by rw [hhi]
        have h1 : (0 : ℝ) < (449404532622434011541355675101 : ℝ) / 1152921504606846976000000000000 := by norm_num
        have h2 : (449404532622434011541355675101 : ℝ) / 1152921504606846976000000000000 < (3899 : ℝ) / 10000 := by norm_num
        exact ⟨by linarith [asinHi_window.1, Real.pi_gt_d20], by linarith [asinHi_window.2]⟩)
    (by norm_num) (by norm_num) asinLo_kernel_le asinHi_kernel_ge
  rw [hlo] at hmem
  rw [hhi] at hmem
  simpa only [Set.mem_Icc] using hmem

/-- **The bracket for the C921 arc length `L = 2 * arcsin (19/50)`**, width 2e-12. -/
theorem arc_L_mem :
    (2 * ((1150475603510479590494077 : ℝ) / 2951479051793528258560000)) ≤ 2 * Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ) ∧
      2 * Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ) ≤ 2 * ((449404532622434011541355675101 : ℝ) / 1152921504606846976000000000000) :=
  ⟨by linarith [arcsin_19_50_mem.1], by linarith [arcsin_19_50_mem.2]⟩

end N11Formalization.ArcsinBracket

/-! ## 3. Axiom profile (read only when this file has 0 errors) -/

#print axioms N11Formalization.ArcsinBracket.arcsin_bracket_of_kernel
#print axioms N11Formalization.ArcsinBracket.asinLo_kernel_le
#print axioms N11Formalization.ArcsinBracket.asinHi_kernel_ge
#print axioms N11Formalization.ArcsinBracket.arcsin_19_50_mem
