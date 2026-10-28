/-
  QA rule v2 -- second-order support minorant with quadratic error absorption.
  STANDALONE DRAFT (imports Mathlib only).  Supersedes QA-Rule.lean, which is kept
  unchanged as history.  NOT compiled by its author (no Lean run in this scope);
  produced for a single Lead-controlled build slot.

  REVIEW OF THE v1 DRAFT -- three errors reported by the Lead, plus two more of the same
  class found in the author's own pass.  All five are fixed here.

  (1) v1 L82 `monotoneOn_deriv_phi`: the second argument of `monotoneOn_of_deriv_nonneg`
      must be `ContinuousOn f s` for the SAME `f` whose monotonicity is claimed, i.e.
      `ContinuousOn (deriv (qaPhi t m)) (Icc a b)`.  v1 passed continuity of `qaPhi`, a
      different function.  FIX: `continuous_deriv_qaPhi` (function identity by `funext`
      first, then continuity of the explicit expression).
  (2) v1 L97 `rw [deriv_phi, hd]`: `deriv_qaPhi` is a POINTWISE statement; rewriting the
      outer `deriv` (derivative of a function) needs the FUNCTION-level identity first.
      FIX: `deriv_qaPhi_fun` by `funext`, then `rw [deriv_qaPhi_fun]`, then the pointwise
      derivative of the resulting explicit function.  Regression probe kept as `example`.
  (3) v1 L157 `hst`: direction and signs were wrong.  The proof needs
      `(s - sin t) * (z - t) <= e * |z - t|` (equivalently the LOWER form
      `-e * |z - t| <= (sin t - s) * (z - t)`: the side carrying the minus sign is
      `sin t - s`).  v1 had `(sin t - s) * (z - t) <= e * |z - t|`, which does not give the
      minorant.  FIX: `hst` in the correct direction, from `|s - sin t| <= e`
      (via `abs_sub_comm`) and `le_abs_self`, `abs_mul`.
  (4) v1 L199 `tangent_of_cos_ge`: after `refine` the second goal is the SCALAR hypothesis
      `hc`, so `intro z hz` was illegal.  FIX: both remaining goals closed by `simp`.
  (5) v1 `one_sub_cos_ge_taylor2`, both branches: `MonotoneOn` was applied to membership
      proofs from the WRONG interval (`hanti hz <hzt, le_rfl> hz.2`, where `hz` is
      membership in `Icc a b` while the set is `Icc z t`).  FIX: correct memberships, and
      the `[a,b]`-monotonicity is applied directly with `[a,b]` memberships, so
      `MonotoneOn.mono` is not needed at all (one fewer unverified library name).

  DISCIPLINE NOTE (Lead's review): library names are NOT trusted here.  Everything used is
  listed in the `#check` block with its FULL type, so one build slot shows all signatures
  before the proofs.  Names the author could not verify are marked `-- UNVERIFIED NAME`.

  Discipline: no sorry, no custom axiom, no native_decide, no #eval, autoImplicit false.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false

namespace N11Formalization.QASupport

/- full types of every library fact used below (read these first). -/
section checks

#check @monotoneOn_of_deriv_nonneg

#check @antitoneOn_of_deriv_nonpos

#check @convex_Icc

#check @interior_subset

#check @Continuous.sub

#check @ContinuousOn.sub

#check @continuous_const

#check @continuous_id

#check @Real.hasDerivAt_sin

#check @Real.hasDerivAt_cos

#check @hasDerivAt_const

#check @hasDerivAt_id

#check @HasDerivAt.sub

#check @HasDerivAt.sub_const

#check @HasDerivAt.const_mul

#check @HasDerivAt.pow -- UNVERIFIED NAME (used once, in `hasDerivAt_sq_sub`)

#check @HasDerivAt.deriv

#check @HasDerivAt.differentiableAt

#check @DifferentiableAt.differentiableWithinAt

#check @abs_mul

#check @abs_sub_comm -- UNVERIFIED NAME

#check @le_abs_self

#check @abs_nonneg

#check @mul_le_mul_of_nonneg_right

#check @mul_le_mul_of_nonpos_left

#check @le_max_left

#check @le_max_right

#check @sub_sq -- UNVERIFIED NAME

#check @sq_abs -- UNVERIFIED NAME

#check @sq_nonneg

#check @ne_of_gt

#check @funext

end checks

/-- `qaPhi t m z = (1 - cos z) - sin t * (z - t) - (m/2) * (z - t)^2`.
Its minimum on `[a,b]` is `qaPhi t m t = 1 - cos t` whenever `cos >= m` on `[a,b]`. -/
noncomputable def qaPhi (t m : ℝ) : ℝ → ℝ :=
  fun z => (1 - Real.cos z) - Real.sin t * (z - t) - (m / 2) * (z - t) ^ 2

theorem continuous_qaPhi (t m : ℝ) : Continuous (qaPhi t m) := by
  unfold qaPhi
  fun_prop

/-- Derivative of `(w - t)^2` at `z`, isolated so that `HasDerivAt.pow` is used once. -/
theorem hasDerivAt_sq_sub (t z : ℝ) :
    HasDerivAt (fun w : ℝ => (w - t) ^ 2) (2 * (z - t)) z := by
  have hid : HasDerivAt (fun w : ℝ => w - t) (1 : ℝ) z := by
    simpa using (hasDerivAt_id z).sub_const t
  have h := hid.mul hid
  have hv : (1 : ℝ) * (z - t) + (z - t) * 1 = 2 * (z - t) := by ring
  rw [hv] at h
  have heq : ((fun w : ℝ => w - t) * (fun w : ℝ => w - t)) =
      (fun w : ℝ => (w - t) ^ 2) := by
    funext w
    exact (pow_two (w - t)).symm
  rw [heq] at h
  exact h

theorem hasDerivAt_qaPhi (t m z : ℝ) :
    HasDerivAt (qaPhi t m) (Real.sin z - Real.sin t - m * (z - t)) z := by
  unfold qaPhi
  have hcos : HasDerivAt (fun w : ℝ => Real.cos w) (-Real.sin z) z := Real.hasDerivAt_cos z
  have h1 : HasDerivAt (fun w : ℝ => 1 - Real.cos w) (0 - (-Real.sin z)) z :=
    (hasDerivAt_const (x := z) (c := (1 : ℝ))).sub hcos
  have hid : HasDerivAt (fun w : ℝ => w - t) (1 : ℝ) z := by
    simpa using (hasDerivAt_id z).sub_const t
  have h2 : HasDerivAt (fun w : ℝ => Real.sin t * (w - t)) (Real.sin t) z := by
    simpa using hid.const_mul (Real.sin t)
  have h3 : HasDerivAt (fun w : ℝ => (m / 2) * (w - t) ^ 2) (m * (z - t)) z := by
    have h4 := (hasDerivAt_sq_sub t z).const_mul (m / 2)
    have hv : (m / 2) * (2 * (z - t)) = m * (z - t) := by ring
    rw [hv] at h4
    exact h4
  have h := (h1.sub h2).sub h3
  have hv2 : (0 - (-Real.sin z)) - Real.sin t - m * (z - t)
      = Real.sin z - Real.sin t - m * (z - t) := by ring
  rw [hv2] at h
  exact h

theorem deriv_qaPhi (t m z : ℝ) :
    deriv (qaPhi t m) z = Real.sin z - Real.sin t - m * (z - t) :=
  (hasDerivAt_qaPhi t m z).deriv

/-- FUNCTION-level identity (the fix for review item 2). -/
theorem deriv_qaPhi_fun (t m : ℝ) :
    deriv (qaPhi t m) = fun w : ℝ => Real.sin w - Real.sin t - m * (w - t) :=
  funext (fun w => deriv_qaPhi t m w)

theorem continuous_deriv_qaPhi (t m : ℝ) : Continuous (deriv (qaPhi t m)) := by
  rw [deriv_qaPhi_fun]
  fun_prop

theorem differentiableAt_deriv_qaPhi (t m z : ℝ) : DifferentiableAt ℝ (deriv (qaPhi t m)) z := by
  rw [deriv_qaPhi_fun]
  have h1 : HasDerivAt (fun w : ℝ => Real.sin w - Real.sin t) (Real.cos z) z := by
    simpa using (Real.hasDerivAt_sin z).sub_const (Real.sin t)
  have h2 : HasDerivAt (fun w : ℝ => m * (w - t)) m z := by
    simpa using ((hasDerivAt_id z).sub_const t).const_mul m
  exact (h1.sub h2).differentiableAt

/-- REGRESSION PROBE for review item 2: the pointwise derivative of the explicit function
that `deriv_qaPhi_fun` produces.  If this fails, `monotoneOn_deriv_qaPhi` fails at the same
rewrite. -/
example (t m z : ℝ) :
    deriv (fun w : ℝ => Real.sin w - Real.sin t - m * (w - t)) z = Real.cos z - m := by
  have h1 : HasDerivAt (fun w : ℝ => Real.sin w - Real.sin t) (Real.cos z) z := by
    simpa using (Real.hasDerivAt_sin z).sub_const (Real.sin t)
  have h2 : HasDerivAt (fun w : ℝ => m * (w - t)) m z := by
    simpa using ((hasDerivAt_id z).sub_const t).const_mul m
  exact (h1.sub h2).deriv

/-- `qaPhi'` is nondecreasing where `cos >= m`; the only input besides differentiability. -/
theorem monotoneOn_deriv_qaPhi {a b t m : ℝ} (hm : ∀ z ∈ Set.Icc a b, m ≤ Real.cos z) :
    MonotoneOn (deriv (qaPhi t m)) (Set.Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuous_deriv_qaPhi t m).continuousOn
    (fun x _ => (differentiableAt_deriv_qaPhi t m x).differentiableWithinAt) ?_
  intro x hx
  have hx' : x ∈ Set.Icc a b := interior_subset hx
  rw [deriv_qaPhi_fun]
  have h1 : HasDerivAt (fun w : ℝ => Real.sin w - Real.sin t) (Real.cos x) x := by
    simpa using (Real.hasDerivAt_sin x).sub_const (Real.sin t)
  have h2 : HasDerivAt (fun w : ℝ => m * (w - t)) m x := by
    simpa using ((hasDerivAt_id x).sub_const t).const_mul m
  have hd : deriv (fun w : ℝ => Real.sin w - Real.sin t - m * (w - t)) x = Real.cos x - m :=
    (h1.sub h2).deriv
  rw [hd]
  linarith [hm x hx']

/-- **Lemma 1 (strong convexity of `1 - cos` with constant `m`).**  Continuum hypothesis
`cos >= m` on the whole interval; `t` and `z` both range over the whole interval. -/
theorem one_sub_cos_ge_taylor2 {a b t m : ℝ} (hab : a ≤ b)
    (ht : t ∈ Set.Icc a b) (hm : ∀ z ∈ Set.Icc a b, m ≤ Real.cos z) :
    ∀ z ∈ Set.Icc a b,
      1 - Real.cos t + Real.sin t * (z - t) + (m / 2) * (z - t) ^ 2 ≤ 1 - Real.cos z := by
  intro z hz
  have hmono := monotoneOn_deriv_qaPhi (a := a) (b := b) (t := t) (m := m) hm
  have hderiv_t : deriv (qaPhi t m) t = 0 := by rw [deriv_qaPhi]; ring
  have hphi_t : qaPhi t m t = 1 - Real.cos t := by unfold qaPhi; ring
  rcases le_total t z with htz | hzt
  · have hnonneg : ∀ w ∈ Set.Icc t z, 0 ≤ deriv (qaPhi t m) w := by
      intro w hw
      have hwab : w ∈ Set.Icc a b := ⟨le_trans ht.1 hw.1, le_trans hw.2 hz.2⟩
      have hle : deriv (qaPhi t m) t ≤ deriv (qaPhi t m) w := hmono ht hwab hw.1
      linarith
    have hmono_phi : MonotoneOn (qaPhi t m) (Set.Icc t z) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc t z) (continuous_qaPhi t m).continuousOn
        (fun x _ => (hasDerivAt_qaPhi t m x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      exact hnonneg x (interior_subset hx)
    have hfin := hmono_phi ⟨le_rfl, htz⟩ ⟨htz, le_rfl⟩ htz
    rw [hphi_t] at hfin
    unfold qaPhi at hfin
    linarith
  · have hnonpos : ∀ w ∈ Set.Icc z t, deriv (qaPhi t m) w ≤ 0 := by
      intro w hw
      have hwab : w ∈ Set.Icc a b := ⟨le_trans hz.1 hw.1, le_trans hw.2 ht.2⟩
      have hle : deriv (qaPhi t m) w ≤ deriv (qaPhi t m) t := hmono hwab ht hw.2
      linarith
    have hanti : AntitoneOn (qaPhi t m) (Set.Icc z t) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc z t) (continuous_qaPhi t m).continuousOn
        (fun x _ => (hasDerivAt_qaPhi t m x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      exact hnonpos x (interior_subset hx)
    have hfin := hanti ⟨le_rfl, hzt⟩ ⟨hzt, le_rfl⟩ hzt
    rw [hphi_t] at hfin
    unfold qaPhi at hfin
    linarith

/-- The completing-the-square scalar inequality `e|u| <= (m/2)u^2 + e^2/(2m)`
(holds for every real `e`; no sign hypothesis needed). -/
theorem abs_scaled_le_sq {m : ℝ} (hm : 0 < m) (e : ℝ) (u : ℝ) :
    e * |u| ≤ (m / 2) * u ^ 2 + e ^ 2 / (2 * m) := by
  have hsq : 0 ≤ (m / 2) * (|u| - e / m) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hm2 : (2 * m) ≠ 0 := ne_of_gt (by positivity)
  have hid : (m / 2) * (|u| - e / m) ^ 2
      = (m / 2) * u ^ 2 - e * |u| + e ^ 2 / (2 * m) := by
    rw [sub_sq, sq_abs]
    field_simp [hm0, hm2]
  linarith

/-- REGRESSION PROBE for the completing-the-square identity (the `abs_mul_abs_self` vs
`sq_abs` issue): the identity holds as a `field_simp; ring` computation. -/
example (m e u : ℝ) (hm : 0 < m) :
    (m / 2) * (|u| - e / m) ^ 2 = (m / 2) * u ^ 2 - e * |u| + e ^ 2 / (2 * m) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hm2 : (2 * m) ≠ 0 := ne_of_gt (by positivity)
  rw [sub_sq, sq_abs]
  field_simp [hm0, hm2]

/-- **Lemma 2 (QA rule).**  The rational line with the explicit drop `e^2/(2m)`. -/
theorem minorant_of_second_order_support {a b t s c m e : ℝ} (hab : a ≤ b)
    (hm : 0 < m) (hcos : ∀ z ∈ Set.Icc a b, m ≤ Real.cos z)
    (ht : t ∈ Set.Icc a b) (he : 0 ≤ e) (hes : |Real.sin t - s| ≤ e)
    (hc : c ≤ 1 - Real.cos t - s * t - e ^ 2 / (2 * m)) :
    ∀ z ∈ Set.Icc a b, s * z + c ≤ 1 - Real.cos z := by
  intro z hz
  have h1 := one_sub_cos_ge_taylor2 hab ht hcos z hz
  have hes' : |s - Real.sin t| ≤ e := by
    rw [abs_sub_comm]
    exact hes
  have h2 : |s - Real.sin t| * |z - t| ≤ e * |z - t| :=
    mul_le_mul_of_nonneg_right hes' (abs_nonneg _)
  have hst : (s - Real.sin t) * (z - t) ≤ e * |z - t| := by
    calc (s - Real.sin t) * (z - t) ≤ |(s - Real.sin t) * (z - t)| := le_abs_self _
      _ = |s - Real.sin t| * |z - t| := by rw [abs_mul]
      _ ≤ e * |z - t| := h2
  have hcs := abs_scaled_le_sq (m := m) hm e (z - t)
  have hsz : s * z = s * t + s * (z - t) := by ring
  have hsplit : s * (z - t) = (s - Real.sin t) * (z - t) + Real.sin t * (z - t) := by ring
  linarith [h1, hst, hcs, hc, hsz, hsplit]

/-- **Corollary: rationalized intercept.**  A rational upper bound `u >= cos t` may replace
`cos t` in the intercept (the intercept only decreases). -/
theorem minorant_of_second_order_support_rational {a b t s c u m e : ℝ} (hab : a ≤ b)
    (hm : 0 < m) (hcos : ∀ z ∈ Set.Icc a b, m ≤ Real.cos z)
    (ht : t ∈ Set.Icc a b) (he : 0 ≤ e) (hes : |Real.sin t - s| ≤ e)
    (hu : Real.cos t ≤ u)
    (hc : c ≤ 1 - u - s * t - e ^ 2 / (2 * m)) :
    ∀ z ∈ Set.Icc a b, s * z + c ≤ 1 - Real.cos z :=
  minorant_of_second_order_support hab hm hcos ht he hes (by linarith)

/-- **Corollary: bracket consumption for `s * t`** (no sign case split).  Same pattern as
`G3SliceL4.critical_condition_of_bracket`. -/
theorem s_mul_le_max_of_mem_bracket {s t x y : ℝ} (ht : t ∈ Set.Icc x y) :
    s * t ≤ max (s * x) (s * y) := by
  rcases le_total 0 s with hs | hs
  · exact (mul_le_mul_of_nonneg_left ht.2 hs).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left ht.1 hs).trans (le_max_left _ _)

/-- **Calibration instance (`e = 0`)**: the tangent bound on any arc with `cos >= m > 0`.
No monotonicity of `sin` is needed (contrast `FlashCosineSupport.support_of_monotone_sin`). -/
theorem tangent_of_cos_ge {a b t m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hcos : ∀ z ∈ Set.Icc a b, m ≤ Real.cos z) (ht : t ∈ Set.Icc a b) :
    ∀ z ∈ Set.Icc a b,
      Real.sin t * z + (1 - Real.cos t - Real.sin t * t) ≤ 1 - Real.cos z := by
  refine minorant_of_second_order_support (s := Real.sin t)
    (c := 1 - Real.cos t - Real.sin t * t) (m := m) (e := 0) hab hm hcos ht le_rfl ?_ ?_
  · simp
  · simp

/-- REGRESSION PROBE for review item 4: the `e = 0` scalar goal is closed by `simp`. -/
example (t m : ℝ) : (1 - Real.cos t - Real.sin t * t : ℝ) ≤
    1 - Real.cos t - Real.sin t * t - 0 ^ 2 / (2 * m) := by
  simp

end N11Formalization.QASupport

/-! Axiom profile (read only when this file has 0 errors and 0 warnings). -/

#print axioms N11Formalization.QASupport.one_sub_cos_ge_taylor2

#print axioms N11Formalization.QASupport.abs_scaled_le_sq

#print axioms N11Formalization.QASupport.minorant_of_second_order_support

#print axioms N11Formalization.QASupport.minorant_of_second_order_support_rational

#print axioms N11Formalization.QASupport.s_mul_le_max_of_mem_bracket

#print axioms N11Formalization.QASupport.tangent_of_cos_ge
