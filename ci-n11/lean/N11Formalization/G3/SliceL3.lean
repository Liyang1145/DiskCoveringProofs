/-
  G3 first slice, level L3 -- the exact reduction of the per-line minorant.

  THE OBLIGATION.  For each recorded minorant line of each pair of each energy leaf
  of the C921 tree (124130 lines), with a, b, s, v all RATIONAL:
        for all z in [a,b],   s*z + v  <=  1 - cos z .
  It is the last non-rational link of the leaf obligation.

  WHAT THIS FILE PROVES.  Put  S(s,v,z) := s*z + v - (1 - cos z)  (the slack).  Then
  S'(z) = s - sin z, so the maxima of S on [a,b] can only sit at an endpoint or where
  sin z = s.  Hence the EXACT equivalence

        (for all z in [a,b], s*z + v <= 1 - cos z)
        <=>  (endpoint conditions at a and b)
             AND (for all z in [a,b], sin z = s -> s*z + v <= 1 - cos z).

  Nothing here is weaker or stronger than the obligation: the two endpoint conditions
  are instances of it, and the critical condition covers exactly the remaining case.
  The value of the reduction is that it names the single hard obligation -- a
  pointwise evaluation at the critical point -- instead of hiding it inside an
  interval estimate.

  THE ALGEBRAIC FORM OF THE CRITICAL CONDITION.  Where sin z = s and cos z >= 0,
  cos^2 z = 1 - s^2 gives  cos z = sqrt (1 - s^2)  EXACTLY, so the condition becomes
        s*z + v - 1 + sqrt (1 - s^2)  <=  0 ,
  i.e. the cosine is eliminated and only the critical point z = asin(s) (mod 2pi)
  remains.  In the C921 setting every cell interval, after the L2 pi-shift, lies in
  |nu| <= 39/25 < pi/2 = 1.5707..., so cos > 0 at the shifted critical points and
  this form applies.  (Both facts are recorded, not assumed away.)

  WHAT IS STILL MISSING (named, not hidden): a rational enclosure of `asin(s)` -- so
  that `s*z` can be bounded rationally -- and rational enclosures of cos at the
  RATIONAL endpoints a, b.  This is the same kernel piece G5 needs for its acos/atan
  evaluations; the two blocks share it.

  WORKFLOW NOTE ON THE RELOCATION.  Slices L0/L1/L2 were wired into the root by the
  Lead (jobs 8782 -> 8785, each step predicted as +1/+1 before running).  L2 imports
  L1 as a MODULE (`import N11Formalization.G3.SliceL1`); evidence-directory files are
  not importable, so the earlier intermediate form inlined L1 and was deleted.
  This file (L3) currently depends on nothing but Mathlib, so it is self-contained.

  Discipline: no sorry, no custom axiom, no native_decide, no #eval.
-/
import Mathlib

namespace N11Formalization.G3SliceL3

/-! ## 1. The slack function and its derivative -/

/-- The slack of the minorant line `s*z + v <= 1 - cos z`:
`S(s,v,z) = s*z + v - (1 - cos z)`.  The obligation is `S <= 0` on the interval. -/
noncomputable def S (s v : ℝ) : ℝ → ℝ := fun z => s * z + v - (1 - Real.cos z)

theorem continuous_S (s v : ℝ) : Continuous (S s v) := by
  unfold S
  fun_prop

theorem hasDerivAt_S (s v z : ℝ) : HasDerivAt (S s v) (s - Real.sin z) z := by
  have h1 : HasDerivAt (fun w : ℝ => Real.cos w) (-Real.sin z) z := Real.hasDerivAt_cos z
  have h2 : HasDerivAt (fun w : ℝ => 1 - Real.cos w) (0 - (-Real.sin z)) z :=
    (hasDerivAt_const (x := z) (c := (1 : ℝ))).sub h1
  have h3 : HasDerivAt (fun w : ℝ => s * w + v) s z := by
    simpa using ((hasDerivAt_id z).const_mul s).add_const v
  have h4 := h3.sub h2
  have h5 : s - (0 - -Real.sin z) = s - Real.sin z := by ring
  rw [h5] at h4
  exact h4

theorem deriv_S (s v z : ℝ) : deriv (S s v) z = s - Real.sin z :=
  (hasDerivAt_S s v z).deriv

/-! ## 2. The exact reduction -/

/-- **The per-line minorant, exactly reduced.**  On `Icc a b` the obligation
`s*z + v <= 1 - cos z` holds iff it holds at both endpoints AND at every point where
`sin z = s`.  (`S` is continuous on the compact interval, so it attains a maximum; a
maximiser is either an endpoint or an interior local maximum, whose derivative
vanishes by Fermat.) -/
theorem minorant_iff_endpoints_and_critical {a b s v : ℝ} (hab : a ≤ b) :
    (∀ z ∈ Set.Icc a b, s * z + v ≤ 1 - Real.cos z) ↔
      ((s * a + v ≤ 1 - Real.cos a) ∧ (s * b + v ≤ 1 - Real.cos b) ∧
        (∀ z ∈ Set.Icc a b, Real.sin z = s → s * z + v ≤ 1 - Real.cos z)) := by
  constructor
  · intro h
    exact ⟨h a ⟨le_rfl, hab⟩, h b ⟨hab, le_rfl⟩, fun z hz _ => h z hz⟩
  · rintro ⟨ha, hb, hcrit⟩
    by_contra hcon
    simp only [not_forall, not_le] at hcon
    obtain ⟨z, hzmem, hzgt⟩ := hcon
    -- hzgt : 1 - cos z < s*z + v  i.e. 0 < S s v z
    have hzpos : 0 < S s v z := by
      unfold S; linarith
    obtain ⟨z₀, hz₀mem, hz₀max⟩ :=
      IsCompact.exists_isMaxOn isCompact_Icc (Set.nonempty_Icc.mpr hab)
        (continuous_S s v).continuousOn
    have hz₀pos : 0 < S s v z₀ := lt_of_lt_of_le hzpos ((isMaxOn_iff.mp hz₀max) z hzmem)
    have hne_a : z₀ ≠ a := by
      intro h_eq
      have hzero : S s v z₀ ≤ 0 := by
        rw [h_eq]
        unfold S
        linarith
      linarith
    have hne_b : z₀ ≠ b := by
      intro h_eq
      have hzero : S s v z₀ ≤ 0 := by
        rw [h_eq]
        unfold S
        linarith
      linarith
    have hlt_a : a < z₀ := lt_of_le_of_ne hz₀mem.1 (Ne.symm hne_a)
    have hlt_b : z₀ < b := lt_of_le_of_ne hz₀mem.2 hne_b
    have hnhds : Set.Icc a b ∈ nhds z₀ := Icc_mem_nhds hlt_a hlt_b
    have hmax : IsLocalMax (S s v) z₀ := hz₀max.isLocalMax hnhds
    have hderiv : deriv (S s v) z₀ = 0 := hmax.deriv_eq_zero
    have hsin : Real.sin z₀ = s := by
      have := deriv_S s v z₀
      linarith [hderiv]
    have hcrit₀ := hcrit z₀ hz₀mem hsin
    have : S s v z₀ ≤ 0 := by unfold S; linarith
    linarith

/-! ## 3. The algebraic form of the critical condition -/

/-- Where `sin z = s` and `0 ≤ cos z`, the cosine is determined by the slope:
`cos z = sqrt (1 - s^2)`.  This eliminates the transcendental value `cos z` from the
critical condition. -/
theorem cos_eq_sqrt_one_sub_sq {z s : ℝ} (hsin : Real.sin z = s) (hcos : 0 ≤ Real.cos z) :
    Real.cos z = Real.sqrt (1 - s ^ 2) := by
  have hsq : Real.cos z ^ 2 = 1 - s ^ 2 := by
    have h := Real.sin_sq_add_cos_sq z
    rw [hsin] at h
    linarith
  rw [← hsq, Real.sqrt_sq hcos]

/-- **The critical condition in algebraic form**: where `sin z = s` and `cos z ≥ 0`,
the minorant's slack is `s*z + v - 1 + sqrt (1 - s^2)` -- the cosine is gone, and the
only transcendental datum left is the critical point `z` itself. -/
theorem critical_condition_algebraic {z s v : ℝ} (hsin : Real.sin z = s)
    (hcos : 0 ≤ Real.cos z) :
    S s v z = s * z + v - 1 + Real.sqrt (1 - s ^ 2) := by
  unfold S
  rw [cos_eq_sqrt_one_sub_sq hsin hcos]
  ring

/-- **Sign-free worst case**: for any `z` with `sin z = s`, the cosine is at most
`sqrt (1 - s^2)`.  This is the form the reduction below consumes, because it needs no
case split on the sign of `cos z`.  (In the C921 setting the shifted critical points
have `cos > 0`, so the two forms agree there.) -/
theorem cos_le_sqrt_one_sub_sq {z s : ℝ} (hsin : Real.sin z = s) :
    Real.cos z ≤ Real.sqrt (1 - s ^ 2) := by
  have hsq : Real.cos z ^ 2 = 1 - s ^ 2 := by
    have h := Real.sin_sq_add_cos_sq z
    rw [hsin] at h
    linarith
  calc Real.cos z ≤ |Real.cos z| := le_abs_self _
    _ = Real.sqrt (Real.cos z ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt (1 - s ^ 2) := by rw [hsq]

/-- **The reduced obligation**, with the critical condition in algebraic (cosine-free)
form: it suffices to check the two rational endpoints and, at every critical point,
`s*z + v - 1 + sqrt (1 - s^2) ≤ 0`. -/
theorem minorant_of_endpoints_and_algebraic_critical {a b s v : ℝ} (hab : a ≤ b)
    (ha : s * a + v ≤ 1 - Real.cos a) (hb : s * b + v ≤ 1 - Real.cos b)
    (hcrit : ∀ z ∈ Set.Icc a b, Real.sin z = s →
      s * z + v - 1 + Real.sqrt (1 - s ^ 2) ≤ 0) :
    ∀ z ∈ Set.Icc a b, s * z + v ≤ 1 - Real.cos z := by
  refine (minorant_iff_endpoints_and_critical hab).mpr ⟨ha, hb, ?_⟩
  intro z hz hsin
  have h2 : Real.cos z ≤ Real.sqrt (1 - s ^ 2) := cos_le_sqrt_one_sub_sq hsin
  have h3 := hcrit z hz hsin
  linarith

end N11Formalization.G3SliceL3

/-! ## 4. Axiom profile (read only when this file has 0 errors) -/

#print axioms N11Formalization.G3SliceL3.continuous_S
#print axioms N11Formalization.G3SliceL3.hasDerivAt_S
#print axioms N11Formalization.G3SliceL3.deriv_S
#print axioms N11Formalization.G3SliceL3.minorant_iff_endpoints_and_critical
#print axioms N11Formalization.G3SliceL3.cos_eq_sqrt_one_sub_sq
#print axioms N11Formalization.G3SliceL3.critical_condition_algebraic
