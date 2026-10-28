/-
  EndpointInterval.V3.lean — cap → periodic-interval integration (consumer geometry)
  (evidence draft 2026-10-01, producer = ownership-topology; **NOT kernel-checked by the
  producer** — the Lead owns the serial Lean slot.)

  GATE-VERSION RULE (Lead): this is a NEW file; the frozen `EndpointInterval.V2-frozen.lean`
  is not touched, and future revisions get new `…V4` names rather than overwriting.

  WHAT IS NEW HERE (relative to the frozen V2).  V2 proved the consumer *inside* the periodic
  interval model (cover-by-intervals ⇒ consecutive overlaps, wrap included).  This file
  discharges the geometric side of that model for an actual family of nine disks:

    §1  the cap of a disk is exactly the periodic angular interval of half-width
        `capHalfWidth c r` about the direction `circleAngle (centerDir c)`:
        `dist (circleMap t) c ≤ r  ↔  ∃ m : ℤ, L + m·2π ≤ t ≤ R + m·2π`
        with `L = ψ − α`, `R = ψ + α`.  Proof: project lemmas `cap_eq_of_meets`
        (dist ≤ r ↔ cos α ≤ ⟪x, centerDir c⟫), `inner_circleMap` (inner product = cos of the
        angle difference), and a new exact trig lemma
        `cos α ≤ cos d ↔ ∃ m, |d − m·2π| ≤ α` built from the project's
        `exists_abs_sub_two_pi_mul_int_le` plus its converse.
    §2  transfer of a cover of the circle to the periodic-interval cover hypothesis.
    §3  composition: nine disks covering S¹ with strictly ordered endpoint lifts meet
        consecutively.  The consumer itself is inlined (the frozen V2 file cannot be imported:
        its name is not a legal module path), with the period factor written `m · (2π)`.

  STILL EXPLICIT (not claimed here): that the nine half-widths satisfy the no-containment
  endpoint inequality `|α i − α (i+1)| < ψ (i+1) − ψ i` (its geometric equivalence and the
  `16β < 2π` essentiality input), that the directions `ψ` are the *sorted* lift of the nine
  directions, and the wrap identities `ψ 9 = ψ 0 + 2π`, `α 9 = α 0`.  No full 9-cover
  reduction is asserted.

  No `sorry`, no custom axiom, no `native_decide`.
-/
import Mathlib
import N11Formalization.Definitions
import N11Formalization.Geometry.ArcCovering
import N11Formalization.Geometry.DiskToArc

set_option linter.unusedVariables false

namespace N11Formalization.EndpointIntervalV3

open N11Formalization

/-! ## §1  Cap = periodic angular interval -/

/-- The periodic-interval membership predicate used throughout: `t` lies in the lifted
interval `[L, R]` for some period (`m · 2π`). -/
def InPeriodicInterval (L R t : ℝ) : Prop :=
  ∃ m : ℤ, L + m * (2 * Real.pi) ≤ t ∧ t ≤ R + m * (2 * Real.pi)

/-- For a unit vector `u`, the inner product with `circleMap t` is the cosine of the angle
difference to the direction of `u`. -/
theorem inner_circleMap_unit (t : ℝ) {u : Point} (hu : ‖u‖ = 1) :
    inner ℝ (circleMap t) u = Real.cos (t - circleAngle u) := by
  conv_lhs => rw [← circleMap_circleAngle u hu]
  rw [inner_circleMap]

/-- Exact trig form of interval membership: for a half-width `α ∈ [0, π]`,
`cos α ≤ cos d` holds iff `d` is within `α` of a multiple of `2π`.  (Forward direction: the
project's `exists_abs_sub_two_pi_mul_int_le`; backward: monotonicity of `cos` on `[0, π]`
plus `2π`-periodicity.) -/
theorem cos_le_cos_iff_abs {d α : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) :
    Real.cos α ≤ Real.cos d ↔ ∃ m : ℤ, |d - m * (2 * Real.pi)| ≤ α := by
  constructor
  · exact exists_abs_sub_two_pi_mul_int_le hα0 hαπ
  · rintro ⟨m, hm⟩
    calc Real.cos α ≤ Real.cos |d - m * (2 * Real.pi)| :=
          Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hαπ hm
      _ = Real.cos (d - m * (2 * Real.pi)) := Real.cos_abs _
      _ = Real.cos d := Real.cos_sub_int_mul_two_pi d m

theorem cos_le_cos_iff_interval {d α : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) :
    Real.cos α ≤ Real.cos d ↔
      ∃ m : ℤ, -α + m * (2 * Real.pi) ≤ d ∧ d ≤ α + m * (2 * Real.pi) := by
  rw [cos_le_cos_iff_abs hα0 hαπ]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by linarith [(abs_le.mp hm).1], by linarith [(abs_le.mp hm).2]⟩
  · rintro ⟨m, h1, h2⟩
    exact ⟨m, by rw [abs_le]; exact ⟨by linarith, by linarith⟩⟩

/-- **Cap = periodic interval.**  For a disk `B(c,r)` with `c ≠ 0`, `0 ≤ r < 1`, meeting `S¹`,
the cap membership of the angle-`t` point of the circle is exactly membership of `t` in the
periodic interval `[ψ − α, ψ + α]`, `ψ = circleAngle (centerDir c)`, `α = capHalfWidth c r`. -/
theorem cap_mem_iff_periodicInterval {c : Point} {r : ℝ} (hc : c ≠ 0) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hmeet : ∃ y : Point, ‖y‖ = 1 ∧ dist y c ≤ r) (t : ℝ) :
    dist (circleMap t) c ≤ r ↔
      InPeriodicInterval (circleAngle (centerDir c) - capHalfWidth c r)
        (circleAngle (centerDir c) + capHalfWidth c r) t := by
  have hnorm : ‖centerDir c‖ = 1 := centerDir_norm hc
  have hα0 : 0 ≤ capHalfWidth c r := capHalfWidth_nonneg c r
  have hαπ : capHalfWidth c r ≤ Real.pi := by
    have h1 : capHalfWidth c r ≤ Real.arcsin r := capHalfWidth_le_arcsin hc hr0 hr1
    have h2 : Real.arcsin r ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two r
    linarith [Real.pi_pos]
  have hx1 : ‖circleMap t‖ = 1 := circleMap_norm t
  rw [(cap_eq_of_meets hc hr0 hr1 hmeet hx1).1]
  have hinner : inner ℝ (circleMap t) (centerDir c) =
      Real.cos (t - circleAngle (centerDir c)) :=
    inner_circleMap_unit t hnorm
  rw [hinner]
  have hiff := cos_le_cos_iff_interval (d := t - circleAngle (centerDir c)) hα0 hαπ
  constructor
  · intro hc'
    obtain ⟨m, h1, h2⟩ := hiff.mp hc'
    exact ⟨m, by linarith, by linarith⟩
  · rintro ⟨m, h1, h2⟩
    exact hiff.mpr ⟨m, by linarith, by linarith⟩

/-! ## §2  Cover transfer: circle cover ⇒ periodic-interval cover -/

theorem periodic_cover_of_circle_cover {c : ℕ → Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcne : ∀ k < 9, c k ≠ 0)
    (hmeet : ∀ k < 9, ∃ y : Point, ‖y‖ = 1 ∧ dist y (c k) ≤ r)
    (hcov : ∀ x : Point, ‖x‖ = 1 → ∃ k < 9, dist x (c k) ≤ r) :
    ∀ t : ℝ, ∃ k < 9, InPeriodicInterval (circleAngle (centerDir (c k)) - capHalfWidth (c k) r)
      (circleAngle (centerDir (c k)) + capHalfWidth (c k) r) t := by
  intro t
  obtain ⟨k, hk, hd⟩ := hcov (circleMap t) (circleMap_norm t)
  exact ⟨k, hk, (cap_mem_iff_periodicInterval (hcne k hk) hr0 hr1 (hmeet k hk) t).mp hd⟩

/-! ## §3  Consumer, inlined from the frozen V2 (period factor written `m · (2π)`)

The frozen file `EndpointInterval.V2-frozen.lean` has a name that is not a legal module path,
so its consumer is reproduced here verbatim (up to the cosmetic period-factor form) rather
than imported.  Re-proving it keeps this file gateable standalone. -/

theorem endpoint_order {n : ℕ} {ψ α : ℕ → ℝ}
    (hgap : ∀ i < n, |α i - α (i + 1)| < ψ (i + 1) - ψ i) :
    ∀ i < n, ψ i - α i < ψ (i + 1) - α (i + 1) ∧
      ψ i + α i < ψ (i + 1) + α (i + 1) := by
  intro i hi
  have h := hgap i hi
  rw [abs_lt] at h
  exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩

theorem endpoint_mono_left {n : ℕ} {ψ α : ℕ → ℝ}
    (hgap : ∀ i < n, |α i - α (i + 1)| < ψ (i + 1) - ψ i) :
    ∀ j ≤ n, ∀ i ≤ j, ψ i - α i ≤ ψ j - α j := by
  intro j
  induction j with
  | zero =>
      intro _ i hi
      have h0 : i = 0 := by omega
      exact le_of_eq (by rw [h0])
  | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · have hj' : j ≤ n := by omega
        have hstep : ψ j - α j ≤ ψ (j + 1) - α (j + 1) :=
          le_of_lt (endpoint_order hgap j (by omega)).1
        exact (ih hj' i (by omega)).trans hstep
      · exact le_of_eq (by rw [heq])

theorem endpoint_mono_right {n : ℕ} {ψ α : ℕ → ℝ}
    (hgap : ∀ i < n, |α i - α (i + 1)| < ψ (i + 1) - ψ i) :
    ∀ j ≤ n, ∀ i ≤ j, ψ i + α i ≤ ψ j + α j := by
  intro j
  induction j with
  | zero =>
      intro _ i hi
      have h0 : i = 0 := by omega
      exact le_of_eq (by rw [h0])
  | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · have hj' : j ≤ n := by omega
        have hstep : ψ j + α j ≤ ψ (j + 1) + α (j + 1) :=
          le_of_lt (endpoint_order hgap j (by omega)).2
        exact (ih hj' i (by omega)).trans hstep
      · exact le_of_eq (by rw [heq])

/-- Consumer (inlined from the frozen V2): periodic intervals covering all angles, with
strictly increasing endpoints, overlap consecutively — wrap included. -/
theorem adjacent_overlap_of_periodic_cover {ψ α : ℕ → ℝ}
    (h9 : ψ 9 = ψ 0 + 2 * Real.pi) (hα9 : α 9 = α 0)
    (hgap : ∀ i < 9, |α i - α (i + 1)| < ψ (i + 1) - ψ i)
    (hcover : ∀ x : ℝ, ∃ k < 9, InPeriodicInterval (ψ k - α k) (ψ k + α k) x) :
    ∀ i < 9, ψ (i + 1) - α (i + 1) ≤ ψ i + α i := by
  have hL : ∀ j ≤ 9, ∀ i ≤ j, ψ i - α i ≤ ψ j - α j := endpoint_mono_left hgap
  have hR : ∀ j ≤ 9, ∀ i ≤ j, ψ i + α i ≤ ψ j + α j := endpoint_mono_right hgap
  have hL9 : ψ 9 - α 9 = ψ 0 + 2 * Real.pi - α 0 := by rw [h9, hα9]
  have hR9 : ψ 9 + α 9 = ψ 0 + 2 * Real.pi + α 0 := by rw [h9, hα9]
  intro i hi
  by_contra hcon
  have hcon' : ψ i + α i < ψ (i + 1) - α (i + 1) := not_le.mp hcon
  set x : ℝ := (ψ i + α i + (ψ (i + 1) - α (i + 1))) / 2 with hx
  have hxL : ψ i + α i < x := by rw [hx]; linarith
  have hxR : x < ψ (i + 1) - α (i + 1) := by rw [hx]; linarith
  obtain ⟨k, hk9, m, hm1, hm2⟩ := hcover x
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.two_pi_pos]
  by_cases hki : k ≤ i
  · -- `k ≤ i`
    have hRk : ψ k + α k ≤ ψ i + α i := hR i (by omega) k hki
    have hpos : (0 : ℝ) < m * (2 * Real.pi) := by linarith
    have hmR : (0 : ℝ) < (m : ℝ) := by
      by_contra hnn
      push_neg at hnn
      nlinarith
    have hmZ : (0 : ℤ) < m := by exact_mod_cast hmR
    have hm1Z : (1 : ℤ) ≤ m := by omega
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1Z
    have htop : x < ψ 0 - α 0 + 2 * Real.pi := by
      have h1 : ψ (i + 1) - α (i + 1) ≤ ψ 9 - α 9 := hL 9 (by omega) (i + 1) (by omega)
      rw [hL9] at h1
      linarith
    have hbot : ψ 0 - α 0 + 2 * Real.pi ≤ x := by
      have h1 : ψ 0 - α 0 ≤ ψ k - α k := hL k (by omega) 0 (by omega)
      have h2 : (1 : ℝ) * (2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hm1R h2pi.le
      linarith
    linarith
  · -- `k ≥ i + 1`
    have hik : i < k := Nat.lt_of_not_ge hki
    have hik' : i + 1 ≤ k := by omega
    have hLk : ψ (i + 1) - α (i + 1) ≤ ψ k - α k := hL k (by omega) (i + 1) hik'
    have hneg : m * (2 * Real.pi) < 0 := by linarith
    have hmR : (m : ℝ) < 0 := by
      by_contra hnn
      push_neg at hnn
      nlinarith
    have hmZ : m < 0 := by exact_mod_cast hmR
    have hmleZ : m ≤ -1 := by omega
    have hmleR : (m : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hmleZ
    have hbot : x ≤ ψ 0 + α 0 := by
      have h1 : ψ k + α k ≤ ψ 9 + α 9 := hR 9 (by omega) k (by omega)
      rw [hR9] at h1
      have h2 : (m : ℝ) * (2 * Real.pi) ≤ (-1 : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hmleR h2pi.le
      linarith
    have htop : ψ 0 + α 0 < x := by
      have h1 : ψ 0 + α 0 ≤ ψ i + α i := hR i (by omega) 0 (by omega)
      linarith
    linarith

/-- **Composed consumer: nine disks covering the circle meet consecutively.**

`ψ` and `α` are the site directions and cap half-widths (the hypotheses `hψ`, `hα` state
this), `h9`/`hα9` are the wrap bookkeeping, and `hgap` is the explicit no-containment input.
The conclusion is the lifted overlap `L (i+1) ≤ R i` for every `i < 9`, i.e. adjacent caps
meet — including the wrap pair `(8, 0)`. -/
theorem consecutive_caps_meet_of_circle_cover {c : ℕ → Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcne : ∀ k < 9, c k ≠ 0)
    (hmeet : ∀ k < 9, ∃ y : Point, ‖y‖ = 1 ∧ dist y (c k) ≤ r)
    (hcov : ∀ x : Point, ‖x‖ = 1 → ∃ k < 9, dist x (c k) ≤ r)
    {ψ α : ℕ → ℝ} (hψ : ∀ k < 9, ψ k = circleAngle (centerDir (c k)))
    (hα : ∀ k < 9, α k = capHalfWidth (c k) r)
    (h9 : ψ 9 = ψ 0 + 2 * Real.pi) (hα9 : α 9 = α 0)
    (hgap : ∀ i < 9, |α i - α (i + 1)| < ψ (i + 1) - ψ i) :
    ∀ i < 9, ψ (i + 1) - α (i + 1) ≤ ψ i + α i := by
  refine adjacent_overlap_of_periodic_cover h9 hα9 hgap ?_
  intro t
  obtain ⟨k, hk, hInt⟩ := periodic_cover_of_circle_cover hr0 hr1 hcne hmeet hcov t
  exact ⟨k, hk, by
    simpa only [InPeriodicInterval, ← hψ k hk, ← hα k hk] using hInt⟩

/-! ## §4  Core interface printout -/

#check @N11Formalization.EndpointIntervalV3.InPeriodicInterval
#check @N11Formalization.EndpointIntervalV3.inner_circleMap_unit
#check @N11Formalization.EndpointIntervalV3.cos_le_cos_iff_abs
#check @N11Formalization.EndpointIntervalV3.cos_le_cos_iff_interval
#check @N11Formalization.EndpointIntervalV3.cap_mem_iff_periodicInterval
#check @N11Formalization.EndpointIntervalV3.periodic_cover_of_circle_cover
#check @N11Formalization.EndpointIntervalV3.adjacent_overlap_of_periodic_cover
#check @N11Formalization.EndpointIntervalV3.consecutive_caps_meet_of_circle_cover

#print axioms N11Formalization.EndpointIntervalV3.inner_circleMap_unit
#print axioms N11Formalization.EndpointIntervalV3.cos_le_cos_iff_abs
#print axioms N11Formalization.EndpointIntervalV3.cos_le_cos_iff_interval
#print axioms N11Formalization.EndpointIntervalV3.cap_mem_iff_periodicInterval
#print axioms N11Formalization.EndpointIntervalV3.periodic_cover_of_circle_cover
#print axioms N11Formalization.EndpointIntervalV3.adjacent_overlap_of_periodic_cover
#print axioms N11Formalization.EndpointIntervalV3.consecutive_caps_meet_of_circle_cover

end N11Formalization.EndpointIntervalV3
