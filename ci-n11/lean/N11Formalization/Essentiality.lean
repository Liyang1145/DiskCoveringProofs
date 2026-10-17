/-
  Essentiality.V3.lean — no redundant cap, from the gated cap measure (V3)
  (evidence draft 2026-10-01, producer = ownership-topology; **NOT kernel-checked by the
  producer** — the Lead owns the serial Lean slot.  NEW file; V1/V2 are not edited.)

  ## V3 repairs gate2 (`lead/essentiality-gate2.log`): one remaining error, L176

  Gate2 left a single error: at the membership proof for `Finset.univ.erase i9` the term
  `hji : j ≠ i` (a `ℕ`-inequality) had to prove `¬ ⟨j, hj9⟩ = i9` (a `Fin 9` equation) and
  `simpa` could not bridge it, because `i9` was introduced with `set … with hi9`, so `i9.val`
  was *not* definitionally `i`.  Fix (Lead's prescription): drop the `set i9`, use
  `⟨i, hi⟩ : Fin 9` inline at every site of use (so `Fin.val` projections reduce by `rfl`),
  and prove the two `Fin` inequalities by `intro hEq; exact hji (congrArg Fin.val hEq)`
  (first branch) resp. `have hkv : k.val = i := congrArg Fin.val hEq; rw [hkv] at hk` (second
  branch).  All measure bounds and the strict `16 arcsin` bound were already standard/standard
  axioms in gate2; `exists_cap_exclusive_point` was carried by `sorryAx` only because of this
  error, so V3 is the first revision in which it is actually discharged.

  ## V2 repaired gate1 (`lead/essentiality-gate1.log`)

  Primary defect: the file never opened `MeasureTheory`, so with Lean's default
  `autoImplicit true` every occurrence of `volume` (and `measure_mono`, `volume.real`) in the
  *statements* was silently auto-bound as a fresh implicit variable — the gate log even shows
  the polluted type `@volumeReal_capPreimage_le : ∀ {c r}, 0 ≤ r → r < 1 → sorry ≤ 2 * arcsin r`
  and the hint "The identifier `volume` is unknown, and Lean's `autoImplicit` option causes an
  unknown identifier to be treated as an implicitly bound variable".  Fixes:

    * `set_option autoImplicit false` — so a missing name can never again pollute a type;
    * `open MeasureTheory` and `noncomputable section` (the pattern of the gate-green
      `OwnershipLedger.lean`: `open MeasureTheory`, `open N11Formalization.ResumeGlobal`,
      `noncomputable section`), giving `volume`, `measure_mono`, `measureReal_mono`,
      `measureReal_biUnion_finset_le`;
    * `rcases le_or_lt …` (unknown identifier) replaced by `by_cases hdi : …` with
      `not_le.mp hdi` in the negative branch;
    * `push_neg` (deprecated in this toolchain) replaced by `push Not`.

  Every declaration is re-audited with `autoImplicit false` and its full type is printed at the
  end (`#check @`), so no parameter can be implicitly invented.

  ## Content (unchanged from V1)

    §1  cap measure copied verbatim from the gate3-green `OwnershipLedger` §3
        (`capPreimage`, `volumeReal_capPreimage_le`, `capPreimage_measure_ne_top`) plus the
        certified-π strict bound `sixteen_arcsin_lt_two_pi_of_le_R0`, from the **library** fact
        `eight_mul_arcsin_R0_lt_pi` (`Geometry/CapArc.lean:46`).
    §2  `exists_cap_exclusive_point` — nine radius-`r` disks covering `S¹` with `r ≤ 19/50`:
        each disk owns a circle point outside all the others (otherwise the other eight
        preimages cover `(0,2π)`, giving `2π ≤ 8·2 arcsin r = 16 arcsin r < 2π`).
    §3  `not_cap_subset_of_covers` and the periodic-interval form
        `not_interval_subset_of_covers` (via the in-tree module's
        `cap_mem_iff_periodicInterval`) — the `hno1`/`hno2` inputs of `NoContainment.V3`.

  STILL EXPLICIT / OPEN: the sorted lift (`horder`, wrap identities) and
  `Covers c r ⇒ circle cover` (restricting to `‖x‖ = 1`).

  No `sorry`, no custom axiom, no `native_decide`.
-/
import Mathlib
import N11Formalization.Definitions
import N11Formalization.Geometry.ArcCovering
import N11Formalization.Geometry.CapArc
import N11Formalization.EndpointInterval

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.Essentiality

open MeasureTheory
open N11Formalization

noncomputable section

/-! ## §1  Cap measure (verbatim from the gate3-green `OwnershipLedger.lean` §3) -/

/-- Angular preimage of the cap of a single disk. -/
def capPreimage (c : Point) (r : ℝ) : Set ℝ :=
  {t : ℝ | t ∈ Set.Ioo 0 (2 * Real.pi) ∧ dist (circleMap t) c ≤ r}

/-- Per-disk cap measure bound `≤ 2 arcsin r`.  (Proof copied verbatim from
`OwnershipLedger.volumeReal_capPreimage_le`, gate3 GREEN.) -/
theorem volumeReal_capPreimage_le {c : Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    volume.real (capPreimage c r) ≤ 2 * Real.arcsin r := by
  set δ : ℝ := Real.arcsin r with hδdef
  have hδ0 : 0 ≤ δ := Real.arcsin_nonneg.mpr hr0
  have hδ2 : δ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two r
  rcases eq_or_ne c 0 with hzero | hne
  · have hempty : capPreimage c r = ∅ := by
      ext t
      constructor
      · rintro ⟨-, hd⟩
        rw [hzero, dist_zero_right, circleMap_norm] at hd
        linarith
      · intro h
        exact absurd h (Set.notMem_empty t)
    rw [hempty]
    show (volume (∅ : Set ℝ)).toReal ≤ 2 * Real.arcsin r
    rw [measure_empty, ENNReal.toReal_zero]
    linarith
  · have hs : 0 < ‖c‖ := norm_pos_iff.mpr hne
    have hnorm : ‖(‖c‖)⁻¹ • c‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (ne_of_gt hs)]
    set θ : ℝ := circleAngle ((‖c‖)⁻¹ • c) with hθdef
    have hθmem : θ ∈ Set.Ioc (-Real.pi) Real.pi := by
      rw [hθdef]
      exact circleAngle_mem_Ioc _
    have hθ : circleMap θ = (‖c‖)⁻¹ • c := by
      rw [hθdef]
      exact circleMap_circleAngle _ hnorm
    have hc_eq : c = ‖c‖ • circleMap θ := by
      rw [hθ, smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
    have hsub : capPreimage c r ⊆
        {t : ℝ | t ∈ Set.Ioo 0 (2 * Real.pi) ∧ Real.cos δ ≤ Real.cos (t - θ)} := by
      rintro t ⟨htI, hd⟩
      refine ⟨htI, ?_⟩
      have hinner : inner ℝ (circleMap t) c = ‖c‖ * Real.cos (t - θ) := by
        conv_lhs => rw [hc_eq]
        rw [real_inner_smul_right, inner_circleMap]
      have hiff := (mem_sphere_closedBall_iff hr0 (circleMap_norm t)).mp hd
      rw [hinner] at hiff
      have hnum : 0 ≤ 1 + ‖c‖ ^ 2 - r ^ 2 := by nlinarith
      have hden : (0 : ℝ) < 2 * ‖c‖ := by linarith
      have hτ0 : 0 ≤ (1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖) := div_nonneg hnum hden.le
      have hτ : (1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖) ≤ Real.cos (t - θ) := by
        rw [div_le_iff₀ hden]
        linarith
      have hsqrt : Real.sqrt (1 - r ^ 2) ≤ (1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖) := by
        have hden2 : (0 : ℝ) < (2 * ‖c‖) ^ 2 := by nlinarith [hs]
        have hsq : (Real.sqrt (1 - r ^ 2)) ^ 2
            ≤ ((1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖)) ^ 2 := by
          rw [Real.sq_sqrt (by nlinarith), div_pow, le_div_iff₀ hden2]
          nlinarith [sq_nonneg (‖c‖ ^ 2 - (1 - r ^ 2))]
        have h2 := sq_le_sq.mp hsq
        rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hτ0] at h2
      have hcosδ : Real.cos δ = Real.sqrt (1 - r ^ 2) := by
        rw [hδdef, Real.cos_arcsin]
      rw [hcosδ]
      linarith
    have hmain : volume (capPreimage c r) ≤ ENNReal.ofReal (2 * δ) :=
      (measure_mono hsub).trans (volume_cos_ge_le hθmem hδ0 hδ2)
    calc volume.real (capPreimage c r) = (volume (capPreimage c r)).toReal := rfl
      _ ≤ (ENNReal.ofReal (2 * δ)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne hmain
      _ = 2 * δ := ENNReal.toReal_ofReal (by linarith)
      _ = 2 * Real.arcsin r := by rw [hδdef]

theorem capPreimage_measure_ne_top {c : Point} {r : ℝ} :
    volume (capPreimage c r) ≠ ⊤ := by
  have hsub : capPreimage c r ⊆ Set.Ioo (0 : ℝ) (2 * Real.pi) := fun t ht => ht.1
  have hb : volume (capPreimage c r) ≤ ENNReal.ofReal (2 * Real.pi) := by
    calc volume (capPreimage c r) ≤ volume (Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
          measure_mono hsub
      _ = ENNReal.ofReal (2 * Real.pi) := by rw [Real.volume_Ioo, sub_zero]
  exact ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hb

/-- Certified-π strict bound: `16 arcsin r < 2π` for `r ≤ 19/50`, from the **library** fact
`eight_mul_arcsin_R0_lt_pi` (`Geometry/CapArc.lean:46`).  No numeric evaluation. -/
theorem sixteen_arcsin_lt_two_pi_of_le_R0 {r : ℝ} (hr : r ≤ (19 : ℝ) / 50) :
    16 * Real.arcsin r < 2 * Real.pi := by
  have h := eight_mul_arcsin_R0_lt_pi
  have h2 : Real.arcsin r ≤ Real.arcsin ((19 : ℝ) / 50) := Real.arcsin_le_arcsin hr
  linarith [Real.pi_pos]

/-! ## §2  Essentiality: no redundant cap -/

/-- **No redundant cap (essentiality, point form).**  Nine radius-`r` disks covering the
circle with `r ≤ 19/50`: each disk owns a circle point outside all the other eight. -/
theorem exists_cap_exclusive_point {c : ℕ → Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrR0 : r ≤ (19 : ℝ) / 50)
    (hcov : ∀ x : Point, ‖x‖ = 1 → ∃ k < 9, dist x (c k) ≤ r) {i : ℕ} (hi : i < 9) :
    ∃ t : ℝ, t ∈ Set.Ioo 0 (2 * Real.pi) ∧ dist (circleMap t) (c i) ≤ r ∧
      ∀ j < 9, j ≠ i → r < dist (circleMap t) (c j) := by
  classical
  by_contra h
  push Not at h
  have hcov9 : ∀ x : Point, ‖x‖ = 1 → ∃ k : Fin 9, dist x (c k.val) ≤ r := by
    intro x hx
    obtain ⟨k, hk, hd⟩ := hcov x hx
    exact ⟨⟨k, hk⟩, hd⟩
  set s : Finset (Fin 9) := Finset.univ.erase (⟨i, hi⟩ : Fin 9) with hs
  have hpre : Set.Ioo (0 : ℝ) (2 * Real.pi) ⊆ ⋃ j ∈ s, capPreimage (c j.val) r := by
    intro t ht
    by_cases hdi : dist (circleMap t) (c i) ≤ r
    · obtain ⟨j, hj9, hji, hdj⟩ := h t ht hdi
      have hmem : (⟨j, hj9⟩ : Fin 9) ∈ s := by
        rw [hs]
        exact Finset.mem_erase.mpr
          ⟨by intro hEq; exact hji (congrArg Fin.val hEq), Finset.mem_univ _⟩
      exact Set.mem_iUnion.mpr ⟨⟨j, hj9⟩, Set.mem_iUnion.mpr ⟨hmem, ⟨ht, hdj⟩⟩⟩
    · have hdi' : r < dist (circleMap t) (c i) := not_le.mp hdi
      obtain ⟨k, hk⟩ := hcov9 (circleMap t) (circleMap_norm t)
      have hki : k ≠ (⟨i, hi⟩ : Fin 9) := by
        intro hEq
        have hkv : k.val = i := congrArg Fin.val hEq
        rw [hkv] at hk
        exact absurd hk (not_le.mpr hdi')
      have hmem : k ∈ s := by
        rw [hs]
        exact Finset.mem_erase.mpr ⟨hki, Finset.mem_univ _⟩
      exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hmem, ⟨ht, hk⟩⟩⟩
  have hunion_sub : (⋃ j ∈ s, capPreimage (c j.val) r) ⊆ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
    intro t ht
    rw [Set.mem_iUnion] at ht
    obtain ⟨j, ht⟩ := ht
    rw [Set.mem_iUnion] at ht
    obtain ⟨_, ht⟩ := ht
    exact ht.1
  have hfin : volume (⋃ j ∈ s, capPreimage (c j.val) r) ≠ ⊤ := by
    have hle : volume (⋃ j ∈ s, capPreimage (c j.val) r) ≤ ENNReal.ofReal (2 * Real.pi) :=
      (measure_mono hunion_sub).trans (by rw [Real.volume_Ioo, sub_zero])
    exact ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hle
  have hmono : volume.real (Set.Ioo (0 : ℝ) (2 * Real.pi))
      ≤ volume.real (⋃ j ∈ s, capPreimage (c j.val) r) :=
    measureReal_mono hpre hfin
  have hbi : volume.real (⋃ j ∈ s, capPreimage (c j.val) r)
      ≤ ∑ j ∈ s, volume.real (capPreimage (c j.val) r) :=
    measureReal_biUnion_finset_le s (fun j => capPreimage (c j.val) r)
  have hper : ∀ j ∈ s, volume.real (capPreimage (c j.val) r) ≤ 2 * Real.arcsin r :=
    fun j _ => volumeReal_capPreimage_le (c := c j.val) hr0 hr1
  have hcard : s.card = 8 := by
    rw [hs]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (⟨i, hi⟩ : Fin 9)), Finset.card_univ,
      Fintype.card_fin]
    try norm_num
  have hbound : ∑ j ∈ s, volume.real (capPreimage (c j.val) r) ≤ 8 * (2 * Real.arcsin r) := by
    calc ∑ j ∈ s, volume.real (capPreimage (c j.val) r)
        ≤ ∑ _j ∈ s, (2 * Real.arcsin r) := Finset.sum_le_sum hper
      _ = ((s.card : ℕ) : ℝ) * (2 * Real.arcsin r) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = 8 * (2 * Real.arcsin r) := by
            rw [hcard]
            norm_num
  have hLHS : volume.real (Set.Ioo (0 : ℝ) (2 * Real.pi)) = 2 * Real.pi := by
    show (volume (Set.Ioo (0 : ℝ) (2 * Real.pi))).toReal = 2 * Real.pi
    rw [Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  have h16 : 16 * Real.arcsin r < 2 * Real.pi := sixteen_arcsin_lt_two_pi_of_le_R0 hrR0
  have hchain : 2 * Real.pi ≤ 8 * (2 * Real.arcsin r) := by
    rw [hLHS] at hmono
    linarith
  linarith

/-! ## §3  Consumer-facing corollaries: the two containment negations -/

/-- **Non-containment (cap form).**  With `j ≠ i` and `j < 9` the containment
`cap i ⊆ cap j` fails; this is exactly the `hno1`/`hno2` shape of
`NoContainment.V3.gap_gt_abs_sub_of_cap_no_containment`. -/
theorem not_cap_subset_of_covers {c : ℕ → Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrR0 : r ≤ (19 : ℝ) / 50)
    (hcov : ∀ x : Point, ‖x‖ = 1 → ∃ k < 9, dist x (c k) ≤ r)
    {i j : ℕ} (hi : i < 9) (hj : j < 9) (hji : j ≠ i) :
    ¬ (∀ x : Point, ‖x‖ = 1 → dist x (c i) ≤ r → dist x (c j) ≤ r) := by
  intro hsub
  obtain ⟨t, _ht, hti, hexcl⟩ := exists_cap_exclusive_point hr0 hr1 hrR0 hcov hi
  have hx : ‖circleMap t‖ = 1 := circleMap_norm t
  exact absurd (hsub (circleMap t) hx hti) (not_le.mpr (hexcl j hj hji))

/-- **Non-containment in the consumer's own vocabulary (periodic intervals).**  Uses the
in-tree module `EndpointIntervalV3.cap_mem_iff_periodicInterval`, so the cap definitions here
are literally the consumer's. -/
theorem not_interval_subset_of_covers {c : ℕ → Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrR0 : r ≤ (19 : ℝ) / 50)
    (hcne : ∀ k < 9, c k ≠ 0)
    (hmeet : ∀ k < 9, ∃ y : Point, ‖y‖ = 1 ∧ dist y (c k) ≤ r)
    (hcov : ∀ x : Point, ‖x‖ = 1 → ∃ k < 9, dist x (c k) ≤ r)
    {i j : ℕ} (hi : i < 9) (hj : j < 9) (hji : j ≠ i) :
    ¬ (∀ t, EndpointIntervalV3.InPeriodicInterval
          (circleAngle (centerDir (c i)) - capHalfWidth (c i) r)
          (circleAngle (centerDir (c i)) + capHalfWidth (c i) r) t →
        EndpointIntervalV3.InPeriodicInterval
          (circleAngle (centerDir (c j)) - capHalfWidth (c j) r)
          (circleAngle (centerDir (c j)) + capHalfWidth (c j) r) t) := by
  intro hsub
  refine not_cap_subset_of_covers hr0 hr1 hrR0 hcov hi hj hji ?_
  intro x hx hxi
  have hx' : circleMap (circleAngle x) = x := circleMap_circleAngle x hx
  have hIdI := EndpointIntervalV3.cap_mem_iff_periodicInterval (hcne i hi) hr0 hr1
    (hmeet i hi) (circleAngle x)
  have hIdJ := EndpointIntervalV3.cap_mem_iff_periodicInterval (hcne j hj) hr0 hr1
    (hmeet j hj) (circleAngle x)
  have hI : EndpointIntervalV3.InPeriodicInterval
      (circleAngle (centerDir (c i)) - capHalfWidth (c i) r)
      (circleAngle (centerDir (c i)) + capHalfWidth (c i) r) (circleAngle x) :=
    hIdI.mp (by rwa [hx'])
  simpa only [hx'] using hIdJ.mpr (hsub _ hI)

/-! ## §4  Full-type audit (`autoImplicit false` above makes this binding) -/

#check @N11Formalization.Essentiality.capPreimage
#check @N11Formalization.Essentiality.volumeReal_capPreimage_le
#check @N11Formalization.Essentiality.capPreimage_measure_ne_top
#check @N11Formalization.Essentiality.sixteen_arcsin_lt_two_pi_of_le_R0
#check @N11Formalization.Essentiality.exists_cap_exclusive_point
#check @N11Formalization.Essentiality.not_cap_subset_of_covers
#check @N11Formalization.Essentiality.not_interval_subset_of_covers

#print axioms N11Formalization.Essentiality.volumeReal_capPreimage_le
#print axioms N11Formalization.Essentiality.capPreimage_measure_ne_top
#print axioms N11Formalization.Essentiality.sixteen_arcsin_lt_two_pi_of_le_R0
#print axioms N11Formalization.Essentiality.exists_cap_exclusive_point
#print axioms N11Formalization.Essentiality.not_cap_subset_of_covers
#print axioms N11Formalization.Essentiality.not_interval_subset_of_covers

end

end N11Formalization.Essentiality
