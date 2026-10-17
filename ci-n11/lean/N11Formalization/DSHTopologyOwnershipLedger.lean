/-
  DSHTopologyOwnershipLedger.lean — DSH-TOPO-C2 (part B): the measure ledger for ownership
  of the active boundary arcs of an ACTUAL eleven-disk cover, plus the explicit degenerate
  branches.

  ## Content

  For the real cover domain (`Covers c r`, `Fin 11`, `BoundaryIdx` = the actual boundary
  disks, i.e. those whose closed disk meets `S¹`), with `0 ≤ r < 19/50`:

  * `ownership_ledger_actual` / `ownership_ledger_actual_R0` — **each boundary disk owns a
    POSITIVE angular measure, at most `2 arcsin r`, and the owned measures sum to `2π`.**
    Positivity is exactly "no boundary disk owns an empty arc": the counting engine
    (`8 * 2 arcsin r < 2π`) forces every one of the nine owned widths to be positive, so no
    boundary disk is redundant.  Sum `= 2π` is "no uncovered gap".
  * `sum_volumeReal_ownerSetB` — the ledger identity `∑ Δ i = 2π` (no cover hypothesis).
  * `capPreimage_volumeReal_pos` — hence each ACTUAL boundary arc has positive angular
    length: zero-length / antenna / tangent arcs cannot occur.
  * `not_exists_coincident_of_card_nine` — hence no two boundary disks have coincident
    centres (the higher-index one would own nothing, `ownerSetB_eq_empty_of_coincident`).
  * `unique_ownership_actual` — the headline assembly (conditional).

  ## Conditional premise (explicit, typed, NOT assumed silently)

  `Fintype.card (BoundaryIdx c r) = 9` — the exactly-nine-boundary-disk statement.  It is the
  job of the ten-boundary-exclusion line (C1, teammate `topo-ten-bdy`); here it is an
  explicit hypothesis of every theorem that needs it, so all those results are CONDITIONAL.
  Its unconditional half is available in the tree: `nine_le_card_boundary`
  (`Assembly/BoundaryCount.lean`) gives `9 ≤ card` for `0 ≤ r < 19/50` and `Covers c r`, so
  the premise reduces to the ten-boundary exclusion `card ≤ 10`.

  No `sorry`, no custom axiom, no `native_decide`.
-/
import Mathlib
import N11Formalization.DSHTopologyOwnership

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace N11Formalization.DSHTopologyOwnershipLedger

open MeasureTheory
open N11Formalization
open N11Formalization.DSHTopologyOwnership

noncomputable section

/-! ## §3  Cap measure and the boundary ownership ledger -/

/-- Angular preimage of the cap of a single disk (`(0, 2π)` chart). -/
def capPreimage (c : Point) (r : ℝ) : Set ℝ :=
  {t : ℝ | t ∈ Set.Ioo 0 (2 * Real.pi) ∧ dist (circleMap t) c ≤ r}

/-- Per-disk cap measure bound `≤ 2 arcsin r`.  (Proof is the inline argument of
`Geometry/ArcCovering.lean`'s counting theorem, restated in `Measure.real` form; it was
gated green as `OwnershipLedger.volumeReal_capPreimage_le`.) -/
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

theorem capPreimage_measure_ne_top {c : Point} {r : ℝ} : volume (capPreimage c r) ≠ ⊤ := by
  have hsub : capPreimage c r ⊆ Set.Ioo (0 : ℝ) (2 * Real.pi) := fun t ht => ht.1
  have hb : volume (capPreimage c r) ≤ ENNReal.ofReal (2 * Real.pi) := by
    calc volume (capPreimage c r) ≤ volume (Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
          measure_mono hsub
      _ = ENNReal.ofReal (2 * Real.pi) := by rw [Real.volume_Ioo, sub_zero]
  exact ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hb

/-- The owner of an angle is contained in its own cap (uses the actual cover). -/
theorem ownerSetB_subset_capPreimage {c : Fin 11 → Point} {r : ℝ} (hcov : Covers c r)
    (i : BoundaryIdx c r) : ownerSetB c r i ⊆ capPreimage (c i.1) r := by
  intro t ht
  obtain ⟨htI, hnear, -⟩ := ht
  obtain ⟨j, hj⟩ := hcov (circleMap t) (le_of_eq (circleMap_norm t))
  have hjB : MeetsCircle c r j := ⟨circleMap t, circleMap_norm t, hj⟩
  refine ⟨htI, ?_⟩
  have hsq : sqDist (c i.1) t ≤ sqDist (c j) t := hnear ⟨j, hjB⟩
  have h2 : dist (circleMap t) (c i.1) ^ 2 ≤ dist (circleMap t) (c j) ^ 2 := by
    rw [← sqDist_eq_dist_sq, ← sqDist_eq_dist_sq]
    exact hsq
  exact ((dist_le_dist_iff_sq (circleMap t) (c i.1) (c j)).mpr h2).trans hj

theorem ownerSetB_volumeReal_le {c : Fin 11 → Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcov : Covers c r) (i : BoundaryIdx c r) :
    volume.real (ownerSetB c r i) ≤ 2 * Real.arcsin r :=
  (measureReal_mono (ownerSetB_subset_capPreimage hcov i) capPreimage_measure_ne_top).trans
    (volumeReal_capPreimage_le hr0 hr1)

theorem measurableSet_ownerSetB (c : Fin 11 → Point) (r : ℝ) (i : BoundaryIdx c r) :
    MeasurableSet (ownerSetB c r i) := by
  classical
  have hle : ∀ j : BoundaryIdx c r,
      MeasurableSet {t : ℝ | sqDist (c i.1) t ≤ sqDist (c j.1) t} :=
    fun j => measurableSet_le (measurable_sqDist (c i.1)) (measurable_sqDist (c j.1))
  have hlt : ∀ j : BoundaryIdx c r,
      MeasurableSet {t : ℝ | sqDist (c i.1) t < sqDist (c j.1) t} :=
    fun j => measurableSet_lt (measurable_sqDist (c i.1)) (measurable_sqDist (c j.1))
  have h1 : MeasurableSet
      (⋂ j : BoundaryIdx c r, {t : ℝ | sqDist (c i.1) t ≤ sqDist (c j.1) t}) :=
    MeasurableSet.iInter hle
  have h2 : MeasurableSet
      (⋂ j : BoundaryIdx c r, {t : ℝ | j.1 < i.1 → sqDist (c i.1) t < sqDist (c j.1) t}) := by
    refine MeasurableSet.iInter (fun j => ?_)
    by_cases hj : j.1 < i.1
    · simpa [hj] using hlt j
    · simpa [hj] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
  have h3 : MeasurableSet (Set.Ioo (0 : ℝ) (2 * Real.pi)) := measurableSet_Ioo
  have hEq : ownerSetB c r i = Set.Ioo 0 (2 * Real.pi) ∩
      ((⋂ j : BoundaryIdx c r, {t : ℝ | sqDist (c i.1) t ≤ sqDist (c j.1) t}) ∩
        (⋂ j : BoundaryIdx c r,
          {t : ℝ | j.1 < i.1 → sqDist (c i.1) t < sqDist (c j.1) t})) := by
    ext t
    simp only [ownerSetB, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, OwnsB]
    try tauto
  rw [hEq]
  exact h3.inter (h1.inter h2)

/-- **The ownership ledger identity**: the owned angular measures of the boundary disks sum
to `2π` (partition of the fundamental interval; no cover hypothesis needed). -/
theorem sum_volumeReal_ownerSetB (c : Fin 11 → Point) (r : ℝ)
    (hne : (Finset.univ : Finset (BoundaryIdx c r)).Nonempty) :
    ∑ i : BoundaryIdx c r, volume.real (ownerSetB c r i) = 2 * Real.pi := by
  have hdisj : ∀ i j : BoundaryIdx c r, i ≠ j → Disjoint (ownerSetB c r i) (ownerSetB c r j) :=
    ownerSetB_pairwiseDisjoint c r
  have hmeas : ∀ i : BoundaryIdx c r, MeasurableSet (ownerSetB c r i) :=
    measurableSet_ownerSetB c r
  have hfin : ∀ i : BoundaryIdx c r, volume (ownerSetB c r i) ≠ ⊤ := by
    intro i
    have hsub : ownerSetB c r i ⊆ Set.Ioo (0 : ℝ) (2 * Real.pi) := fun t ht => ht.1
    have hb : volume (ownerSetB c r i) ≤ ENNReal.ofReal (2 * Real.pi) := by
      calc volume (ownerSetB c r i) ≤ volume (Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
            measure_mono hsub
        _ = ENNReal.ofReal (2 * Real.pi) := by rw [Real.volume_Ioo, sub_zero]
    exact ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hb
  have hsplit := measureReal_iUnion_fintype (μ := volume) (f := ownerSetB c r)
    (fun i j hij => hdisj i j hij) hmeas hfin
  have hvol : volume.real (Set.iUnion (fun i : BoundaryIdx c r => ownerSetB c r i))
      = 2 * Real.pi := by
    rw [iUnion_ownerSetB c r hne]
    rw [measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  rw [hvol] at hsplit
  exact hsplit.symm

/-- **The ownership ledger over the real cover (conditional on `card = 9`).**  Every boundary
disk owns a positive angular measure, at most `2 arcsin r`; positivity is what excludes
redundant / degenerate boundary disks. -/
theorem ownership_ledger_actual {c : Fin 11 → Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hr8 : 8 * Real.arcsin r < Real.pi) (hcov : Covers c r)
    (hcard : Fintype.card (BoundaryIdx c r) = 9) (i : BoundaryIdx c r) :
    0 < volume.real (ownerSetB c r i) ∧ volume.real (ownerSetB c r i) ≤ 2 * Real.arcsin r := by
  refine ⟨?_, ownerSetB_volumeReal_le hr0 hr1 hcov i⟩
  have hle : ∀ j : BoundaryIdx c r, volume.real (ownerSetB c r j) ≤ 2 * Real.arcsin r :=
    fun j => ownerSetB_volumeReal_le hr0 hr1 hcov j
  have hsum := sum_volumeReal_ownerSetB c r (boundaryIdx_nonempty_of_covers hcov)
  have hcard8 : (Finset.univ.erase i).card = 8 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hcard]
  have hothers : ∑ j ∈ Finset.univ.erase i, volume.real (ownerSetB c r j)
      ≤ 8 * (2 * Real.arcsin r) := by
    calc ∑ j ∈ Finset.univ.erase i, volume.real (ownerSetB c r j)
        ≤ ∑ _j ∈ Finset.univ.erase i, (2 * Real.arcsin r) := Finset.sum_le_sum fun j _ => hle j
      _ = ((Finset.univ.erase i).card : ℝ) * (2 * Real.arcsin r) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = 8 * (2 * Real.arcsin r) := by
            rw [hcard8]
            norm_num
  have hsplit : volume.real (ownerSetB c r i)
      + ∑ j ∈ Finset.univ.erase i, volume.real (ownerSetB c r j) = 2 * Real.pi := by
    rw [Finset.add_sum_erase (s := (Finset.univ : Finset (BoundaryIdx c r)))
      (f := fun j : BoundaryIdx c r => volume.real (ownerSetB c r j)) (a := i)
      (Finset.mem_univ i)]
    simpa using hsum
  linarith

/-- `8 arcsin r < π` from the canonical radius bound `r < 19/50`. -/
theorem eight_arcsin_lt_pi_of_lt_R0 {r : ℝ} (hr : r < (19 : ℝ) / 50) :
    8 * Real.arcsin r < Real.pi := by
  have h1 : Real.arcsin r ≤ Real.arcsin ((19 : ℝ) / 50) := Real.arcsin_le_arcsin hr.le
  linarith [eight_mul_arcsin_R0_lt_pi]

/-- Canonical form of `ownership_ledger_actual` at `r < 19/50`. -/
theorem ownership_ledger_actual_R0 {c : Fin 11 → Point} {r : ℝ} (hr0 : 0 ≤ r)
    (hrR0 : r < (19 : ℝ) / 50) (hcov : Covers c r)
    (hcard : Fintype.card (BoundaryIdx c r) = 9) (i : BoundaryIdx c r) :
    0 < volume.real (ownerSetB c r i) ∧ volume.real (ownerSetB c r i) ≤ 2 * Real.arcsin r :=
  ownership_ledger_actual hr0 (by linarith) (eight_arcsin_lt_pi_of_lt_R0 hrR0) hcov hcard i

/-! ## §4  Degenerate branches, handled explicitly -/

/-- **Coincident centres**: the higher-index of two boundary disks with the same centre never
owns any angle (the strict tie-break forces a strict inequality against an equal distance). -/
theorem ownsB_false_of_coincident {c : Fin 11 → Point} {r : ℝ} {i j : BoundaryIdx c r}
    (hlt : i.1 < j.1) (hcent : c i.1 = c j.1) (t : ℝ) : ¬ OwnsB c r j t := by
  intro h
  have h1 := h.2 i hlt
  rw [hcent] at h1
  exact lt_irrefl _ h1

theorem ownerSetB_eq_empty_of_coincident {c : Fin 11 → Point} {r : ℝ} {i j : BoundaryIdx c r}
    (hlt : i.1 < j.1) (hcent : c i.1 = c j.1) : ownerSetB c r j = ∅ := by
  ext t
  constructor
  · intro ht
    exact absurd ht.2 (ownsB_false_of_coincident hlt hcent t)
  · intro ht
    exact absurd ht (Set.notMem_empty t)

/-- **The nine-boundary-disk premise excludes coincident boundary centres.**  So the explicit
premise `card (BoundaryIdx c r) = 9` of the ledger is load-bearing, not cosmetic: with a
duplicated centre the ledger's strict positivity would fail. -/
theorem not_exists_coincident_of_card_nine {c : Fin 11 → Point} {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hr8 : 8 * Real.arcsin r < Real.pi) (hcov : Covers c r)
    (hcard : Fintype.card (BoundaryIdx c r) = 9) :
    ¬ ∃ i j : BoundaryIdx c r, i ≠ j ∧ c i.1 = c j.1 := by
  rintro ⟨i, j, hij, hcent⟩
  rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
  · have hempty := ownerSetB_eq_empty_of_coincident (r := r) hlt hcent
    have hpos := (ownership_ledger_actual hr0 hr1 hr8 hcov hcard j).1
    rw [hempty, measureReal_empty] at hpos
    exact lt_irrefl _ hpos
  · exact hij (Subtype.ext heq)
  · have hempty := ownerSetB_eq_empty_of_coincident (r := r) hgt hcent.symm
    have hpos := (ownership_ledger_actual hr0 hr1 hr8 hcov hcard i).1
    rw [hempty, measureReal_empty] at hpos
    exact lt_irrefl _ hpos

/-- **Every actual boundary arc has positive angular length.**  The owned part of the cap has
positive measure and is contained in the cap, so no zero-length / antenna / tangent boundary
arc survives the nine-disk premise. -/
theorem capPreimage_volumeReal_pos {c : Fin 11 → Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hr8 : 8 * Real.arcsin r < Real.pi) (hcov : Covers c r)
    (hcard : Fintype.card (BoundaryIdx c r) = 9) (i : BoundaryIdx c r) :
    0 < volume.real (capPreimage (c i.1) r) :=
  lt_of_lt_of_le (ownership_ledger_actual hr0 hr1 hr8 hcov hcard i).1
    (measureReal_mono (ownerSetB_subset_capPreimage hcov i) capPreimage_measure_ne_top)

/-! ## §5  Headline assembly -/

/-- **DSH-TOPO-C2 headline (conditional form).**  For an actual eleven-disk cover of the unit
disk with `0 ≤ r < 19/50` and exactly nine boundary disks:

  1. every point of `S¹` has EXACTLY ONE owning boundary disk, which is within `r` of it
     (no double ownership, no uncovered bubble/gap) — this part is unconditional in fact;
  2. every boundary disk owns a POSITIVE angular measure `≤ 2 arcsin r` (no redundant owner);
  3. every actual boundary arc has positive angular length (no degenerate/zero-length arc);
  4. the owned measures sum to `2π` (no gap);
  5. every angle has exactly one owning boundary disk (`∃!` on `(0,2π)`).

  The premise `Fintype.card (BoundaryIdx c r) = 9` is the ten-boundary exclusion (line C1),
  stated explicitly; the results are conditional on it. -/
theorem unique_ownership_actual {c : Fin 11 → Point} {r : ℝ} (hr0 : 0 ≤ r)
    (hrR0 : r < (19 : ℝ) / 50) (hcov : Covers c r)
    (hcard : Fintype.card (BoundaryIdx c r) = 9) :
    (∀ x : Point, ‖x‖ = 1 →
        ∃! i : Fin 11, MeetsCircle c r i ∧ OwnsPt c i x ∧ dist x (c i) ≤ r) ∧
    (∀ i : BoundaryIdx c r, 0 < volume.real (ownerSetB c r i) ∧
        volume.real (ownerSetB c r i) ≤ 2 * Real.arcsin r) ∧
    (∀ i : BoundaryIdx c r, 0 < volume.real (capPreimage (c i.1) r)) ∧
    (∑ i : BoundaryIdx c r, volume.real (ownerSetB c r i) = 2 * Real.pi) ∧
    (∀ t : ℝ, t ∈ Set.Ioo 0 (2 * Real.pi) →
        ∃! i : BoundaryIdx c r, OwnsB c r i t) := by
  have hne : (Finset.univ : Finset (BoundaryIdx c r)).Nonempty :=
    boundaryIdx_nonempty_of_covers hcov
  have hr1 : r < 1 := by linarith
  have hr8 : 8 * Real.arcsin r < Real.pi := eight_arcsin_lt_pi_of_lt_R0 hrR0
  exact ⟨unique_ownership_points hcov,
    fun i => ownership_ledger_actual hr0 hr1 hr8 hcov hcard i,
    fun i => capPreimage_volumeReal_pos hr0 hr1 hr8 hcov hcard i,
    sum_volumeReal_ownerSetB c r hne,
    fun t _ => ownsB_owner_existsUnique c r hne t⟩

/-! ## §6  Verbatim types and trusted base (for the §4 evidence pack) -/

#check @N11Formalization.DSHTopologyOwnership.OwnsPt
#check @N11Formalization.DSHTopologyOwnership.ownsPt_exists
#check @N11Formalization.DSHTopologyOwnership.ownsPt_unique
#check @N11Formalization.DSHTopologyOwnership.ownsPt_owner_existsUnique
#check @N11Formalization.DSHTopologyOwnership.ownsPt_ne_of_ne
#check @N11Formalization.DSHTopologyOwnership.ownsPt_dist_le_of_covers
#check @N11Formalization.DSHTopologyOwnership.ownsPt_meetsCircle_of_covers
#check @N11Formalization.DSHTopologyOwnership.Owns
#check @N11Formalization.DSHTopologyOwnership.ownerSet
#check @N11Formalization.DSHTopologyOwnership.owns_unique
#check @N11Formalization.DSHTopologyOwnership.ownsPt_iff_owns_circleAngle
#check @N11Formalization.DSHTopologyOwnership.ownerSet_pairwiseDisjoint
#check @N11Formalization.DSHTopologyOwnership.iUnion_ownerSet
#check @N11Formalization.DSHTopologyOwnership.OwnsB
#check @N11Formalization.DSHTopologyOwnership.ownerSetB
#check @N11Formalization.DSHTopologyOwnership.boundaryIdx_nonempty_of_covers
#check @N11Formalization.DSHTopologyOwnership.ownsB_exists
#check @N11Formalization.DSHTopologyOwnership.ownsB_unique
#check @N11Formalization.DSHTopologyOwnership.ownsB_owner_existsUnique
#check @N11Formalization.DSHTopologyOwnership.ownerSetB_pairwiseDisjoint
#check @N11Formalization.DSHTopologyOwnership.iUnion_ownerSetB
#check @N11Formalization.DSHTopologyOwnership.ownsB_iff_ownsPt
#check @N11Formalization.DSHTopologyOwnership.unique_ownership_points
#check @N11Formalization.DSHTopologyOwnership.exists_owner_covering
#check @N11Formalization.DSHTopologyOwnershipLedger.capPreimage
#check @N11Formalization.DSHTopologyOwnershipLedger.volumeReal_capPreimage_le
#check @N11Formalization.DSHTopologyOwnershipLedger.ownerSetB_subset_capPreimage
#check @N11Formalization.DSHTopologyOwnershipLedger.ownerSetB_volumeReal_le
#check @N11Formalization.DSHTopologyOwnershipLedger.sum_volumeReal_ownerSetB
#check @N11Formalization.DSHTopologyOwnershipLedger.ownership_ledger_actual
#check @N11Formalization.DSHTopologyOwnershipLedger.ownership_ledger_actual_R0
#check @N11Formalization.DSHTopologyOwnershipLedger.ownsB_false_of_coincident
#check @N11Formalization.DSHTopologyOwnershipLedger.ownerSetB_eq_empty_of_coincident
#check @N11Formalization.DSHTopologyOwnershipLedger.not_exists_coincident_of_card_nine
#check @N11Formalization.DSHTopologyOwnershipLedger.capPreimage_volumeReal_pos
#check @N11Formalization.DSHTopologyOwnershipLedger.unique_ownership_actual

#print axioms N11Formalization.DSHTopologyOwnership.ownsPt_exists
#print axioms N11Formalization.DSHTopologyOwnership.ownsPt_unique
#print axioms N11Formalization.DSHTopologyOwnership.ownsPt_iff_owns_circleAngle
#print axioms N11Formalization.DSHTopologyOwnership.ownsB_unique
#print axioms N11Formalization.DSHTopologyOwnership.ownsB_iff_ownsPt
#print axioms N11Formalization.DSHTopologyOwnership.unique_ownership_points
#print axioms N11Formalization.DSHTopologyOwnershipLedger.volumeReal_capPreimage_le
#print axioms N11Formalization.DSHTopologyOwnershipLedger.ownership_ledger_actual
#print axioms N11Formalization.DSHTopologyOwnershipLedger.not_exists_coincident_of_card_nine
#print axioms N11Formalization.DSHTopologyOwnershipLedger.unique_ownership_actual

end

end N11Formalization.DSHTopologyOwnershipLedger
