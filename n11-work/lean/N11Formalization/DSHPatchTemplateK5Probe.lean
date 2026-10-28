/-
DSHPatchTemplateK5Probe.lean -- DSH-PATCH-T0 NEGATIVE CONTROLS for the K5 sharp patch.

Companion probe to `DSHPatchTemplateK5.lean`.  Every statement here is meant to FAIL as a
mathematical claim, and each failure is traced to the intended mathematical reason, not to an
elaborator accident.  The controls are the three registered by patch-survey
(`evidence/dsh/patches/survey/negative-controls.json`) plus the mixed-remainder control required
by the handoff, in the survey/lead numbering:

  NC-A  row flip            : swapping the two hull rows / endpoints destroys the L2 containment
                              interface (`memberOK`).  (Case (1) of the survey controls; the
                              kernel-proved `Patch120K5Actual.wrong_orientation_rejected` is the
                              pin-row version.)
  NC-B  constant swap       : replacing the frozen radius `729/50000` by `1459/100000` (one part
                              in `10^5`) makes the C920 coefficient gate fail, so the sharp gain
                              can no longer follow from containment.
  NC-C  hull excludes cell  : the hull must actually CONTAIN the cell; raising hull index 0 by
                              1/512 excludes the cell endpoint and the member check fails.
  NC-D  replaced MIXED constant (handoff requirement): raising the mixed coefficient from the
                              ACTUAL `1468*((99/200)*(2/25)+429/50000) = 884103/12500` to `71`
                              (above the exact critical value) breaks the conclusion even though
                              BOTH separate blocks still hold -- positivity on two separate
                              blocks is NOT the mixed positivity.

NOT a valid failure control (stated here so nobody re-introduces it): narrowing the CELL's DBM
matrix `d` cannot be a negative control, because `Cell` is antitone in `d` (`d' <= d` pointwise
gives `Cell d' t -> Cell d t`).  NC-C is about the HULL failing to contain the cell endpoint,
which is a different object.  See `gates_phase1.ps1` / `NOTES.md`.

Calibration of the exact rationals is in `verify_sharpness.py` / `verify_sharpness.out.txt`
(exact Fraction arithmetic, no floats).
-/
import N11Formalization.DSHPatchTemplateK5

set_option autoImplicit false
set_option maxRecDepth 10000

namespace N11Formalization.DSHPatchTemplate.K5Probe

open N11Formalization
open N11Formalization.Patch120K5
open N11Formalization.Patch120K5Actual
open N11Formalization.ResumeRelativeScalar

noncomputable section

/-! ## NC-A: row flip -- the hull rows may not be swapped -/

/-- Row 0 of the lower hull is exactly attained by the cell's own DBM row (tight). -/
theorem db4935_zero_six : db4935 (0 : Fin 10) (6 : Fin 10) = (267 / 512 : ℚ) := by
  decide +kernel

theorem k5lo_zero_tight : k5lo (0 : Fin 9) = -db4935 (0 : Fin 10) (6 : Fin 10) := by
  rw [db4935_zero_six, k5lo_0]
  norm_num

/-- Row 0 of the upper hull is exactly attained by the cell's own DBM row (tight). -/
theorem db4935_six_zero : db4935 (6 : Fin 10) (0 : Fin 10) = (-33 / 64 : ℚ) := by
  decide +kernel

theorem k5hi_zero_tight : k5hi (0 : Fin 9) = db4935 (6 : Fin 10) (0 : Fin 10) := by
  rw [db4935_six_zero, k5hi_0]

/-- NC-C domain: the hull with index 0 raised by 1/512 (`-267/512 -> -266/512`), i.e. a hull
that NO LONGER CONTAINS the cell endpoint. -/
def k5loNarrow : Fin 9 → ℚ := fun i => if (i : ℕ) = 0 then (-133 / 256 : ℚ) else k5lo i

theorem k5loNarrow_zero : k5loNarrow (0 : Fin 9) = (-133 / 256 : ℚ) := by
  simp [k5loNarrow]

/-- **NC-C**: a hull that excludes the cell endpoint FAILS the L2 containment interface, at
index 0 (the tight row).  Intended mathematical reason: the hull endpoint is exactly the cell's
row value, so the hull cannot be raised at all. -/
theorem hull_excludes_cell_rejected : ¬ memberOK k5loNarrow k5hi db4935 := by
  unfold memberOK
  decide +kernel

/-- NC-C, right-reason witness: the failure is the index-0 lower row inequality
(`-266/512 <= -267/512` is false). -/
theorem hull_excludes_cell_failure_witness :
    ¬ (k5loNarrow (0 : Fin 9) ≤ -db4935 (0 : Fin 10) (6 : Fin 10)) := by
  rw [k5loNarrow_zero, db4935_zero_six]
  norm_num

/-- **NC-A**: swapping the hull endpoints (row flip) also destroys the interface. -/
theorem flipped_endpoints_rejected : ¬ memberOK k5hi k5lo db4935 := by
  unfold memberOK
  decide +kernel

/-- NC-A, right-reason witness: with flipped endpoints the index-0 lower inequality reads
`-33/64 <= -267/512`, which is false. -/
theorem flipped_endpoints_failure_witness :
    ¬ (k5hi (0 : Fin 9) ≤ -db4935 (0 : Fin 10) (6 : Fin 10)) := by
  rw [k5hi_0, db4935_zero_six]
  norm_num

/-- The documented consequence: `memberOK` is exactly the hypothesis of
`Patch120K5.cell_in_hull`, hence the only route from the emitted tree rows to the L2
containment box.  A hull that excludes the cell therefore loses L2 outright. -/
theorem hull_excludes_cell_breaks_L2 :
    ¬ (∀ i : Fin 9, i ≠ 6 → k5loNarrow i ≤ -db4935 (f9 i) (6 : Fin 10)) := by
  decide +kernel

/-! ## NC-B: constant swap -- enlarging the frozen radius -/

/-- **NC-B**: at radius `1459/100000` (one part in `10^5` above the frozen `729/50000`) the C920
coefficient gate fails: `coefficient (1459/100000) < 1/100000`.  Intended mathematical reason:
the gain `q^2/100000 <= E` is produced by the coefficient gate, so a larger containment radius
cannot pay it.  (Same threshold as `ResumeRelativeScalar.rounded_radius_rejected`.) -/
theorem enlarged_radius_rejected : coefficient (1459 / 100000 : ℝ) < (1 / 100000 : ℝ) := by
  norm_num [coefficient]

/-- NC-B, quantified form: with the enlarged radius the sharp gain fails at an explicit `q`. -/
theorem enlarged_radius_gain_fails :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ (1459 / 100000 : ℝ)
      ∧ coefficient q * q ^ 2 < q ^ 2 / 100000 := by
  refine ⟨1459 / 100000, by norm_num, le_rfl, ?_⟩
  have h := enlarged_radius_rejected
  have hq : (0 : ℝ) < (1459 / 100000) ^ 2 := by norm_num
  have hm := mul_lt_mul_of_pos_right h hq
  linarith [hm]

/-- NC-B sanity: the FROZEN radius is on the correct side of the same threshold. -/
theorem frozen_radius_gate_holds : (1 / 100000 : ℝ) < coefficient (729 / 50000) := by
  norm_num [coefficient]

/-! ## NC-D: replaced MIXED constant -- separate blocks do NOT give mixed positivity -/

/-- The replaced mixed coefficient: `71` instead of the actual
`1468*((99/200)*(2/25)+429/50000) = 884103/12500 = 70.72824`. -/
def Mbad : ℝ := 71

theorem actual_mixed_coefficient : (1468 : ℝ) * ((99 / 200) * (2 / 25) + 429 / 50000)
    = 884103 / 12500 := by norm_num

theorem Mbad_gt_actual_mixed : (1468 : ℝ) * ((99 / 200) * (2 / 25) + 429 / 50000) < Mbad := by
  norm_num [Mbad]

/-- The EXACT critical mixed coefficient squared: solving
`(9/10000)q^2 - C q^3 - (d/3)q^4 - M^2 q^4/(4*734) = q^2/100000` at `q = 729/50000` gives
`M_crit^2 = 66494398816/13286025 = 5004.8377...`, and `Mbad^2 = 5041` exceeds it.  The actual
coefficient sits only `0.047%` (in `M^2`) below the critical value -- the mixed constant is
genuinely sharp, not slack. -/
theorem Mbad_exceeds_critical_sq : (66494398816 / 13286025 : ℝ) < Mbad ^ 2 := by
  norm_num [Mbad]

/-- **NC-D.** There are `q, p, E` inside the frozen containment interval for which BOTH
separate blocks hold --
  block 1: `(1/100000) q^2 <= (9/10000) q^2 - (179/5000) q^3 - ((2/25)/3) q^4` (the
           cubic/quartic remainder block is bounded by the sharp gain at this `q`), and
  block 2: `0 <= 734 p^2` (the p-block is positive) --
and the mixed form with the REPLACED coefficient `Mbad` is still `<= E`, while the conclusion
`q^2/100000 <= E` FAILS.  Intended mathematical reason: with `M > M_crit` the p-block can no
longer absorb the mixed term (`734(p - K q^2)^2` is no longer the exact completion), so the
mixed block genuinely needs its own argument; two separately positive blocks are not enough. -/
theorem separate_blocks_do_not_imply_mixed :
    ∃ q p E : ℝ,
      0 ≤ q ∧ q ≤ (729 / 50000 : ℝ) ∧
      (1 / 100000 : ℝ) * q ^ 2
        ≤ (9 / 10000 : ℝ) * q ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4 ∧
      0 ≤ 734 * p ^ 2 ∧
      (9 / 10000 : ℝ) * q ^ 2 + 734 * p ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4
        - Mbad * p * q ^ 2 ≤ E ∧
      ¬ (q ^ 2 / 100000 ≤ E) := by
  refine ⟨729 / 50000, 37732311 / 3670000000000, 1 / 500000000,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num [Mbad]
  · norm_num

/-- **NC-D, implication form.** The naive inference "two separately positive blocks plus a
mixed-form bound give the sharp gain" is FALSE once the mixed coefficient is replaced. -/
theorem naive_mixed_inference_false :
    ¬ (∀ q p E : ℝ, 0 ≤ q → q ≤ (729 / 50000 : ℝ) →
        (1 / 100000 : ℝ) * q ^ 2
          ≤ (9 / 10000 : ℝ) * q ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4 →
        0 ≤ 734 * p ^ 2 →
        (9 / 10000 : ℝ) * q ^ 2 + 734 * p ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4
          - Mbad * p * q ^ 2 ≤ E →
        q ^ 2 / 100000 ≤ E) := by
  intro h
  obtain ⟨q, p, E, hq, hr, hb1, hb2, hmix, hconcl⟩ := separate_blocks_do_not_imply_mixed
  exact hconcl (h q p E hq hr hb1 hb2 hmix)

/-- **NC-D positive companion.** With the ACTUAL mixed coefficient the same data DO give the
conclusion, unconditionally, at every `q` in the frozen interval and every `p` -- because the
mixed term is exactly a square completion (L3-a) and the coefficient gate (L3-b) holds. -/
theorem actual_mixed_coefficient_works {q p : ℝ} (hq : 0 ≤ q) (hr : q ≤ 729 / 50000) :
    (1 / 100000 : ℝ) * q ^ 2
      ≤ (9 / 10000 : ℝ) * q ^ 2 + 734 * p ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4
        - 1468 * ((99 / 200) * (2 / 25) + 429 / 50000) * p * q ^ 2 := by
  have hcomp := N11Formalization.DSHPatchTemplate.K5.mixed_remainder_completion q p
  have hc := coefficient_gt hq hr
  have hmul : (1 / 100000 : ℝ) * q ^ 2 ≤ coefficient q * q ^ 2 :=
    mul_le_mul_of_nonneg_right hc.le (sq_nonneg q)
  have hs : 0 ≤ 734 * (p - ((99 / 200) * (2 / 25) + 429 / 50000) * q ^ 2) ^ 2 := by positivity
  linarith [hcomp, hmul, hs]

end

end N11Formalization.DSHPatchTemplate.K5Probe

#check @N11Formalization.DSHPatchTemplate.K5Probe.k5lo_zero_tight
#check @N11Formalization.DSHPatchTemplate.K5Probe.hull_excludes_cell_rejected
#check @N11Formalization.DSHPatchTemplate.K5Probe.flipped_endpoints_rejected
#check @N11Formalization.DSHPatchTemplate.K5Probe.enlarged_radius_gain_fails
#check @N11Formalization.DSHPatchTemplate.K5Probe.Mbad_exceeds_critical_sq
#check @N11Formalization.DSHPatchTemplate.K5Probe.separate_blocks_do_not_imply_mixed
#check @N11Formalization.DSHPatchTemplate.K5Probe.naive_mixed_inference_false
#check @N11Formalization.DSHPatchTemplate.K5Probe.actual_mixed_coefficient_works
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.hull_excludes_cell_rejected
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.hull_excludes_cell_failure_witness
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.hull_excludes_cell_breaks_L2
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.flipped_endpoints_rejected
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.flipped_endpoints_failure_witness
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.enlarged_radius_rejected
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.enlarged_radius_gain_fails
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.Mbad_exceeds_critical_sq
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.separate_blocks_do_not_imply_mixed
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.naive_mixed_inference_false
#print axioms N11Formalization.DSHPatchTemplate.K5Probe.actual_mixed_coefficient_works
