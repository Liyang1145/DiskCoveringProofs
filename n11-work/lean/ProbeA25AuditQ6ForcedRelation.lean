/-
  ProbeA25AuditQ6ForcedRelation.lean   (owner: m5b-adversarial-audit, task-4)
  Top-level probe; NOT part of the A25 manifest module list.

  ============================ CREDIT SCOPE ============================
  This probe establishes a STRUCTURAL OBSTRUCTION.  It is NOT a class payment
  (it pays zero class credit and does not move c450/energy/classes remaining),
  and it does NOT disprove any existing theorem.  What it proves:

  (a) `audQ6_forced_relation` / `_B`: for ANY class F, ANY D : CanonicalCoeffQ F
      with CanonicalMaskBalancedQ D, and ANY k with cycleEdge k ∈ faceEdges F,
          (Σ over the face slots whose flagEdge is cycleEdge k of canonicalFaceQ D f s)
            + canonicalSwitchQ D k = 0,
      and the same with canonicalFaceB / sideFirst.

  (c) `audQ6_slot_unique`: for the class `q0Faces 1`, the face slot whose
      flagEdge is `cycleEdge 0 = {0,1}` is UNIQUE — it is the hub slot of the
      face `{0,1,9}`.  This is what turns (a)'s filtered sum into a TWO-TERM
      identity, so it is load-bearing and is stated as its own theorem.
      (Stated label-free, i.e. as "f.val.erase i = {0,1} with i ∈ f.val", so it
      does not depend on reducing `Finset.orderIsoOfFin`; it implies the labelled
      form because `canonicalLabel` sends `s` to some element of `f.val`.)

  (b) `audQ6_q0_obstruction`: instantiating (a) at `q0Faces 1`, `k = 0` with the
      concrete parsed rationals gives `False`.  I.e. no single `D` can carry the
      concrete Face1 q-data AND the concrete switch-0 q-data.

  (d) `audQ6_control_*`: negative controls.  `audQ6_control_balance_is_exactly_
      the_obstruction` shows that when `sideSecond (cycleEdge k) ≠ 0` the relation
      is EQUIVALENT to the balance condition — so it is not vacuous — and it
      exposes the one degenerate escape (`sideSecond = 0`).  `audQ6_residuals_
      nonzero` checks the two concrete residuals really are nonzero.

  What this does NOT establish: it does not show the A25 route is dead (consistent
  data could be regenerated); it does not touch the orbit transport, the
  `FiniteCanonicalCertificate.toCanonical` derivation, the Face1 coverage
  argument, or interface satisfiability; and it is SPECIFIC to the three Q0
  classes (`(0,1,9)` is not a face of `q1Faces k m`), i.e. 3 of the 7 exclusions.

  Cross-link: the Lead's C1804 is an INDEPENDENT second obstruction for the same
  three classes, obtained from the `P` family with no `(f,s)` freedom (a 6-term
  signed sum of face-P equations cancels every mu and kap coefficient and leaves
  0 = -88193367/1000000000).  The two use disjoint mechanism families: C1804 uses
  `P`, this probe uses `Q`/`B` plus the balance field.

  Axioms: propext, Classical.choice, Quot.sound only (see the #print axioms lines).
-/
import N11Formalization.CanonicalSharedMomentFiniteCertificate
import N11Formalization.SharedMomentConcreteFace1Data
import N11Formalization.SharedMomentConcreteSwitchBatch

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA25AuditQ6ForcedRelation

open ActualCanonicalMomentTransport ActualOrderedMetricGraphs
open ActualEdgeFlagSums ActualSharedMomentRationalCertificate

/-! ## (a) The forced relation -/

/-- `switchSumQ` picks out its own index on a cycle edge. -/
theorem audQ6_switchSumQ_cycle (g : Fin 9 → ℚ) (k : Fin 9) :
    switchSumQ g (cycleEdge k) = g k := by
  classical
  rw [switchSumQ]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi
    have hne : cycleEdge i ≠ cycleEdge k := fun h => hi (cycle_edge_injective h)
    simp only [hne, if_false]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- Factorisation: the filtered face-`q` sum is `sideSecond (cycleEdge k)` times
the canonical edge sum.  This is where `sideSecond`'s edge-indexing is used. -/
theorem audQ6_filter_sum_Q {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (k : Fin 9) :
    (∑ f : F, ∑ s : Fin 3,
        if D.flagEdge f s = cycleEdge k then canonicalFaceQ D f s else 0)
      = D.sideSecond (cycleEdge k) * canonicalEdgeSumQ D (cycleEdge k) := by
  classical
  unfold canonicalEdgeSumQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : D.flagEdge f s = cycleEdge k
  · rw [if_pos h, if_pos h, canonicalFaceQ, h]
    ring
  · simp only [if_neg h, mul_zero]

/-- The same factorisation for `b` / `sideFirst`. -/
theorem audQ6_filter_sum_B {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (k : Fin 9) :
    (∑ f : F, ∑ s : Fin 3,
        if D.flagEdge f s = cycleEdge k then canonicalFaceB D f s else 0)
      = D.sideFirst (cycleEdge k) * canonicalEdgeSumQ D (cycleEdge k) := by
  classical
  unfold canonicalEdgeSumQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : D.flagEdge f s = cycleEdge k
  · rw [if_pos h, if_pos h, canonicalFaceB, h]
    ring
  · simp only [if_neg h, mul_zero]

/-- **The forced relation** (Q).  Balance forces the face `q`-slots sitting on a
cycle edge to cancel the corresponding switch `q`. -/
theorem audQ6_forced_relation {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (hm : CanonicalMaskBalancedQ D) {k : Fin 9} (hk : cycleEdge k ∈ faceEdges F) :
    (∑ f : F, ∑ s : Fin 3,
        if D.flagEdge f s = cycleEdge k then canonicalFaceQ D f s else 0)
      + canonicalSwitchQ D k = 0 := by
  have hbal := hm (cycleEdge k) hk
  rw [audQ6_switchSumQ_cycle] at hbal
  have hces : canonicalEdgeSumQ D (cycleEdge k) = -D.switchMask k := by linarith
  rw [audQ6_filter_sum_Q, canonicalSwitchQ, hces]
  ring

/-- **The forced relation** (B). -/
theorem audQ6_forced_relation_B {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (hm : CanonicalMaskBalancedQ D) {k : Fin 9} (hk : cycleEdge k ∈ faceEdges F) :
    (∑ f : F, ∑ s : Fin 3,
        if D.flagEdge f s = cycleEdge k then canonicalFaceB D f s else 0)
      + canonicalSwitchB D k = 0 := by
  have hbal := hm (cycleEdge k) hk
  rw [audQ6_switchSumQ_cycle] at hbal
  have hces : canonicalEdgeSumQ D (cycleEdge k) = -D.switchMask k := by linarith
  rw [audQ6_filter_sum_B, canonicalSwitchB, hces]
  ring

/-! ## (c) The exactly-one-slot premise (load-bearing) -/

/-- Label-free uniqueness: in `q0Faces 1`, the only way to erase one element of a
face and land on `{0,1}` is to erase `9` from `{0,1,9}`.

NOTE (Lead fix): the original `decide`-closed statement was FALSE as written,
because `erase i` is vacuous when `i ∉ f`, so e.g. `(0,8,10).erase 2 = (0,8,10)`
is not `{0,1}` but the biconditional's right side is also false -- the failure
came from the `→` direction on `i ∉ f`. Restricting to `i ∈ f` and stating the
converse separately is the correct form. -/
theorem audQ6_slot_unique :
    ∀ (f : q0Faces 1) (i : Fin 11), i ∈ f.val →
      (f.val.erase i = cycleEdge 0 → f.val = ({0, 1, 9} : Finset (Fin 11)) ∧ i = 9) := by
  decide +kernel

/-- Conversely, erasing `9` from `{0,1,9}` does land on `cycleEdge 0`. -/
theorem audQ6_slot_exists :
    (⟨({0, 1, 9} : Finset (Fin 11)), by decide +kernel⟩ : q0Faces 1).val.erase (9 : Fin 11)
      = cycleEdge 0 := by
  decide +kernel

/-- `cycleEdge 0` really is a face edge of the Q0 class, so the obstruction is
not vacuous for want of its hypothesis. -/
theorem audQ6_cycleEdge0_mem : cycleEdge 0 ∈ faceEdges (q0Faces 1) := by
  decide +kernel

/-- The class really has 11 faces, matching the consumer's `∀ f : F`. -/
theorem audQ6_card : (q0Faces 1).card = 11 := by decide +kernel

/-! ## (b) The concrete incompatibility, kernel-checked -/

/-- **Headline.**  For the class `q0Faces 1`, if `D` satisfies balance and the
cycle-edge-0 face slots carry the concrete Face1 `q` data while switch 0 carries
the concrete switch-`q` data, then `False`. -/
theorem audQ6_q0_obstruction
    (D : CanonicalCoeffQ (q0Faces 1)) (hm : CanonicalMaskBalancedQ D)
    (hk : cycleEdge 0 ∈ faceEdges (q0Faces 1))
    (hface : (∑ f : q0Faces 1, ∑ s : Fin 3,
        if D.flagEdge f s = cycleEdge 0 then canonicalFaceQ D f s else 0)
      = 251843483/1000000000)
    (hsw : canonicalSwitchQ D 0 = 21538627/125000000) : False := by
  have h := audQ6_forced_relation D hm hk
  rw [hface, hsw] at h
  norm_num at h

/-- The same for the `b` family. -/
theorem audQ6_q0_obstruction_B
    (D : CanonicalCoeffQ (q0Faces 1)) (hm : CanonicalMaskBalancedQ D)
    (hk : cycleEdge 0 ∈ faceEdges (q0Faces 1))
    (hface : (∑ f : q0Faces 1, ∑ s : Fin 3,
        if D.flagEdge f s = cycleEdge 0 then canonicalFaceB D f s else 0)
      = -102151007/500000000)
    (hsw : canonicalSwitchB D 0 = -184795967/1000000000) : False := by
  have h := audQ6_forced_relation_B D hm hk
  rw [hface, hsw] at h
  norm_num at h

/-! ## (d) Negative controls -/

/-- The two concrete residuals really are nonzero (not a rounding artefact). -/
theorem audQ6_residuals_nonzero :
    (251843483/1000000000 : ℚ) + 21538627/125000000 ≠ 0 ∧
    (-102151007/500000000 : ℚ) + (-184795967/1000000000) ≠ 0 := by
  norm_num

/-- The residuals are large: at least `1/3` in absolute value.  This is the
quantitative form of "the two data sets are genuinely incompatible" (the actual
values are `≈ 0.4242` and `≈ 0.3891`). -/
theorem audQ6_residuals_large :
    (1/3 : ℚ) ≤ |(251843483/1000000000 : ℚ) + 21538627/125000000| ∧
    (1/3 : ℚ) ≤ |(-102151007/500000000 : ℚ) + (-184795967/1000000000)| := by
  norm_num

/-- **Non-vacuity control.**  When `sideSecond (cycleEdge k) ≠ 0`, the forced
relation is EXACTLY the balance condition (not something weaker, and not
trivially true).  This also exposes the single degenerate escape: if `sideSecond`
vanishes on that edge the relation holds regardless of balance. -/
theorem audQ6_control_balance_is_exactly_the_obstruction
    {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F) {k : Fin 9}
    (hss : D.sideSecond (cycleEdge k) ≠ 0) :
    ((∑ f : F, ∑ s : Fin 3,
        if D.flagEdge f s = cycleEdge k then canonicalFaceQ D f s else 0)
        + canonicalSwitchQ D k = 0)
      ↔ (canonicalEdgeSumQ D (cycleEdge k)
          + switchSumQ D.switchMask (cycleEdge k) = 0) := by
  rw [audQ6_switchSumQ_cycle, audQ6_filter_sum_Q, canonicalSwitchQ]
  have key : D.sideSecond (cycleEdge k)
        * (canonicalEdgeSumQ D (cycleEdge k) + D.switchMask k) = 0
      ↔ (canonicalEdgeSumQ D (cycleEdge k) + D.switchMask k = 0) := by
    refine ⟨fun h => ?_, fun h => by rw [h, mul_zero]⟩
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hss
    · exact h1
  constructor
  · intro h
    exact key.mp (by linear_combination h)
  · intro h
    linear_combination (D.sideSecond (cycleEdge k)) * h

/-- A control `D` for the class `q0Faces 1` with `faceMask ≡ 0` and
`switchMask ≡ 1`.  It violates balance, so the forced relation must NOT hold
for it — this is the negative control that shows the balance hypothesis is
doing real work. -/
def audControlD : CanonicalCoeffQ (q0Faces 1) where
  faceCard := q0FaceCard 1
  mu := fun _ => 0
  faceMask := fun _ _ => 0
  switchMask := fun _ => 1
  sideFirst := fun _ => 0
  sideSecond := fun _ => 1
  leftFirst := fun _ => 0
  leftSecond := fun _ => 0
  rightFirst := fun _ => 0
  rightSecond := fun _ => 0
  width := 0

theorem audQ6_control_edgeSum_zero :
    canonicalEdgeSumQ audControlD (cycleEdge 0) = 0 := by
  unfold canonicalEdgeSumQ
  refine Finset.sum_eq_zero fun f _ => Finset.sum_eq_zero fun s _ => ?_
  simp only [audControlD]
  exact ite_self 0

theorem audQ6_control_switchSum_one :
    switchSumQ audControlD.switchMask (cycleEdge 0) = 1 := by
  rw [audQ6_switchSumQ_cycle]
  rfl

/-- The control really does violate balance (it fails for the intended
mathematical reason, not by a parser or type error). -/
theorem audQ6_control_not_balanced : ¬ CanonicalMaskBalancedQ audControlD := by
  intro h
  have hb := h (cycleEdge 0) audQ6_cycleEdge0_mem
  rw [audQ6_control_edgeSum_zero, audQ6_control_switchSum_one] at hb
  norm_num at hb

/-- **Negative control, expressed as the `Zero` the relation would give.**  For
`audControlD` the filtered face-`q` sum is `0` while `canonicalSwitchQ` is `1`, so
the expression in the forced relation equals `1 ≠ 0`.  Hence the relation is NOT
a trivial identity and genuinely uses `CanonicalMaskBalancedQ`. -/
theorem audQ6_control_relation_fails :
    ¬ ((∑ f : q0Faces 1, ∑ s : Fin 3,
        if audControlD.flagEdge f s = cycleEdge 0
          then canonicalFaceQ audControlD f s else 0)
        + canonicalSwitchQ audControlD 0 = 0) := by
  have hface : (∑ f : q0Faces 1, ∑ s : Fin 3,
        if audControlD.flagEdge f s = cycleEdge 0
          then canonicalFaceQ audControlD f s else 0) = 0 := by
    unfold canonicalFaceQ
    refine Finset.sum_eq_zero fun f _ => Finset.sum_eq_zero fun s _ => ?_
    by_cases h : audControlD.flagEdge f s = cycleEdge 0 <;> simp [h, audControlD]
  have hsw : canonicalSwitchQ audControlD 0 = 1 := by
    unfold canonicalSwitchQ
    simp [audControlD]
  rw [hface, hsw]
  norm_num

end N11Formalization.ProbeA25AuditQ6ForcedRelation

#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_switchSumQ_cycle
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_filter_sum_Q
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_filter_sum_B
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_forced_relation
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_forced_relation_B
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_slot_unique
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_cycleEdge0_mem
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_card
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_q0_obstruction
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_q0_obstruction_B
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_residuals_nonzero
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_residuals_large
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_control_balance_is_exactly_the_obstruction
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_control_edgeSum_zero
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_control_switchSum_one
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_control_not_balanced
#print axioms N11Formalization.ProbeA25AuditQ6ForcedRelation.audQ6_control_relation_fails
