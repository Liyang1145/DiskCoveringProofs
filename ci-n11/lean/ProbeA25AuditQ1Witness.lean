/-
  ProbeA25AuditQ1Witness.lean   (owner: m5b-adversarial-audit, task-4)
  Top-level probe; NOT part of the A25 manifest module list.

  ============================ CREDIT SCOPE ============================
  This probe is a NON-VACUITY / SATISFIABILITY result for the A25 CONSUMER
  INTERFACE ONLY.  It exhibits concrete rational coefficient data at which
  every field of `ActualCanonicalSharedMomentConsumer.CanonicalCertificate`
  EXCEPT the semantic field `bounds : CanonicalFactorBounds` is discharged,
  and at which the strict field
      canonicalTotalUpperQ D kap eta alpha faceMax switchMax sectorMax < RatInterval.piLo
  HOLDS.  The semantic bounds are deliberately LEFT OUT and named as the
  remaining obligation (see `audInterfaceNonvacuous`).  A witness with freely
  chosen faceMax/switchMax/sectorMax is NOT a payable class table: it does not
  show that any concrete A25 finite leaf tree can produce those maxima, and it
  pays zero class credit.  What it does show is that the A25 exclusion route is
  not vacuous for the trivial reason of an unsatisfiable strict field.

  NEGATIVE CONTROL (same file, `audBadStrictFails`): for a DIFFERENT concrete
  rational datum the SAME strict inequality is FALSE, kernel-checked as a `¬`.
  So the positive arm is sensitive to the strict field and does not pass
  vacuously.

  Axioms: propext, Classical.choice, Quot.sound only (see the #print axioms
  lines at the end of this file).
-/
import N11Formalization.ActualCanonicalSharedMomentConsumer

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA25AuditQ1Witness

open ActualCanonicalSharedMomentConsumer ActualCanonicalMomentTransport
open ActualOrderedMetricGraphs ActualSharedMomentSharpConstant
open ActualSharedMomentRationalCertificate MetricAreaRationalCertificate

/-- The audited class: `q0Faces 1`, the Q0 degree-3 class, 11 faces. -/
abbrev audF : Finset (Finset (Fin 11)) := q0Faces 1

/-- Witness coefficient `mu` (all rationals). -/
def audMu : Fin 11 → ℚ :=
  ![11/2000, 11/2000, -17/1000, -31/2000, -31/2000, -31/2000, -31/2000,
    -31/2000, -17/1000, -49/1000, 193/2000]

/-- Witness coefficients: `mu` as above, `width = 0`, and every structural
coefficient identically zero.  With all masks zero, `CanonicalMaskBalancedQ`
holds identically (`audBalanced`). -/
def audD : CanonicalCoeffQ audF where
  faceCard := q0FaceCard 1
  mu := audMu
  faceMask := fun _ _ => 0
  switchMask := fun _ => 0
  sideFirst := fun _ => 0
  sideSecond := fun _ => 0
  leftFirst := fun _ => 0
  leftSecond := fun _ => 0
  rightFirst := fun _ => 0
  rightSecond := fun _ => 0
  width := 0

def audKap : Finset (Fin 11) → ℚ := fun _ => 0
def audFaceMax : audF → ℚ := fun _ => 3/20
def audSwitchMax : Fin 9 → ℚ := fun _ => 1/20
def audSectorMax : Fin 9 → ℚ := fun _ => 1/10

theorem audCard : audF.card = 11 := by decide +kernel

theorem audStation : canonicalStationCoeffQ audD = -11/2000 := by decide +kernel

theorem audConst : canonicalConstantCoeffQ audD audKap 0 = -11/2000 := by
  rw [canonicalConstantCoeffQ, audStation]
  simp [audD, audKap]

theorem audFaceSum : (∑ f : audF, audFaceMax f) = 33/20 := by decide +kernel

theorem audSwitchSum : (∑ i : Fin 9, audSwitchMax i) = 9/20 := by decide +kernel

theorem audSectorSum : (∑ i : Fin 9, audSectorMax i) = 9/10 := by decide +kernel

/-- POSITIVE ARM: the strict field holds at the witness data. -/
theorem audStrict :
    canonicalTotalUpperQ audD audKap 0 sharpAlpha audFaceMax audSwitchMax audSectorMax
      < RatInterval.piLo := by
  rw [canonicalTotalUpperQ, canonicalSharpConstantUpperQ, audConst, audFaceSum,
    audSwitchSum, audSectorSum]
  norm_num [piProductUpper, RatInterval.piLo, RatInterval.piHi, sharpAlpha]

/-- With `faceMask ≡ 0` the flag sum vanishes identically. -/
theorem audEdgeSumZero (e : Finset (Fin 11)) : canonicalEdgeSumQ audD e = 0 := by
  rw [canonicalEdgeSumQ]
  refine Finset.sum_eq_zero (fun f _ => ?_)
  refine Finset.sum_eq_zero (fun s _ => ?_)
  simp only [audD, CanonicalCoeffQ.flagEdge]
  exact ite_self 0

/-- With `switchMask ≡ 0` the cyclic-switch sum vanishes identically. -/
theorem audSwitchSumZero (e : Finset (Fin 11)) : switchSumQ audD.switchMask e = 0 := by
  rw [switchSumQ]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  simp only [audD]
  exact ite_self 0

theorem audBalanced : CanonicalMaskBalancedQ audD := by
  intro e _
  rw [audEdgeSumZero, audSwitchSumZero, add_zero]

/-- NON-VACUITY: `CanonicalCertificate` minus its semantic field `bounds` is
inhabited at concrete rational data.  The remaining obligation is exactly
`CanonicalFactorBounds audD audKap 0 0 audFaceMax audSwitchMax audSectorMax`,
i.e. the per-face/per-switch/per-sector semantic upper bounds that the A25
finite leaf trees are supposed to supply. -/
theorem audInterfaceNonvacuous :
    ∃ faceMax : audF → ℚ, ∃ switchMax sectorMax : Fin 9 → ℚ,
      CanonicalMaskBalancedQ audD ∧
      (∀ e ∈ faceEdges audF, 0 ≤ audKap e) ∧
      (0 : ℚ) ≤ 0 ∧
      EarAsinBracket sharpAlpha ∧
      canonicalTotalUpperQ audD audKap 0 sharpAlpha faceMax switchMax sectorMax
        < RatInterval.piLo :=
  ⟨audFaceMax, audSwitchMax, audSectorMax, audBalanced,
   (by intro e _; simp [audKap]), le_refl 0, sharpAlpha_bracket, audStrict⟩

/-! ## NEGATIVE CONTROL: the strict field genuinely can fail -/

def audMuBad : Fin 11 → ℚ := fun i => if i = 10 then 1/20 else 0

def audDBad : CanonicalCoeffQ audF where
  faceCard := q0FaceCard 1
  mu := audMuBad
  faceMask := fun _ _ => 0
  switchMask := fun _ => 0
  sideFirst := fun _ => 0
  sideSecond := fun _ => 0
  leftFirst := fun _ => 0
  leftSecond := fun _ => 0
  rightFirst := fun _ => 0
  rightSecond := fun _ => 0
  width := 0

theorem audBadStation : canonicalStationCoeffQ audDBad = 1/10 := by decide +kernel

theorem audBadConst : canonicalConstantCoeffQ audDBad audKap 0 = 1/10 := by
  rw [canonicalConstantCoeffQ, audBadStation]
  simp [audDBad, audKap]

theorem audBadTotal :
    canonicalTotalUpperQ audDBad audKap 0 sharpAlpha audFaceMax audSwitchMax audSectorMax
      = RatInterval.piHi/10 + 3 := by
  rw [canonicalTotalUpperQ, canonicalSharpConstantUpperQ, audBadConst, audFaceSum,
    audSwitchSum, audSectorSum]
  norm_num [piProductUpper, RatInterval.piLo, RatInterval.piHi, sharpAlpha]

/-- The same strict inequality is FALSE for the bad datum: the positive arm is
sensitive to the strict field. -/
theorem audBadStrictFails :
    ¬ (canonicalTotalUpperQ audDBad audKap 0 sharpAlpha audFaceMax audSwitchMax
        audSectorMax < RatInterval.piLo) := by
  rw [audBadTotal]
  norm_num [RatInterval.piHi, RatInterval.piLo]

end N11Formalization.ProbeA25AuditQ1Witness

#print axioms N11Formalization.ProbeA25AuditQ1Witness.audCard
#print axioms N11Formalization.ProbeA25AuditQ1Witness.audStation
#print axioms N11Formalization.ProbeA25AuditQ1Witness.audConst
#print axioms N11Formalization.ProbeA25AuditQ1Witness.audFaceSum
#print axioms N11Formalization.ProbeA25AuditQ1Witness.audStrict
#print axioms N11Formalization.ProbeA25AuditQ1Witness.audBalanced
#print axioms N11Formalization.ProbeA25AuditQ1Witness.audInterfaceNonvacuous
#print axioms N11Formalization.ProbeA25AuditQ1Witness.audBadTotal
#print axioms N11Formalization.ProbeA25AuditQ1Witness.audBadStrictFails
