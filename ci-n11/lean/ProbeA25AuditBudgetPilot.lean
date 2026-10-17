/-
  ProbeA25AuditBudgetPilot.lean   (owner: m5b-adversarial-audit)
  Top-level probe; NOT part of the A25 manifest module list.

  ===================== THE ONE NUMBER =====================
  Does ELABORATION of a machine-emitted factor tree COMPLETE within the DEFAULT
  budget at the accuracy a real class table needs?

  Setup (ONE factor, nothing else):
    - class F = q0Faces 1, one face, coefficients `start0_face1_p`;
    - q = b = 0 — the coefficient shape the VIABLE arithmetic route produces
      (masks == 0 forces q = b = 0; C1830), so this is the relevant case;
    - the GRADIENT leaf `planeGradientUpperQ p 0 0 C ≤ M`, chosen because C1830
      measured it ~3.5-3.7x cheaper than the direct leaf;
    - root box `planeBox 0 (1571/500) 0 (1571/500)`;
    - outside leaves are free via the proved vacuity branch (`PlaneOutside`,
      SharedMomentFacePlaneCertificate.lean:73, discharged by `plane_not_outside`
      :75-82). C1835: 496 of 1024 cells are free at 32x32.

  Accuracy target.  The class needs the sum of the 29 factor maxima below `piLo`
  while the sound total sits at 3.0654 < 3.14159, i.e. 0.076225 of slack.  A
  fair split gives 0.002628 per factor; Face1's true sup (q=b=0) is 0.21612476,
  so the target is 0.218753 and the required depth is 14 (measured in
  `pilot_calib.py`: depth 12 gives excess 1.279e-2, depth 14 the target).

  NO RESOURCE LIMITS ARE RAISED.  If elaboration fails, the failure is the answer.

  DOES NOT claim any class exclusion; pays ZERO class credit.
-/
import N11Formalization.SharedMomentFacePlaneGradientCertificate
import N11Formalization.SharedMomentConcreteFace1Data

set_option autoImplicit false
namespace N11Formalization.ProbeA25AuditBudgetPilot

open RationalBoxSubdivision SharedMomentFacePlaneGradientCertificate
open SharedMomentFacePlaneCertificate SharedMomentConcreteFace1

/-- The gradient leaf test, `q = b = 0`. -/
def GradOK (p : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2)) : Prop :=
  planeGradientUpperQ p 0 0 B ≤ M

instance (p : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2)) : Decidable (GradOK p M B) :=
  inferInstanceAs (Decidable (planeGradientUpperQ p 0 0 B ≤ M))

/-- A passing test is a legitimate `GradientPlaneLeaf`. -/
theorem gradOK_leaf {p : Fin 3 → ℚ} {M : ℚ} {B : Cell (Fin 2)}
    (h : GradOK p M B) : GradientPlaneLeaf p 0 0 M B := Or.inr h

/-- `decide` on the leaf test agrees with the `Prop`, so branching on the `Bool`
is faithful. -/
theorem gradOK_iff (p : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2)) :
    (decide (GradOK p M B) = true) = GradOK p M B :=
  decide_eq_true_eq

/-- Vacuity, as a directly computable rational comparison: exactly
`PlaneOutside B := RatInterval.piHi ≤ (B 0).lo + (B 1).lo`
(SharedMomentFacePlaneCertificate.lean:73), restated so `decide` can reduce it.
The proved `plane_not_outside` then discharges every such leaf for free. -/
def outB (B : Cell (Fin 2)) : Bool :=
  decide (RatInterval.piHi ≤ (B 0).lo + (B 1).lo)

theorem outB_iff (B : Cell (Fin 2)) : outB B = true ↔ PlaneOutside B := by
  simp only [outB, decide_eq_true_eq, PlaneOutside]

/-- Split the wider coordinate. -/
def splitCoord (B : Cell (Fin 2)) : Fin 2 :=
  if (B 1).hi - (B 1).lo ≤ (B 0).hi - (B 0).lo then 0 else 1

/-- Computable test: does every leaf of a depth-`d` midpoint subdivision pass?
Outside leaves are free.  This is the emitter `allOK` of ProbeA25AuditTreeEmit
with the gradient leaf in place of the direct leaf. -/
def allOK (p : Fin 3 → ℚ) (M : ℚ) : (d : ℕ) → Cell (Fin 2) → Bool
  | 0, B => if outB B then true else decide (GradOK p M B)
  | d + 1, B =>
      if outB B then true
      else if decide (GradOK p M B) then true
      else
        let i := splitCoord B
        let t := RationalBoxSubdivision.midpoint B i
        allOK p M d (leftChild B i t) && allOK p M d (rightChild B i t)

/-- The fair-split target for Face1, rounded UP (true sup 0.21612476 + 0.002628). -/
def pilotM : ℚ := 21876/100000

/-- The root box. -/
def pilotBox : Cell (Fin 2) := planeBox (0 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ)

/-! ## Pilot instances, increasing depth

Each is a separate `decide +kernel` obligation, so each records its own
elaboration cost.  We climb until either the budget fails or the target is met. -/

theorem pilot_d1_false : allOK start0_face1_p pilotM 1 pilotBox = false := by
  decide +kernel

theorem pilot_d1_true : allOK start0_face1_p 2 1 pilotBox = true := by
  decide +kernel

theorem pilot_d2_false : allOK start0_face1_p pilotM 2 pilotBox = false := by
  decide +kernel

theorem pilot_d3_false : allOK start0_face1_p pilotM 3 pilotBox = false := by
  decide +kernel

theorem pilot_d4_false : allOK start0_face1_p pilotM 4 pilotBox = false := by
  decide +kernel

theorem pilot_d5_false : allOK start0_face1_p pilotM 5 pilotBox = false := by
  decide +kernel

theorem pilot_d6_false : allOK start0_face1_p pilotM 6 pilotBox = false := by
  decide +kernel

-- depths 7-10: 79, 151, 287, 559 leaves (72, 136, 272, 528 paid).  These climb
-- toward the depth-14 requirement and record where elaboration cost bites.
theorem pilot_d7_false : allOK start0_face1_p pilotM 7 pilotBox = false := by
  decide +kernel

theorem pilot_d8_false : allOK start0_face1_p pilotM 8 pilotBox = false := by
  decide +kernel

-- depths 9-12: 287, 559, 1087, 2143 leaves (272, 528, 1056, 2080 paid).
-- Depth 12 is where `pilot_calib.py` measured excess 1.279e-2, still above the
-- 0.002628 fair-split target; depth 14 is the target.  We climb and stop where
-- the DEFAULT heartbeat budget stops us.
theorem pilot_d9_false : allOK start0_face1_p pilotM 9 pilotBox = false := by
  decide +kernel

theorem pilot_d10_false : allOK start0_face1_p pilotM 10 pilotBox = false := by
  decide +kernel

end N11Formalization.ProbeA25AuditBudgetPilot

#print axioms N11Formalization.ProbeA25AuditBudgetPilot.gradOK_leaf
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.outB_iff
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.gradOK_iff
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d1_false
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d1_true
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d2_false
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d3_false
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d4_false
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d5_false
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d6_false
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d7_false
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d8_false
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d9_false
#print axioms N11Formalization.ProbeA25AuditBudgetPilot.pilot_d10_false
