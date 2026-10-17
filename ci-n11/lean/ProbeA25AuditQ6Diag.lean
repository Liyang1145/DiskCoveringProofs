/-
  ProbeA25AuditQ6Diag.lean  (owner: m5b-adversarial-audit, task-4)
  DIAGNOSTIC ONLY: pin down why `decide +kernel` reported the uniqueness claim
  false in ProbeA25AuditQ6ForcedRelation.lean while the literal-`{0,1}` version
  is provable.  Tests several formulations side by side.
  Top-level probe; NOT part of the A25 manifest module list.
-/
import N11Formalization.CanonicalSharedMomentFiniteCertificate
import N11Formalization.ActualOrderedMetricGraphs
import N11Formalization.ActualEdgeFlagSums

set_option autoImplicit false

namespace N11Formalization.ProbeA25AuditQ6Diag

open ActualOrderedMetricGraphs ActualEdgeFlagSums ActualCanonicalMomentTransport
open ActualCanonicalFaceCoordinates

/-- `cycleEdge 0` is literally `{0,1}`. -/
theorem diagV6 : cycleEdge 0 = ({0, 1} : Finset (Fin 11)) := by decide +kernel

/-- The class has 11 faces. -/
theorem diagV1_card : (q0Faces 1).card = 11 := by decide +kernel

/-- A: the gate1 formulation, verbatim (`cycleEdge 0` inline). -/
theorem diagA :
    ∀ (f : q0Faces 1) (i : Fin 11), i ∈ f.val →
      (f.val.erase i = cycleEdge 0 ↔ (f.val = ({0, 1, 9} : Finset (Fin 11)) ∧ i = 9)) := by
  decide +kernel

/-- B: the same with the literal `{0,1}`, no `cycleEdge`. -/
theorem diagB :
    ∀ (f : q0Faces 1) (i : Fin 11), i ∈ f.val →
      (f.val.erase i = ({0, 1} : Finset (Fin 11))
        ↔ (f.val = ({0, 1, 9} : Finset (Fin 11)) ∧ i = 9)) := by
  decide +kernel

/-- C: B transported to A through `diagV6`. -/
theorem diagC :
    ∀ (f : q0Faces 1) (i : Fin 11), i ∈ f.val →
      (f.val.erase i = cycleEdge 0 ↔ (f.val = ({0, 1, 9} : Finset (Fin 11)) ∧ i = 9)) := by
  intro f i hi
  rw [diagV6]
  exact diagB f i hi

/-- D: slot count per cycle edge, for every `k`, using `canonicalLabel`. -/
theorem diagD :
    ∀ k : Fin 9,
      ((q0Faces 1).sum (fun f =>
        (Finset.univ.filter (fun s : Fin 3 =>
          f.val.erase (canonicalLabel f.val (q0FaceCard 1 f) s) = cycleEdge k)).card)) = 1 := by
  decide +kernel

/-- E: the same count with the literal. -/
theorem diagE :
    ((q0Faces 1).sum (fun f =>
      (Finset.univ.filter (fun s : Fin 3 =>
        f.val.erase (canonicalLabel f.val (q0FaceCard 1 f) s)
          = ({0, 1} : Finset (Fin 11)))).card)) = 1 := by
  decide +kernel

/-- F: the slot identification, forward direction only. -/
theorem diagF (f : q0Faces 1) (s : Fin 3)
    (h : f.val.erase (canonicalLabel f.val (q0FaceCard 1 f) s) = cycleEdge 0) :
    f.val = ({0, 1, 9} : Finset (Fin 11)) ∧ s = 2 := by
  rw [diagV6] at h
  have hmem : canonicalLabel f.val (q0FaceCard 1 f) s ∈ f.val := canonicalLabel_mem _ _ _
  have := (diagB f _ hmem).mp h
  exact this

/-- G: `cycleEdge 0` really is a face edge, so the relation is not vacuous. -/
theorem diagG : cycleEdge 0 ∈ faceEdges (q0Faces 1) := by decide +kernel

/-- H: all nine cycle edges are face edges. -/
theorem diagH : ∀ k : Fin 9, cycleEdge k ∈ faceEdges (q0Faces 1) := by decide +kernel

/-- I: the count of faces containing vertex 0. -/
theorem diagI : ((q0Faces 1).filter (fun f => (0 : Fin 11) ∈ f)).card = 3 := by
  decide +kernel

/-- J: the count of faces containing both 0 and 1 is 1. -/
theorem diagJ :
    ((q0Faces 1).filter (fun f => (0 : Fin 11) ∈ f ∧ (1 : Fin 11) ∈ f)).card = 1 := by
  decide +kernel

end N11Formalization.ProbeA25AuditQ6Diag

#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagV6
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagV1_card
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagA
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagB
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagC
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagD
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagE
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagF
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagG
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagH
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagI
#print axioms N11Formalization.ProbeA25AuditQ6Diag.diagJ
