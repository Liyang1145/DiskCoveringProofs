/-
  ProbeA25AuditQ6SlotLemma.lean  (owner: m5b-adversarial-audit, task-4)
  MINIMAL ISOLATION TEST.  Settles whether the biconditional form of the
  slot-uniqueness claim is true.  In the first gate of
  ProbeA25AuditQ6ForcedRelation.lean, `decide +kernel` reported the biconditional
  "false"; that file also had three earlier elaboration errors (line 66
  AddCommMonoid stuck, lines 87/106 rewrite failures), so the report may have been
  a cascade artefact rather than a true statement about the proposition.  This
  file contains ONLY these claims, with no other errors, so the result is clean.
  Top-level probe; NOT part of the A25 manifest module list.
-/
import N11Formalization.CanonicalSharedMomentFiniteCertificate
import N11Formalization.ActualOrderedMetricGraphs
import N11Formalization.ActualEdgeFlagSums

set_option autoImplicit false

namespace N11Formalization.ProbeA25AuditQ6SlotLemma

open ActualOrderedMetricGraphs ActualEdgeFlagSums ActualCanonicalMomentTransport
open ActualCanonicalFaceCoordinates

/-- `cycleEdge 0` is literally `{0,1}`. -/
theorem slot_cycleEdge0 : cycleEdge 0 = ({0, 1} : Finset (Fin 11)) := by decide +kernel

/-- (1) THE BICONDITIONAL, exactly as originally written in the main probe, with
the membership hypothesis. -/
theorem slot_biconditional :
    ∀ (f : q0Faces 1) (i : Fin 11), i ∈ f.val →
      (f.val.erase i = cycleEdge 0
        ↔ (f.val = ({0, 1, 9} : Finset (Fin 11)) ∧ i = 9)) := by
  decide +kernel

/-- (2) The same with the literal `{0,1}`, bypassing `cycleEdge`. -/
theorem slot_biconditional_literal :
    ∀ (f : q0Faces 1) (i : Fin 11), i ∈ f.val →
      (f.val.erase i = ({0, 1} : Finset (Fin 11))
        ↔ (f.val = ({0, 1, 9} : Finset (Fin 11)) ∧ i = 9)) := by
  decide +kernel

/-- (3) Forward direction only. -/
theorem slot_forward (f : q0Faces 1) (i : Fin 11) (hi : i ∈ f.val)
    (he : f.val.erase i = cycleEdge 0) :
    f.val = ({0, 1, 9} : Finset (Fin 11)) ∧ i = 9 :=
  (slot_biconditional f i hi).mp he

/-- (4) Converse: erasing `9` from `{0,1,9}` lands on `cycleEdge 0`. -/
theorem slot_converse :
    ({0, 1, 9} : Finset (Fin 11)).erase (9 : Fin 11) = cycleEdge 0 := by
  decide +kernel

/-- (5) `cycleEdge 0` IS a face edge. -/
theorem slot_cycleEdge0_mem : cycleEdge 0 ∈ faceEdges (q0Faces 1) := by decide +kernel

/-- (6) All nine cycle edges are face edges. -/
theorem slot_all_cycleEdges_mem : ∀ k : Fin 9, cycleEdge k ∈ faceEdges (q0Faces 1) := by
  decide +kernel

/-- (7) Exactly one face contains both `0` and `1`. -/
theorem slot_one_face_contains :
    ((q0Faces 1).filter (fun f => (0 : Fin 11) ∈ f ∧ (1 : Fin 11) ∈ f)).card = 1 := by
  decide +kernel

/-! ### The load-bearing count

`canonicalLabel f.val (q0FaceCard 1 f) s` is `(f.val.orderIsoOfFin _ s).val`, and
`decide` gets STUCK on it (it does not reduce `orderIsoOfFin`).  The failure
message is "did not reduce to `isTrue` or `isFalse`" — which is NOT the same as
the proposition being false.  So the count is stated first in ELEMENT form
(no `orderIsoOfFin`), which is what the relation actually consumes. -/

/-- (8a) ELEMENT FORM: for every cycle edge `k`, exactly one pair `(f,i)` with
`f ∈ q0Faces 1`, `i ∈ f.val` and `f.val.erase i = cycleEdge k` exists. -/
theorem slot_count_one_element :
    ∀ k : Fin 9,
      ((q0Faces 1).attach).sum (fun f =>
        (f.val.filter (fun i => f.val.erase i = cycleEdge k)).card) = 1 := by
  decide +kernel

/-- (8b) The element realizing it, for `k = 0`. -/
theorem slot_element_k0 :
    ((q0Faces 1).attach).sum (fun f =>
      (f.val.filter (fun i => f.val.erase i = cycleEdge 0)).card) = 1 :=
  slot_count_one_element 0

/-- (9) THE WITNESS, in element form (which `decide` CAN reduce, unlike anything
going through `canonicalLabel`/`orderIsoOfFin`): the unique pair realizing
`cycleEdge 0` is the face `{0,1,9}` with the element `9`. -/
theorem slot_witness_k0 :
    ({0, 1, 9} : Finset (Fin 11)).erase (9 : Fin 11) = cycleEdge 0 :=
  slot_converse

/-- (10) The element `9` really is in the face, so the witness is a genuine slot
(not a vacuous `erase` of a non-member). -/
theorem slot_witness_mem : (9 : Fin 11) ∈ ({0, 1, 9} : Finset (Fin 11)) := by
  decide +kernel

/-- (11) The other two elements of the witness face do NOT realize `cycleEdge 0`,
so the witness is the unique one for that face. -/
theorem slot_witness_others :
    ({0, 1, 9} : Finset (Fin 11)).erase (0 : Fin 11) ≠ cycleEdge 0 ∧
    ({0, 1, 9} : Finset (Fin 11)).erase (1 : Fin 11) ≠ cycleEdge 0 := by
  decide +kernel

end N11Formalization.ProbeA25AuditQ6SlotLemma

#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_cycleEdge0
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_biconditional
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_biconditional_literal
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_forward
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_converse
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_cycleEdge0_mem
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_all_cycleEdges_mem
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_one_face_contains
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_count_one_element
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_element_k0
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_witness_k0
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_witness_mem
#print axioms N11Formalization.ProbeA25AuditQ6SlotLemma.slot_witness_others
