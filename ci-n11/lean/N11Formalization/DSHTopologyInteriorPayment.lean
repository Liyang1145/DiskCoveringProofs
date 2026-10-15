/-
n11-formalization — DSH line C4 groundwork (teammate `topo-interior`, task-4).

# DSHTopologyInteriorPayment — per-row payment and per-row C1–C3 dependency marks

Scope: **local groundwork, standalone**; lead integrates. This file consumes only *frozen paid*
data and states no `Covers → Feasible` implication (that is C5, lead-side).

Per-row payment, as it actually exists in the frozen library:

* **27 source-table rows** (`.inl` block, canonical faces `{0,1,2,3,4,6,8,9,10}`) are paid at the
  source configuration with **equality** `= sourceRadius` by
  `SourceSharpEnergyCalibration.carrying_edge_length` (root-integrated), and their
  `canonicalStress` weight is strictly positive (`SourceBoundaryStressPositive.stress_pos`).
* **6 non-source rows** (`.inr` block, canonical faces `5 = [5,6,10]`, `7 = [7,8,10]`) are paid at
  the candidate/source configuration by the frozen witness table
  `FlashBoundaryCapsFaces.faceOK_table` (through `FlashLeafRootNetwork.exists_face_witnesses`),
  whose single input `FaceCoverable u 0 1 10` is itself paid by
  `FlashSlackConsumer.faceCoverable01_10` (witness = the fixed rational point
  `FlashSlackFace1.O0`, **not** a Voronoi vertex). Their `canonicalStress` weight is `0`
  (`SourceCentreB2Readout.canonical_slack_zero`), and zero weight does not delete the primal row.

Consumer: the 33 rows + the frozen 18 boundary rows rebuild `Feasible` at the source
configuration and drive the frozen `ResumeNetwork.oracle_le_feasible` consumer, reproducing the
root-integrated `SourceSharpEnergyCalibration.source_oracle_upper`.

The `CoversObligation` record at the end marks, **per row**, which of C1 (ten-boundary
exclusion), C2 (ownership/no-bubble) and C3 (two-hub/two-fan) the *arbitrary-cover* payment of
that row still needs. It is a documentation record with a kernel-checked index spec — it is not
a proof of those obligations.
-/
import N11Formalization.DSHTopologyInteriorRows
import N11Formalization.FlashLeafRootNetwork
import N11Formalization.FlashSlackConsumer
import N11Formalization.SourceSharpEnergyCalibration
import N11Formalization.SourceBoundaryStressPositive
import N11Formalization.SourceAlphaOf
import N11Formalization.SourceCentreB2Readout
import N11Formalization.RootRangeBoxFull

set_option autoImplicit false

namespace N11Formalization.DSHTopologyInterior

open N11Formalization ResumeNetwork ResumeLocalIncidence
open SourcePositiveHarmonicConsumer

/-! ## 1. The index identity between a source-table row and its canonical row -/

/-- A source-table face row lands on its canonical row (`edgeMap` on the face half). -/
theorem edgeMap_source_row (f : Fin 9) (v : Fin 3) :
    edgeMap (.inr (f, v)) = (Sum.inr (rowIdx (.inl (f, v))) : Edge) := rfl

/-! ## 2. The 27 source-table rows: paid with equality at the source configuration -/

/-- **Per-row payment (27 source-table rows)**: at the source configuration the row length is
*exactly* `sourceRadius`, by the frozen paid carrying-edge calibration. -/
theorem source_block_row_paid (f : Fin 9) (v : Fin 3) :
    edgeLength sourceAnchors sourceCenters sourceAux (.inr (rowIdx (.inl (f, v)))) =
      SourceExactRoot.sourceRadius := by
  rw [← edgeMap_source_row f v]
  exact SourceSharpEnergyCalibration.carrying_edge_length (.inr (f, v))

/-- The same row is also a satisfied row constraint at radius `sourceRadius`. -/
theorem source_block_row_le (f : Fin 9) (v : Fin 3) :
    edgeLength sourceAnchors sourceCenters sourceAux (.inr (rowIdx (.inl (f, v)))) ≤
      SourceExactRoot.sourceRadius :=
  le_of_eq (source_block_row_paid f v)

/-- **Per-row weight status (27 source-table rows)**: strictly positive canonical stress. -/
theorem source_block_row_weight_pos (f : Fin 9) (v : Fin 3) :
    0 < SourceCentreB2Readout.canonicalStress (.inr (rowIdx (.inl (f, v)))) := by
  rw [← edgeMap_source_row f v]
  simp only [SourceCentreB2Readout.canonicalStress, SourceAlphaOf.alphaEdge_edgeMap]
  exact SourceBoundaryStressPositive.stress_pos (.inr (f, v))

/-! ## 3. The 6 non-source rows: paid by the frozen witness at the source configuration -/

/-- The frozen witness input for the source root: box membership. -/
theorem sourceRoot_inCertBox : RootRangeBoxFull.InCertBox SourceExactRoot.sourceRoot :=
  FlashRootNetwork.inCertBox_root SourceExactRoot.sourceSpec rfl rfl

/-- The frozen witness input for the source root: the root equation. -/
theorem sourceRoot_residual : N11Formalization.residual SourceExactRoot.sourceRoot = 0 :=
  FlashRootNetwork.residual_root SourceExactRoot.sourceSpec rfl

/-- **Per-row payment (6 non-source rows)**: the frozen witness table pays all six rows of the
two canonical faces `5` and `7` at the source configuration. The witness is a free node, so
this is a `≤` row (not the equality of the 27 carrying rows). -/
theorem slack_block_rows_paid :
    ∃ Z : Fin 11 → Point, ∀ (s : Fin 2) (v : Fin 3),
      edgeLength sourceAnchors sourceCenters Z (.inr (rowIdx (.inr (s, v)))) ≤
        SourceExactRoot.sourceRadius := by
  obtain ⟨Z, hZ⟩ :=
    FlashRootNetwork.exists_face_witnesses SourceExactRoot.sourceRoot sourceRoot_inCertBox
      sourceRoot_residual
      (FlashSlackConsumer.faceCoverable01_10 SourceExactRoot.sourceRoot sourceRoot_inCertBox)
  refine ⟨Z, ?_⟩
  intro s v
  have h := hZ (slackFace s) v
  have h' : dist (sourceCenters (face (slackFace s) v)) (Z (slackFace s)) ≤
      SourceExactRoot.sourceRadius := by
    simpa [sourceCenters, SourceExactRoot.sourceRadius] using h
  simpa [edgeLength, rowIdx] using h'

/-- **Per-row weight status (6 non-source rows)**: the canonical stress on them is `0`. -/
theorem slack_block_row_weight_zero (s : Fin 2) (v : Fin 3) :
    SourceCentreB2Readout.canonicalStress (.inr (rowIdx (.inr (s, v)))) = 0 := by
  fin_cases s
  · simpa [rowIdx, slackFace] using (SourceCentreB2Readout.canonical_slack_zero v).1
  · simpa [rowIdx, slackFace] using (SourceCentreB2Readout.canonical_slack_zero v).2

/-! ## 4. All 33 rows at the source configuration, and the frozen consumer

The witness is patched so that a *single* `Z` pays all 33 rows: the frozen source auxiliary on
the 9 source-table faces (equality), the frozen slack witness on faces `5` and `7`. -/

/-- Patch a witness so that the source auxiliary node is used on the source-table faces. -/
noncomputable def patchAux (Z : Fin 11 → Point) : Fin 11 → Point :=
  fun f => if f = 5 ∨ f = 7 then Z f else sourceAux f

/-- `edgeLength` on a face row depends on `Z` only through `Z f`. -/
theorem edgeLength_inr_congr {U : Fin 9 → Point} {C : Fin 11 → Point} {Z Z' : Fin 11 → Point}
    (f : Fin 11) (v : Fin 3) (h : Z f = Z' f) :
    edgeLength U C Z (.inr (f, v)) = edgeLength U C Z' (.inr (f, v)) := by
  simp only [edgeLength, h]

/-- **All 33 interior rows hold at the source configuration** for one witness `Z`. -/
theorem all33_rows_paid_at_source :
    ∃ Z : Fin 11 → Point, ∀ w : InteriorRow,
      edgeLength sourceAnchors sourceCenters Z (.inr (rowIdx w)) ≤ SourceExactRoot.sourceRadius := by
  obtain ⟨Zs, hZs⟩ := slack_block_rows_paid
  refine ⟨patchAux Zs, ?_⟩
  intro w
  rcases w with ⟨f, v⟩ | ⟨s, v⟩
  · have hne := (source_table_complement (faceMap f)).1 ⟨f, rfl⟩
    have hpatch : patchAux Zs (faceMap f) = sourceAux (faceMap f) := by
      simp [patchAux, hne.1, hne.2]
    rw [show rowIdx (Sum.inl (f, v)) = (faceMap f, v) from rfl]
    rw [edgeLength_inr_congr (faceMap f) v hpatch]
    rw [show (Sum.inr (faceMap f, v) : Edge) = .inr (rowIdx (Sum.inl (f, v))) from rfl]
    exact source_block_row_le f v
  · have hsl : slackFace s = 5 ∨ slackFace s = 7 := by fin_cases s <;> decide
    have hpatch : patchAux Zs (slackFace s) = Zs (slackFace s) := by
      simp [patchAux, hsl]
    rw [show rowIdx (Sum.inr (s, v)) = (slackFace s, v) from rfl]
    rw [edgeLength_inr_congr (slackFace s) v hpatch]
    rw [show (Sum.inr (slackFace s, v) : Edge) = .inr (rowIdx (Sum.inr (s, v))) from rfl]
    exact hZs s v

/-- **The source configuration is `Feasible`** at `r = sourceRadius`: the 18 frozen boundary
rows (`FlashRootNetwork.canon_boundary`) plus the 33 enumerated interior rows. This is the
`Feasible` witness shape that C5 must produce for an *arbitrary* cover; here it is only the
source/candidate configuration. -/
theorem source_config_feasible :
    ∃ Z : Fin 11 → Point, Feasible sourceAnchors sourceCenters Z SourceExactRoot.sourceRadius := by
  obtain ⟨Z, hZ⟩ := all33_rows_paid_at_source
  have HR := RootRangeBoxFull.rootRange_of_box SourceExactRoot.sourceRoot sourceRoot_inCertBox
  refine ⟨Z, feasible_iff_rows.2 ⟨SourceExactRoot.sourceRadius_pos.le, ?_, hZ⟩⟩
  rintro ⟨i, side⟩
  have h := FlashRootNetwork.canon_boundary SourceExactRoot.sourceRoot HR.hsin HR.hR Z i side
  simpa [sourceAnchors, sourceCenters, SourceExactRoot.sourceRadius] using h

/-- **Frozen downstream consumer**: the rebuilt `Feasible` gives the oracle upper bound through
`ResumeNetwork.oracle_le_feasible` (no new interface). -/
theorem source_oracle_upper_via_rows : V2 sourceAnchors ≤ SourceExactRoot.sourceRadius ^ 2 := by
  obtain ⟨Z, hZ⟩ := source_config_feasible
  exact ResumeNetwork.oracle_le_feasible hZ

/-- Calibration against the root-integrated paid theorem (same statement, independent route):
both are the frozen `V2 sourceAnchors ≤ sourceRadius²`. -/
theorem source_oracle_upper_agrees :
    source_oracle_upper_via_rows = SourceSharpEnergyCalibration.source_oracle_upper :=
  Subsingleton.elim _ _

/-- **Per-row payment, canonical indexing**: *every one* of the 33 canonical interior rows
`(f, v)` is a row that holds at the source configuration at radius `sourceRadius`, for a witness
that may be chosen per row. By `source_table_complement` the mechanism is forced by `f`: the 27
source-table rows are paid with the source auxiliary node (equality), the six rows of faces `5`
and `7` by the frozen slack witness. -/
theorem any_row_paid_at_source (f : Fin 11) (v : Fin 3) :
    ∃ Z : Fin 11 → Point,
      edgeLength sourceAnchors sourceCenters Z (.inr (f, v)) ≤ SourceExactRoot.sourceRadius := by
  obtain ⟨Zs, hZs⟩ := slack_block_rows_paid
  by_cases hf : f = 5 ∨ f = 7
  · refine ⟨Zs, ?_⟩
    rcases hf with rfl | rfl
    · simpa [rowIdx, slackFace] using hZs (0 : Fin 2) v
    · simpa [rowIdx, slackFace] using hZs (1 : Fin 2) v
  · obtain ⟨g, hg⟩ := (source_table_complement f).2 (by tauto)
    refine ⟨sourceAux, ?_⟩
    rw [← hg]
    simpa [rowIdx] using source_block_row_le g v

/-- **Cross-table calibration between the two frozen tables.** The canonical slack face `5`
corresponds to *raw* face `7`, and canonical slack face `7` to *raw* face `0` — exactly the two
raw faces the frozen witness table handles through the relaxed fixed rational point
`O0` (`hF0`, i.e. `faceOK_table` case 0) and its mirror (`faceOK_F7_of_F0`, case 7). The source
9-face table never uses raw faces `0` and `7`. -/
theorem slack_raw_correspondence :
    FlashRootNetwork.faceRaw 5 = 7 ∧ FlashRootNetwork.faceRaw 7 = 0 ∧
      (∀ v : Fin 3, face 5 v = ResumeGlobal.rawToCanon (FlashRootNetwork.rawVtx 5 v)) ∧
      (∀ v : Fin 3, face 7 v = ResumeGlobal.rawToCanon (FlashRootNetwork.rawVtx 7 v)) ∧
      (∀ f : Fin 9, FlashRootNetwork.faceRaw (faceMap f) ≠ 0 ∧
        FlashRootNetwork.faceRaw (faceMap f) ≠ 7) :=
  ⟨rfl, rfl, fun v => FlashRootNetwork.face_eq_rawToCanon 5 v,
    fun v => FlashRootNetwork.face_eq_rawToCanon 7 v, by decide⟩

/-! ## 5. Per-row C1–C3 dependency marks (record, not proof)

For an **arbitrary** `Covers c r`, every one of the 33 rows still needs the canonical
configuration to exist. The record below marks, per row, which of the three open obligations it
depends on; the *kernel-checked* content is the index spec (which block a row is in), while the
obligation set itself is the documented open interface (see `REPORT.md` unpaid-premise list).

* C1 = ten-boundary exclusion (radius reduction / 9-boundary configuration + hub split):
  needed by every row.
* C2 = ownership / no-bubble (ring cells ordered, neighbouring cells meeting at a single point):
  needed by every row.
* C3 = two-hub / two-fan (the 11 dual vertices realizing the canonical faces): needed by every
  row; for the six non-source rows it is strictly harder, because the source's own witness for
  those two faces is the relaxed fixed rational point `O0` and its mirror, **not** a primal
  Voronoi vertex. -/

/-- How a row is paid at the source/candidate configuration (frozen data). -/
inductive PayMechanism
  | carryingEquality
  | slackWitness
deriving DecidableEq

/-- The open obligations an arbitrary-cover payment of a row depends on. -/
inductive CoversObligation
  | c1TenBoundaryExclusion
  | c2Ownership
  | c3TwoHubTwoFan
deriving DecidableEq

/-- Per-row mark: payment mechanism, zero-weight flag, and the C1–C3 obligation set. -/
structure RowMark where
  mechanism : PayMechanism
  weightZero : Bool
  obligations : Finset CoversObligation
deriving DecidableEq

/-- The per-row mark table. -/
def rowMark (w : InteriorRow) : RowMark :=
  match w with
  | .inl _ => ⟨PayMechanism.carryingEquality, false,
      {CoversObligation.c1TenBoundaryExclusion, CoversObligation.c2Ownership,
        CoversObligation.c3TwoHubTwoFan}⟩
  | .inr _ => ⟨PayMechanism.slackWitness, true,
      {CoversObligation.c1TenBoundaryExclusion, CoversObligation.c2Ownership,
        CoversObligation.c3TwoHubTwoFan}⟩

theorem rowMark_mechanism_iff (w : InteriorRow) :
    (rowMark w).mechanism = PayMechanism.carryingEquality ↔ ∃ p : Fin 9 × Fin 3, w = .inl p := by
  rcases w with p | p <;> simp [rowMark]

theorem rowMark_weightZero_iff (w : InteriorRow) :
    (rowMark w).weightZero = true ↔ ∃ p : Fin 2 × Fin 3, w = .inr p := by
  rcases w with p | p <;> simp [rowMark]

theorem rowMark_obligations (w : InteriorRow) :
    (rowMark w).obligations =
      {CoversObligation.c1TenBoundaryExclusion, CoversObligation.c2Ownership,
        CoversObligation.c3TwoHubTwoFan} := by
  rcases w with p | p <;> rfl

/-- 27 rows are paid by the carrying-edge equality. -/
theorem rowMark_carrying_card :
    (Finset.univ.filter (fun w : InteriorRow =>
      (rowMark w).mechanism = PayMechanism.carryingEquality)).card = 27 := by
  decide

/-- 6 rows are paid by the relaxed slack witness. -/
theorem rowMark_slack_card :
    (Finset.univ.filter (fun w : InteriorRow =>
      (rowMark w).mechanism = PayMechanism.slackWitness)).card = 6 := by
  decide

/-- The mark table's zero-weight flag agrees with the actual canonical stress being zero
(uses the frozen paid `canonical_slack_zero` and the positivity of the 45 carrying weights). -/
theorem rowMark_weightZero_matches_stress (w : InteriorRow) :
    (rowMark w).weightZero = true ↔
      SourceCentreB2Readout.canonicalStress (.inr (rowIdx w)) = 0 := by
  rcases w with ⟨f, v⟩ | ⟨s, v⟩
  · rw [rowMark_weightZero_iff]
    constructor
    · rintro ⟨p, hp⟩
      exact absurd hp (by simp)
    · intro h
      exact absurd (source_block_row_weight_pos f v) (by rw [h]; exact lt_irrefl 0)
  · rw [rowMark_weightZero_iff]
    exact ⟨fun _ => slack_block_row_weight_zero s v, fun _ => ⟨(s, v), rfl⟩⟩

/-! ## 6. Verbatim frozen types and axiom prints -/

#check @SourceSharpEnergyCalibration.carrying_edge_length
#check @SourceBoundaryStressPositive.stress_pos
#check @SourceBoundaryStressPositive.canonical_nonneg
#check @SourceCentreB2Readout.canonicalStress
#check @SourceCentreB2Readout.canonical_slack_zero
#check @FlashBoundaryCapsFaces.faceOK_table
#check @FlashBoundaryCapsFaces.FaceCoverable
#check @FlashBoundaryCapsFaces.faceOK_F7_of_F0
#check @FlashSlackConsumer.faceCoverable01_10
#check @FlashRootNetwork.exists_face_witnesses
#check @FlashRootNetwork.canon_boundary
#check @FlashRootNetwork.oracle_le_sq_root
#check @SourceSharpEnergyCalibration.source_oracle_upper
#check @N11Formalization.DSHTopologyInterior.source_block_row_paid
#check @N11Formalization.DSHTopologyInterior.slack_block_rows_paid
#check @N11Formalization.DSHTopologyInterior.any_row_paid_at_source
#check @N11Formalization.DSHTopologyInterior.all33_rows_paid_at_source
#check @N11Formalization.DSHTopologyInterior.source_config_feasible
#check @N11Formalization.DSHTopologyInterior.source_oracle_upper_via_rows
#check @N11Formalization.DSHTopologyInterior.rowMark
#check @N11Formalization.DSHTopologyInterior.rowMark_weightZero_matches_stress
#check @N11Formalization.DSHTopologyInterior.slack_raw_correspondence

#print axioms N11Formalization.DSHTopologyInterior.source_block_row_paid
#print axioms N11Formalization.DSHTopologyInterior.source_block_row_weight_pos
#print axioms N11Formalization.DSHTopologyInterior.slack_block_rows_paid
#print axioms N11Formalization.DSHTopologyInterior.slack_block_row_weight_zero
#print axioms N11Formalization.DSHTopologyInterior.any_row_paid_at_source
#print axioms N11Formalization.DSHTopologyInterior.all33_rows_paid_at_source
#print axioms N11Formalization.DSHTopologyInterior.source_config_feasible
#print axioms N11Formalization.DSHTopologyInterior.source_oracle_upper_via_rows
#print axioms N11Formalization.DSHTopologyInterior.rowMark_carrying_card
#print axioms N11Formalization.DSHTopologyInterior.rowMark_slack_card
#print axioms N11Formalization.DSHTopologyInterior.rowMark_weightZero_matches_stress
#print axioms N11Formalization.DSHTopologyInterior.slack_raw_correspondence

end N11Formalization.DSHTopologyInterior
