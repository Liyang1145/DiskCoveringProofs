/-
n11-formalization — DSH line C4 groundwork (teammate `topo-interior`, task-4).

# DSHTopologyInteriorRows — the 33 interior (face) rows of the frozen canonical51 network

Scope: **local groundwork, standalone**. This file only re-reads the frozen definitions
`ResumeNetwork.{Edge,face,edgeLength,Feasible,V2}` and the frozen paid Fin-11 source face table
`ResumeLocalIncidence.{sourceFaces,faceMap,edgeMap,edgeMap_image}`. It does **not** state or use
any `Covers → Feasible` implication (that is C5, lead-side), and it does not redefine a weaker
`Feasible`.

Content:
* a complete index type for the 33 interior rows, with the **verified** real decomposition
  `33 = 27 (source-table block, Fin 9 × Fin 3) + 6 (non-source block, Fin 2 × Fin 3)`;
* the row constraint in the frozen `edgeLength` shape (no new inequality predicate);
* the exact split `Feasible ↔ 0 ≤ r ∧ (18 boundary rows) ∧ (33 interior rows)`;
* the kernel certificate that the 6 non-source rows are exactly the complement of the source
  45-edge image (zero stress weight does not delete a primal row);
* a negative control: the 45 source-image rows do not imply the 6 non-source rows.

No sorry / no custom axiom / no native_decide. Every theorem is kernel-checked by the project
serial gate.
-/
import N11Formalization.ResumeNetwork
import N11Formalization.ResumeLocalIncidence

set_option autoImplicit false

namespace N11Formalization.DSHTopologyInterior

open N11Formalization ResumeNetwork ResumeLocalIncidence

/-! ## 1. The index type: 33 interior rows = 27 source-table rows + 6 non-source rows

The frozen canonical face table `ResumeNetwork.face : Fin 11 → Fin 3 → Fin 11` has 11 faces
(9 fan faces + 2 central faces), and `edgeLength` attaches one primal row
`dist (C (face f v)) (Z f) ≤ r` to each `(f, v)`. So there are `11 × 3 = 33` interior rows.

The frozen paid source table realizes only **9** of the 11 canonical faces, through
`faceMap = ![9,10,8,0,1,2,3,4,6]` (canonical faces `{0,1,2,3,4,6,8,9,10}`). The two faces it
does **not** realize are canonical `5 = [5,6,10]` and `7 = [7,8,10]` — both hub-10 fan faces
with ring pairs `(5,6)` and `(7,8)` — and they are exactly the two faces whose six rows carry
`canonicalStress = 0`. Hence the real decomposition of 33 is `27 + 6`, and the six extra rows
are *not* the two central hub-hub faces (those are inside the source table, as raw faces 0/1).

This index type records that decomposition; `rowIdx` proves it is a bijection onto
`Fin 11 × Fin 3` (nothing dropped, nothing double-counted). -/

/-- Two-block index of the 33 interior rows: `.inl` = the 27 rows realized by the frozen source
9-face table (via `faceMap`), `.inr` = the 6 rows of the two canonical faces `5` and `7` that
the source table does not realize (zero-stress "slack" rows, still primal constraints). -/
abbrev InteriorRow := (Fin 9 × Fin 3) ⊕ (Fin 2 × Fin 3)

/-- The two canonical faces absent from the source table: `5 = [5,6,10]`, `7 = [7,8,10]`. -/
def slackFace : Fin 2 → Fin 11 := ![5, 7]

/-- The canonical `(face, vertex)` index of an interior row. -/
def rowIdx : InteriorRow → Fin 11 × Fin 3
  | .inl p => (faceMap p.1, p.2)
  | .inr p => (slackFace p.1, p.2)

/-- The canonical face of an interior row. -/
def rowFace (w : InteriorRow) : Fin 11 := (rowIdx w).1

/-- The canonical vertex of an interior row. -/
def rowVertex (w : InteriorRow) : Fin 3 := (rowIdx w).2

/-- The canonical site `face f v` touched by an interior row. -/
def rowSite (w : InteriorRow) : Fin 11 := face (rowFace w) (rowVertex w)

theorem rowFace_rowVertex (w : InteriorRow) : (rowFace w, rowVertex w) = rowIdx w := rfl

/-! ## 2. Enumeration facts, all by kernel `decide` on the frozen tables -/

/-- No two interior rows share a canonical `(face, vertex)` index. -/
theorem rowIdx_injective : ∀ a b : InteriorRow, rowIdx a = rowIdx b → a = b := by decide

/-- Every canonical `(face, vertex)` index is hit: **no row is dropped**. -/
theorem rowIdx_surjective : ∀ q : Fin 11 × Fin 3, ∃ w : InteriorRow, rowIdx w = q := by decide

theorem rowIdx_bijective : Function.Bijective rowIdx :=
  ⟨rowIdx_injective, rowIdx_surjective⟩

/-- The enumeration as an equivalence (usable downstream without re-deciding). -/
noncomputable def rowEquiv : InteriorRow ≃ Fin 11 × Fin 3 :=
  Equiv.ofBijective rowIdx rowIdx_bijective

theorem rowEquiv_apply (w : InteriorRow) : rowEquiv w = rowIdx w := rfl

theorem interiorRow_card : Fintype.card InteriorRow = 33 := by decide

/-- **Complete enumeration**: the image of the row index is *all* of `Fin 11 × Fin 3` — no
canonical interior row is missing from the table. -/
theorem rowIdx_image_univ :
    (Finset.univ.image rowIdx) = (Finset.univ : Finset (Fin 11 × Fin 3)) := by decide

/-- The enumerated table has exactly 33 rows. -/
theorem rowIdx_image_card : (Finset.univ.image rowIdx).card = 33 := by decide

/-- Explicit coordinate list of the 33 canonical rows `(face, vertex)` (computable). -/
def rowFaces : List (ℕ × ℕ) :=
  (List.range 11).flatMap (fun f => (List.range 3).map (fun v => (f, v)))

theorem rowFaces_length : rowFaces.length = 33 := by decide

/-- The explicit list contains every canonical interior row. -/
theorem rowFaces_complete (f : Fin 11) (v : Fin 3) : (f.val, v.val) ∈ rowFaces := by
  revert f v
  decide

/-- Printed table of the 33 enumerated rows: canonical `(face, vertex)` and its block.
Printed (not a proof); the kernel certificates are `rowIdx_image_univ`, `rowFaces_complete`
and `rowTable_label_iff`. -/
def rowTable : List (ℕ × ℕ × String) :=
  rowFaces.map (fun p =>
    (p.1, p.2, if p.1 = 5 ∨ p.1 = 7 then "slack-witness" else "source-table"))

theorem rowTable_length : rowTable.length = 33 := by decide

/-- The printed table's label is the frozen source-table complement: `slack-witness` exactly on
the canonical faces outside the `faceMap` image. -/
theorem rowTable_label_iff (f : Fin 11) :
    ((if f.val = 5 ∨ f.val = 7 then "slack-witness" else "source-table") = "slack-witness") ↔
      ¬ ∃ g : Fin 9, faceMap g = f := by
  revert f
  decide

/-- The printed table carries the label of every canonical row. -/
theorem rowTable_covers_label (f : Fin 11) (v : Fin 3) :
    (f.val, v.val, if f.val = 5 ∨ f.val = 7 then "slack-witness" else "source-table") ∈
      rowTable := by
  revert f v
  decide

#eval rowTable

theorem canonicalFaceRow_card : Fintype.card (Fin 11 × Fin 3) = 33 := by decide

theorem sourceBlock_card : Fintype.card (Fin 9 × Fin 3) = 27 := by decide

theorem slackBlock_card : Fintype.card (Fin 2 × Fin 3) = 6 := by decide

theorem rowEquiv_card : Fintype.card InteriorRow = Fintype.card (Fin 11 × Fin 3) :=
  Fintype.card_congr rowEquiv

/-- The two blocks are disjoint in canonical indices: the 27 source-table rows and the 6
non-source rows never collide. -/
theorem blocks_disjoint : ∀ a : Fin 9 × Fin 3, ∀ b : Fin 2 × Fin 3,
    rowIdx (.inl a) ≠ rowIdx (.inr b) := by decide

/-- **The verified decomposition**: 33 = 27 + 6, with the 27 source-table rows and the 6
non-source rows. -/
theorem decomposition_27_6 :
    Fintype.card (Fin 9 × Fin 3) = 27 ∧ Fintype.card (Fin 2 × Fin 3) = 6 ∧
      Fintype.card InteriorRow = 33 ∧
      (∀ a : Fin 9 × Fin 3, ∀ b : Fin 2 × Fin 3, rowIdx (.inl a) ≠ rowIdx (.inr b)) ∧
      (∀ q : Fin 11 × Fin 3,
        (∃ p : Fin 9 × Fin 3, rowIdx (.inl p) = q) ∨
          (∃ p : Fin 2 × Fin 3, rowIdx (.inr p) = q)) := by
  refine ⟨sourceBlock_card, slackBlock_card, interiorRow_card, blocks_disjoint, ?_⟩
  · intro q
    obtain ⟨w, hw⟩ := rowIdx_surjective q
    rcases w with p | p
    · exact Or.inl ⟨p, hw⟩
    · exact Or.inr ⟨p, hw⟩

/-- The two canonical faces missing from the frozen source table are exactly `5` and `7`
(kernel statement of `ResumeLocalIncidence.edgeMap_image` on the face half). -/
theorem source_table_complement (f : Fin 11) :
    (∃ g : Fin 9, faceMap g = f) ↔ f ≠ 5 ∧ f ≠ 7 := by
  revert f
  decide

/-- The six non-source rows are present in the enumeration (they cannot be dropped). -/
theorem slack_rows_present (v : Fin 3) :
    (∃ w : InteriorRow, rowIdx w = ((5 : Fin 11), v)) ∧
      (∃ w : InteriorRow, rowIdx w = ((7 : Fin 11), v)) := by
  revert v
  decide

/-- The six non-source rows, read off the frozen canonical table: `5 = [5,6,10]`,
`7 = [7,8,10]` — two hub-10 fan faces (hub `10` + ring pair `(5,6)` resp. `(7,8)`), **not**
the central hub-hub faces. -/
theorem slack_faces_are_hub10_fan :
    face 5 = ![5, 6, 10] ∧ face 7 = ![7, 8, 10] := ⟨rfl, rfl⟩

/-- The two central hub-hub faces are *inside* the source table (raw faces 0 and 1), so they
are already covered by the 27-row block. -/
theorem central_faces_in_source_block :
    face 9 = ![0, 9, 10] ∧ face 10 = ![4, 9, 10] ∧
      (∃ g : Fin 9, faceMap g = 9) ∧ (∃ g : Fin 9, faceMap g = 10) :=
  ⟨ResumeNetwork.central_face_calibration.1, ResumeNetwork.central_face_calibration.2,
    ⟨0, rfl⟩, ⟨1, rfl⟩⟩

/-! ## 3. Row constraints in the frozen `edgeLength` shape (no weaker redefinition) -/

/-- The interior row constraint, *literally* the frozen `edgeLength` on the frozen `Edge` type.
No new inequality predicate is introduced: this is `edgeLength U C Z (.inr (rowIdx w)) ≤ r`. -/
def RowConstraint (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ)
    (w : InteriorRow) : Prop :=
  edgeLength U C Z (.inr (rowIdx w)) ≤ r

/-- Explicit form of a row constraint (definitionally the frozen `dist (C (face f v)) (Z f) ≤ r`). -/
theorem rowConstraint_iff (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ)
    (w : InteriorRow) :
    RowConstraint U C Z r w ↔ dist (C (rowSite w)) (Z (rowFace w)) ≤ r := Iff.rfl

/-- The same, phrased on the canonical index (what a downstream consumer needs). -/
theorem rowConstraint_canonical (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ)
    (f : Fin 11) (v : Fin 3) {w : InteriorRow} (hw : rowIdx w = (f, v)) :
    RowConstraint U C Z r w ↔ dist (C (face f v)) (Z f) ≤ r := by
  show edgeLength U C Z (.inr (rowIdx w)) ≤ r ↔ dist (C (face f v)) (Z f) ≤ r
  rw [hw]
  rfl

/-- Every interior row is a consequence of the frozen `Feasible` (projection, no C1–C3). -/
theorem row_of_feasible {U : Fin 9 → Point} {C Z : Fin 11 → Point} {r : ℝ}
    (hf : Feasible U C Z r) (w : InteriorRow) : RowConstraint U C Z r w :=
  hf.2 (.inr (rowIdx w))

/-- **The exact 18 + 33 split of the frozen 51 rows**: `Feasible` is equivalent to nonnegativity
plus the 18 boundary rows plus the 33 enumerated interior rows. Nothing else is in `Feasible`,
and no row can be omitted (uses `rowIdx_surjective`). -/
theorem feasible_iff_rows {U : Fin 9 → Point} {C Z : Fin 11 → Point} {r : ℝ} :
    Feasible U C Z r ↔
      0 ≤ r ∧ (∀ p : Fin 9 × Fin 2, edgeLength U C Z (.inl p) ≤ r) ∧
        (∀ w : InteriorRow, RowConstraint U C Z r w) := by
  constructor
  · intro hf
    exact ⟨hf.1, fun p => hf.2 (.inl p), fun w => hf.2 (.inr (rowIdx w))⟩
  · rintro ⟨hr, hb, hi⟩
    refine ⟨hr, ?_⟩
    rintro (p | ⟨f, v⟩)
    · exact hb p
    · obtain ⟨w, hw⟩ := rowIdx_surjective (f, v)
      rw [← hw]
      exact hi w

/-- Consumer-facing form: the 33 rows in the canonical `(face, vertex)` indexing are exactly
the interior half of `Feasible`. -/
theorem feasible_iff_canonical_rows {U : Fin 9 → Point} {C Z : Fin 11 → Point} {r : ℝ} :
    Feasible U C Z r ↔
      0 ≤ r ∧ (∀ p : Fin 9 × Fin 2, edgeLength U C Z (.inl p) ≤ r) ∧
        (∀ f : Fin 11, ∀ v : Fin 3, dist (C (face f v)) (Z f) ≤ r) := by
  constructor
  · intro hf
    exact ⟨hf.1, fun p => hf.2 (.inl p), fun f v => hf.2 (.inr (f, v))⟩
  · rintro ⟨hr, hb, hi⟩
    refine feasible_iff_rows.2 ⟨hr, hb, ?_⟩
    intro w
    exact hi (rowFace w) (rowVertex w)

/-! ## 4. The 45 ≠ 51 certificate: the six non-source rows are logically independent

`ResumeLocalIncidence.edgeMap_image` says the source 45-edge index hits every boundary row and
every face row except `f = 5, 7`. The next three theorems make that a kernel count and a
per-row characterization, and the last one is a negative control showing that the 45 source
rows alone do **not** imply the six remaining primal rows. -/

/-- The source 45-edge index hits exactly 45 of the 51 canonical rows. -/
theorem source_image_card :
    (Finset.univ.filter (fun e : Edge => ∃ s : SourceEdge, edgeMap s = e)).card = 45 := by
  decide

/-- The complement of the source image has exactly 6 rows. -/
theorem nonimage_card :
    (Finset.univ.filter (fun e : Edge => ¬ ∃ s : SourceEdge, edgeMap s = e)).card = 6 := by
  decide

/-- The complement rows are exactly the rows of the two canonical faces `5` and `7`. -/
theorem nonimage_iff (e : Edge) :
    (¬ ∃ s : SourceEdge, edgeMap s = e) ↔
      ∃ v : Fin 3, e = (Sum.inr ((5 : Fin 11), v)) ∨ e = (Sum.inr ((7 : Fin 11), v)) := by
  revert e
  decide

/-- In the interior-row indexing: the non-source rows are exactly the `.inr` block. -/
theorem nonimage_rows_are_slack_block (w : InteriorRow) :
    (¬ ∃ s : SourceEdge, edgeMap s = (Sum.inr (rowIdx w) : Edge)) ↔
      ∃ p : Fin 2 × Fin 3, w = .inr p := by
  revert w
  decide

/-- A concrete nonzero point of the frozen `Point` type (used for the negative control). -/
theorem one_zero_ne : ((!₂[(1 : ℝ), 0] : Point)) ≠ 0 := by
  intro h
  have h0 : ((!₂[(1 : ℝ), 0] : Point)).ofLp 0 = (0 : Point).ofLp 0 :=
    congrArg (fun p : Point => p.ofLp 0) h
  norm_num at h0

/-- **Negative control (45 ≠ 51).** There is a configuration in which *all 45 source-image rows*
hold at radius `0` while an interior row fails. Hence the source's 45 edge lengths are not the
full canonical51 constraint set, and the six non-source rows cannot be deleted. -/
theorem slack_rows_not_implied_by_source_rows (p : Point) (hp : p ≠ 0) :
    ∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
      (∀ e : Edge, (∃ s : SourceEdge, edgeMap s = e) → edgeLength U C Z e ≤ r) ∧
        ¬ (∀ w : InteriorRow, RowConstraint U C Z r w) := by
  refine ⟨fun _ => 0, fun _ => 0, fun f => if f = (5 : Fin 11) then p else 0, 0, ?_, ?_⟩
  · rintro (_ | ⟨f, v⟩) ⟨s, hs⟩
    · simp [edgeLength]
    · have him := (edgeMap_image (Sum.inr (f, v))).1 ⟨s, hs⟩
      -- the row lies in the source image, so `f ≠ 5 ∧ f ≠ 7`; only `f ≠ 5` is needed to
      -- evaluate the chosen witness `Z`
      have hf5 : f ≠ 5 := him.1
      have _hf7 : f ≠ 7 := him.2
      simp [edgeLength, hf5]
  · intro h
    have h5 := h (Sum.inr ((0 : Fin 2), (0 : Fin 3)))
    have h5' : dist (0 : Point) p ≤ 0 := by
      simpa [RowConstraint, rowIdx, slackFace, edgeLength, face] using h5
    have hpos : 0 < dist (0 : Point) p := dist_pos.mpr (Ne.symm hp)
    linarith

/-- Existential form of the negative control with an explicit frozen point. -/
theorem slack_rows_not_implied_by_source_rows' :
    ∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
      (∀ e : Edge, (∃ s : SourceEdge, edgeMap s = e) → edgeLength U C Z e ≤ r) ∧
        ¬ (∀ w : InteriorRow, RowConstraint U C Z r w) :=
  slack_rows_not_implied_by_source_rows _ one_zero_ne

/-! ## 5. Verbatim frozen types used above (printed into the gate log, not restated) -/

#check @ResumeNetwork.Edge
#check @ResumeNetwork.face
#check @ResumeNetwork.edgeLength
#check @ResumeNetwork.Feasible
#check @ResumeNetwork.V2
#check @ResumeNetwork.edge_card
#check @ResumeNetwork.oracle_le_of_geometric_witnesses
#check @ResumeLocalIncidence.sourceFaces
#check @ResumeLocalIncidence.faceMap
#check @ResumeLocalIncidence.faceMap_exact
#check @ResumeLocalIncidence.edgeMap
#check @ResumeLocalIncidence.edgeMap_image
#check @ResumeLocalIncidence.sourceLength_eq
#check @ResumeLocalIncidence.sum_reindex
#check @N11Formalization.DSHTopologyInterior.rowIdx
#check @N11Formalization.DSHTopologyInterior.RowConstraint
#check @N11Formalization.DSHTopologyInterior.feasible_iff_canonical_rows
#check @N11Formalization.DSHTopologyInterior.decomposition_27_6
#check @N11Formalization.DSHTopologyInterior.rowIdx_image_univ

#print axioms N11Formalization.DSHTopologyInterior.rowIdx_injective
#print axioms N11Formalization.DSHTopologyInterior.rowIdx_surjective
#print axioms N11Formalization.DSHTopologyInterior.rowIdx_image_univ
#print axioms N11Formalization.DSHTopologyInterior.rowIdx_image_card
#print axioms N11Formalization.DSHTopologyInterior.decomposition_27_6
#print axioms N11Formalization.DSHTopologyInterior.source_table_complement
#print axioms N11Formalization.DSHTopologyInterior.feasible_iff_rows
#print axioms N11Formalization.DSHTopologyInterior.feasible_iff_canonical_rows
#print axioms N11Formalization.DSHTopologyInterior.nonimage_card
#print axioms N11Formalization.DSHTopologyInterior.nonimage_rows_are_slack_block
#print axioms N11Formalization.DSHTopologyInterior.slack_rows_not_implied_by_source_rows'

end N11Formalization.DSHTopologyInterior
