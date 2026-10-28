/-
  DSHTopologyHubFanConsumer — DSH-TOPO-C3-S*: index-level consumer shim.

  Teammate `topo-hub-fan`, C3 continuance (lead instruction 2026-10-02: choose (i)).
  Write scope: `lean/N11Formalization/DSHTopologyHubFanConsumer*.lean`,
  `evidence/dsh/topology/hub-fan/shim/`.

  ## Purpose

  `DSHTopologyHubFan.lean` (C3) proved the hub/fan index facts about the frozen `Fin 11`
  tables.  `DSHTopologyInteriorInterface.lean` (C4, claim C1724) proved the C5-facing interface
  `0 ≤ r ∧ BoundaryRows ∧ 9 source-face witnesses ∧ FaceWitness 5 ∧ FaceWitness 7 ⇒ ∃ Z, Feasible`
  using an opaque `rowKind_decision` disjunction.  This file is the **thin bridge** between them:
  it re-expresses C4's two named hub-10 fan faces, its source block, and its `InteriorRow`
  reindexing in the C3 hub/fan vocabulary, and it exports C5-facing theorems whose hypotheses are
  indexed by that vocabulary — so a consumer no longer repeats row/index bookkeeping.

  ## Content (INDEX LEVEL ONLY — no metric content, no premises)

  * reindexing: `InteriorRow` / `rowIdx` / `rowEquiv` / `RowConstraint` (C4) ↦ frozen
    `Edge` / `edgeLength` (C3/ResumeNetwork), all at `rfl` level;
  * the row blocks of the frozen 51 rows in the C3 fan vocabulary: fan A, fan B, central, with
    exact lengths, pairwise disjointness and exhaustive concatenation;
  * hub-row facts: the rows whose site is hub 9 (6 rows) and hub 10 (7 rows), no boundary row has
    a hub site, and the hub-hub pair `{9,10}` is carried by exactly the two central rows;
  * source/slack identification: the source image is `[9,10,8,0,1,2,3,4,6]`, its complement is
    exactly `[5,7]` = the two hub-10 fan faces missing from the source table, and fan A is fully
    inside the source image;
  * C5-facing wiring: `feasible_of_source_image_and_fanB_completion`,
    `oracle_le_of_source_image_and_fanB_completion`, and the split
    `faceWitness_split_source_image_and_slack` (the "no repeated index bookkeeping" statement).

  ## Scope

  `local[graph]`, `standalone`.  This file adds no premise and no inequality: every finite claim is
  a kernel `decide` over the frozen tables, and the two C5-facing theorems only *delegate* to the
  already-registered C1724 interface.  It does NOT claim `Covers → Feasible` (C5, lead-side), does
  not touch the root, and carries the same non-consumption fence as C3: it must not be used to
  derive the two-fan graph from counting data (DEAD.md line 86, retracted C1395).

  No `sorry`, no custom axiom, no `native_decide`, no heartbeat bump.
-/
import Mathlib
import N11Formalization.DSHTopologyHubFan
import N11Formalization.DSHTopologyInteriorInterface

set_option maxRecDepth 8000
set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.DSHTopologyHubFanConsumer

open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeLocalIncidence
open N11Formalization.ResumeGlobal
open N11Formalization.DSHTopologyHubFan
open N11Formalization.DSHTopologyInterior

/-- The 33 interior rows of the frozen network, as frozen `Edge` rows, in `(f, v)` order. -/
def rowsOfFaces (fs : List (Fin 11)) : List Edge :=
  fs.flatMap (fun f => [(Sum.inr (f, 0) : Edge), Sum.inr (f, 1), Sum.inr (f, 2)])

/-- All 33 face rows of the frozen `Edge` type. -/
def faceRowList : List Edge := rowsOfFaces (List.finRange 11)

/-- All 18 boundary rows of the frozen `Edge` type. -/
def boundaryRowList : List Edge :=
  (List.finRange 9).flatMap (fun i => [(Sum.inl (i, 0) : Edge), Sum.inl (i, 1)])

/-- Fan A rows (hub-9 side), fan B rows (hub-10 side), central rows. -/
def fanARowList : List Edge := rowsOfFaces fanAFaces
def fanBRowList : List Edge := rowsOfFaces fanBFaces
def centralRowList : List Edge := rowsOfFaces [9, 10]

/-- All `(face, vertex)` indices in `(f, v)` order. -/
def allFaceIdx : List (Fin 11 × Fin 3) :=
  (List.finRange 11).flatMap (fun f => (List.finRange 3).map (fun v => (f, v)))

/-- The canonical site of a face row; `none` for boundary rows. -/
def siteOf (e : Edge) : Option (Fin 11) :=
  match e with
  | Sum.inl _ => none
  | Sum.inr q => some (face q.1 q.2)

/-- The canonical face of a face row; `none` for boundary rows. -/
def faceOf (e : Edge) : Option (Fin 11) :=
  match e with
  | Sum.inl _ => none
  | Sum.inr q => some q.1

/-- Does this row carry a hub as its canonical site? -/
def isHubSite (e : Edge) : Bool :=
  match siteOf e with
  | some v => v == 9 || v == 10
  | none => false

/-- The canonical face pair attached to the index `(f, v)` — the C3 pairing
`{face f v, face f (v+1)}` (so that a row index and a C3 fan pair are interconvertible). -/
def rowPair (q : Fin 11 × Fin 3) : V × V := ep (face q.1 q.2) (face q.1 (nxt q.2))

/-- The canonical faces realised by the frozen source table (`faceMap` image, in raw order). -/
def sourceImageFaces : List (Fin 11) := (List.finRange 9).map faceMap

/-! ## 1. Reindexing: C4 `InteriorRow` ↦ frozen `Edge` (rfl level) -/

/-- The frozen 33 face rows are exactly the `allFaceIdx` indices mapped into `Edge`. -/
theorem faceRowList_exact : faceRowList = allFaceIdx.map (fun q => (Sum.inr q : Edge)) := by
  decide

/-- Every canonical `(face, vertex)` index occurs in `allFaceIdx`. -/
theorem allFaceIdx_mem (q : Fin 11 × Fin 3) : q ∈ allFaceIdx := by revert q; decide

/-- C4's `rowIdx` lands in `allFaceIdx`. -/
theorem rowIdx_mem_allFaceIdx (w : InteriorRow) : rowIdx w ∈ allFaceIdx := by revert w; decide

/-- C4's reindexed row is literally a frozen face row. -/
theorem interiorRow_edge_row (w : InteriorRow) :
    (Sum.inr (rowIdx w) : Edge) ∈ faceRowList := by
  rw [faceRowList_exact]
  exact List.mem_map.2 ⟨rowIdx w, rowIdx_mem_allFaceIdx w, rfl⟩

/-- C4's `RowConstraint` is literally the frozen `edgeLength` on that row. -/
theorem rowConstraint_edgeLength (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ)
    (w : InteriorRow) :
    RowConstraint U C Z r w ↔ edgeLength U C Z (Sum.inr (rowIdx w) : Edge) ≤ r := Iff.rfl

/-- The C4 row index is bijective onto the 33 frozen face rows: nothing dropped, nothing doubled. -/
theorem rowIdx_onto_frozen_rows (q : Fin 11 × Fin 3) :
    (Sum.inr q : Edge) ∈ faceRowList := by
  rw [faceRowList_exact]
  exact List.mem_map.2 ⟨q, allFaceIdx_mem q, rfl⟩

/-- Row counts: 33 face rows, 18 boundary rows, 51 total (frozen `edge_card`). -/
theorem row_counts :
    faceRowList.length = 33 ∧ boundaryRowList.length = 18 ∧
    (faceRowList ++ boundaryRowList).eraseDups.length = 51 ∧ Fintype.card Edge = 51 := by
  decide

/-- The 51 frozen rows are exactly `faceRowList ++ boundaryRowList` (every `Edge` occurs). -/
theorem frozen_rows_covered : ∀ e : Edge, (faceRowList ++ boundaryRowList).contains e = true := by
  decide

/-- Face rows and boundary rows never collide. -/
theorem face_boundary_rows_disjoint :
    (faceRowList.filter (fun e => boundaryRowList.contains e)) = [] := by decide

/-! ## 2. Row blocks in the C3 fan vocabulary -/

/-- Fan A (12 rows), fan B (15 rows), central (6 rows): exact lengths. -/
theorem fan_row_counts :
    fanARowList.length = 12 ∧ fanBRowList.length = 15 ∧ centralRowList.length = 6 ∧
    fanARowList.length + fanBRowList.length + centralRowList.length = faceRowList.length := by
  decide

/-- The three blocks are pairwise disjoint. -/
theorem fan_row_blocks_disjoint :
    (fanARowList.filter (fun e => fanBRowList.contains e)) = [] ∧
    (fanARowList.filter (fun e => centralRowList.contains e)) = [] ∧
    (fanBRowList.filter (fun e => centralRowList.contains e)) = [] := by decide

/-- The three blocks exhaust the 33 face rows, in order. -/
theorem fan_row_blocks_exhaust :
    fanARowList ++ fanBRowList ++ centralRowList = faceRowList := by decide

/-- Fan A is the hub-9 side of the frozen table: its rows are exactly the rows of the faces in
`facesWith 9` that are not central rows. -/
theorem fanA_rows_are_hub9_side :
    fanARowList ++ centralRowList = rowsOfFaces (facesWith 9) := by decide

/-- Fan B is the hub-10 side of the frozen table. -/
theorem fanB_rows_are_hub10_side :
    fanBRowList ++ centralRowList = rowsOfFaces (facesWith 10) := by decide

/-- **Hub-hub uniqueness at row level**: exactly the two central rows carry the C3 hub-hub pair
`{9,10}`; no fan row does. -/
theorem hub_pair_rows_exact :
    (allFaceIdx.filter (fun q => rowPair q == ep 9 10)) = [((9 : Fin 11), (1 : Fin 3)),
      ((10 : Fin 11), (1 : Fin 3))] := by decide

/-- **Hub-site rows**: the 6 rows whose site is hub 9, and the 7 whose site is hub 10 — the
row-level form of the C3 degree pair `(6,7)`. -/
theorem hub_site_rows_exact :
    (allFaceIdx.filter (fun q => face q.1 q.2 == (9 : Fin 11))) =
      [((0 : Fin 11), (2 : Fin 3)), (1, 2), (2, 2), (3, 2), (9, 1), (10, 1)] ∧
    (allFaceIdx.filter (fun q => face q.1 q.2 == (10 : Fin 11))) =
      [((4 : Fin 11), (2 : Fin 3)), (5, 2), (6, 2), (7, 2), (8, 2), (9, 2), (10, 2)] := by
  decide

/-- No boundary row carries a hub site: the hubs are interior-only (C3 `boundary_rows_are_ring`,
restated on the frozen `Edge` rows). -/
theorem no_hub_site_boundary_rows : (boundaryRowList.filter isHubSite) = [] := by decide

/-- Every hub-site row is an interior row, and their number is 6 + 7 = 13. -/
theorem hub_site_rows_card :
    (faceRowList.filter isHubSite).length = 13 ∧
    (faceRowList.filter isHubSite).length +
      (boundaryRowList.filter isHubSite).length = 13 := by decide

/-! ## 3. Source / slack identification in the C3 vocabulary -/

/-- The frozen source table's canonical image, evaluated. -/
theorem sourceImageFaces_exact : sourceImageFaces = [9, 10, 8, 0, 1, 2, 3, 4, 6] := by decide

/-- **The two faces the source table does not realise are exactly `5` and `7`.** -/
theorem source_complement_exact :
    (List.finRange 11).filter (fun f => (sourceImageFaces.contains f) == false) = [5, 7] := by
  decide

/-- The complement inside fan B is the same two faces: the source table needs exactly this
completion of the hub-10 fan, and nothing else. -/
theorem fanB_source_complement : (fanBFaces.filter (fun f => (sourceImageFaces.contains f) == false)) =
    [5, 7] := by decide

/-- Fan A is entirely inside the source image: the hub-9 fan needs no completion. -/
theorem fanA_inside_source_image :
    (sourceImageFaces.filter (fun f => (fanAFaces.contains f) == true)) = fanAFaces := by decide

/-- C4's named slack faces are exactly the complement of the source image (and lie in fan B). -/
theorem slackFace_exact : slackFace = ![5, 7] ∧
    (∀ i : Fin 2, (slackFace i) ∈ fanBFaces) ∧
    (∀ i : Fin 2, (sourceImageFaces.contains (slackFace i)) = false) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i; revert i; decide
  · intro i; revert i; decide

/-- **Every canonical face is either in the source image or is one of the two slack faces.** -/
theorem face_mem_source_or_slack :
    ∀ f : Fin 11, f ∈ sourceImageFaces ∨ f = 5 ∨ f = 7 := by decide

/-! ### 3.1 Minimality of the completion, and the row-level link to the C3 fan pairs

The completion is not just sufficient; **any** family of extra faces that completes the source
image to all eleven faces must contain both `5` and `7`.  So a consumer cannot satisfy the
interface with a cheaper completion, and the two named hub-10 fan witnesses are exactly the
required index-level extra data. -/

/-- **Minimality.** If `extra` completes the source image to all 11 canonical faces, then `extra`
contains both slack faces `5` and `7`. -/
theorem completion_must_contain_slack (extra : List (Fin 11))
    (hcov : ∀ f : Fin 11, f ∈ sourceImageFaces ∨ f ∈ extra) :
    extra.contains (5 : Fin 11) = true ∧ extra.contains (7 : Fin 11) = true := by
  have h5 : ¬ ((5 : Fin 11) ∈ sourceImageFaces) := by
    rw [← List.contains_iff_mem, sourceImageFaces_exact]
    decide
  have h7 : ¬ ((7 : Fin 11) ∈ sourceImageFaces) := by
    rw [← List.contains_iff_mem, sourceImageFaces_exact]
    decide
  exact ⟨List.contains_iff_mem.2 ((hcov 5).resolve_left h5),
    List.contains_iff_mem.2 ((hcov 7).resolve_left h7)⟩

/-- Index-level negative control: the source image alone does **not** cover the 11 faces, and the
two faces it misses are exactly the slack faces. -/
theorem source_image_not_all_faces :
    (sourceImageFaces.length = 9) ∧
      (sourceImageFaces.contains (5 : Fin 11) = false) ∧
      (sourceImageFaces.contains (7 : Fin 11) = false) ∧
      (sourceImageFaces.contains (10 : Fin 11) = true) := by decide

/-- Index-level negative control: fan A + the central faces do not cover the 11 faces (fan B's
interior faces `5,7` are missing), so "fan A + central" is not a valid replacement for the
source-image + slack completion. -/
theorem fanA_plus_central_not_all_faces :
    (fanARowList ++ centralRowList).length = 18 ∧
      ((fanAFaces ++ [9, 10]).contains (5 : Fin 11) = false) ∧
      ((fanAFaces ++ [9, 10]).contains (7 : Fin 11) = false) := by decide

/-- The hub-hub index `(9,1)`/`(10,1)` pairs are *inside* the source image: the hub-hub pair
needs no extra witness (no third witness may be added for it). -/
theorem hub_pair_rows_are_in_source_image :
    (sourceImageFaces.contains (9 : Fin 11) = true) ∧
      (sourceImageFaces.contains (10 : Fin 11) = true) := by decide

/-- **Row-level link to C3.**  The `rowPair` image over the 33 frozen row indices is *literally*
C3's `DSHTopologyHubFan.faceRows` list — so every C3 hub/fan pair fact transfers to the row
indices without re-deriving anything. -/
theorem row_pair_image_eq_c3_faceRows :
    (allFaceIdx.map rowPair) = faceRows := by decide

/-- Consequently the distinct row pairs of the shim are exactly C3's 21 distinct face pairs. -/
theorem row_pair_image_distinct :
    (allFaceIdx.map rowPair).eraseDups = faceRows.eraseDups ∧
      (allFaceIdx.map rowPair).eraseDups.length = 21 := by decide

/-! ## 4. C5-facing wiring (delegation to the registered C1724 interface) -/

/-- The 11-face witness family splits into the 9 source-image witnesses plus the two slack
(hub-10 fan) witnesses — stated with the C3 index lists, so consumers do not redo the split. -/
theorem faceWitness_split_source_image_and_slack (C : Fin 11 → Point) (r : ℝ) :
    (∀ f : Fin 11, FaceWitness C f r) ↔
      (∀ f : Fin 11, f ∈ sourceImageFaces → FaceWitness C f r) ∧
        FaceWitness C 5 r ∧ FaceWitness C 7 r := by
  constructor
  · intro h
    exact ⟨fun f _ => h f, h 5, h 7⟩
  · rintro ⟨hsrc, h5, h7⟩ f
    rcases face_mem_source_or_slack f with hf | hf | hf
    · exact hsrc f hf
    · rw [hf]; exact h5
    · rw [hf]; exact h7

/-- **C5-facing shim (Feasible).** `0 ≤ r`, the 18 boundary rows, one witness per
source-image face, and the two slack (hub-10 fan) witnesses produce the frozen `Feasible`.
The source-image list and the two slack faces are the C3 index facts above. -/
theorem feasible_of_source_image_and_fanB_completion {U : Fin 9 → Point} {C : Fin 11 → Point}
    {r : ℝ} (hr : 0 ≤ r) (hb : BoundaryRows U C r)
    (hsource : ∀ g : Fin 9, FaceWitness C (faceMap g) r)
    (hfan5 : FaceWitness C 5 r) (hfan7 : FaceWitness C 7 r) :
    ∃ Z : Fin 11 → Point, Feasible U C Z r :=
  feasible_of_canonical_source_and_hub10_fan_witnesses hr hb hsource hfan5 hfan7

/-- **C5-facing shim (`V2` consumer).** Same hypotheses give `V2 U ≤ r²` through the frozen
`oracle_le_feasible`. -/
theorem oracle_le_of_source_image_and_fanB_completion {U : Fin 9 → Point} {C : Fin 11 → Point}
    {r : ℝ} (hr : 0 ≤ r) (hb : BoundaryRows U C r)
    (hsource : ∀ g : Fin 9, FaceWitness C (faceMap g) r)
    (hfan5 : FaceWitness C 5 r) (hfan7 : FaceWitness C 7 r) :
    V2 U ≤ r ^ 2 :=
  oracle_le_of_source_and_hub10_fan_witnesses hr hb
    (fun g => (rawFaceWitness_iff C g r).2 (hsource g)) hfan5 hfan7

/-- **C5-facing shim, all-face form.** With the witness family stated over `Fin 11` directly
(no source/slack split at the call site), the same conclusion follows. -/
theorem feasible_of_all_face_witnesses {U : Fin 9 → Point} {C : Fin 11 → Point} {r : ℝ}
    (hr : 0 ≤ r) (hb : BoundaryRows U C r) (h : ∀ f : Fin 11, FaceWitness C f r) :
    ∃ Z : Fin 11 → Point, Feasible U C Z r := by
  obtain ⟨Z, hZ⟩ := exists_Z_of_faceWitnesses h
  refine ⟨Z, feasible_iff_canonical_rows.2 ⟨hr, ?_, ?_⟩⟩
  · intro p
    obtain ⟨i, side⟩ := p
    simpa [edgeLength, BoundaryRows] using hb i side
  · intro f v
    exact hZ f v

/-- **No repeated index bookkeeping (Feasible).**  A consumer that can name *any* covering list
`L` of canonical faces (i.e. `∀ f, L.contains f = true`) together with a witness for each face it
names gets the frozen `Feasible`; the source-image + slack split is then an *instance* of this,
not a requirement repeated at every call site. -/
theorem feasible_of_faceWitness_covering_list {U : Fin 9 → Point} {C : Fin 11 → Point} {r : ℝ}
    (hr : 0 ≤ r) (hb : BoundaryRows U C r) (L : List (Fin 11))
    (hcov : ∀ f : Fin 11, L.contains f = true)
    (hw : ∀ f : Fin 11, L.contains f = true → FaceWitness C f r) :
    ∃ Z : Fin 11 → Point, Feasible U C Z r :=
  feasible_of_all_face_witnesses hr hb (fun f => hw f (hcov f))

/-- **No repeated index bookkeeping (`V2` consumer).**  Same hypotheses give `V2 U ≤ r²`. -/
theorem oracle_le_of_faceWitness_covering_list {U : Fin 9 → Point} {C : Fin 11 → Point} {r : ℝ}
    (hr : 0 ≤ r) (hb : BoundaryRows U C r) (L : List (Fin 11))
    (hcov : ∀ f : Fin 11, L.contains f = true)
    (hw : ∀ f : Fin 11, L.contains f = true → FaceWitness C f r) :
    V2 U ≤ r ^ 2 := by
  obtain ⟨Z, hZ⟩ := feasible_of_faceWitness_covering_list hr hb L hcov hw
  exact ResumeNetwork.oracle_le_feasible hZ

/-- The source-image + slack list is an instance of the covering-list form: its coverage is the
C3 index fact `face_mem_source_or_slack`. -/
theorem source_plus_slack_covers :
    ∀ f : Fin 11, (sourceImageFaces ++ [5, 7]).contains f = true := by decide

/-- The row-level form of the same consumer: from the same hypotheses, all 33 interior rows hold
in C4's `RowConstraint` shape, and all 18 boundary rows hold. -/
theorem rowConstraints_of_source_image_and_fanB_completion {U : Fin 9 → Point}
    {C : Fin 11 → Point} {r : ℝ} (hr : 0 ≤ r) (hb : BoundaryRows U C r)
    (hsource : ∀ g : Fin 9, FaceWitness C (faceMap g) r)
    (hfan5 : FaceWitness C 5 r) (hfan7 : FaceWitness C 7 r) :
    ∃ Z : Fin 11 → Point,
      (∀ w : InteriorRow, RowConstraint U C Z r w) ∧
        (∀ i : Fin 9, ∀ side : Fin 2,
          edgeLength U C Z (Sum.inl (i, side) : Edge) ≤ r) := by
  obtain ⟨Z, hZ⟩ := feasible_of_source_image_and_fanB_completion hr hb hsource hfan5 hfan7
  exact ⟨Z, fun w => hZ.2 (Sum.inr (rowIdx w)), fun i side => hZ.2 (Sum.inl (i, side))⟩

end N11Formalization.DSHTopologyHubFanConsumer

/-! ## 5. Verbatim types and axiom audit -/

#check @N11Formalization.DSHTopologyHubFanConsumer.rowsOfFaces
#check @N11Formalization.DSHTopologyHubFanConsumer.interiorRow_edge_row
#check @N11Formalization.DSHTopologyHubFanConsumer.rowConstraint_edgeLength
#check @N11Formalization.DSHTopologyHubFanConsumer.row_counts
#check @N11Formalization.DSHTopologyHubFanConsumer.frozen_rows_covered
#check @N11Formalization.DSHTopologyHubFanConsumer.fan_row_blocks_exhaust
#check @N11Formalization.DSHTopologyHubFanConsumer.fan_row_blocks_disjoint
#check @N11Formalization.DSHTopologyHubFanConsumer.fanA_rows_are_hub9_side
#check @N11Formalization.DSHTopologyHubFanConsumer.fanB_rows_are_hub10_side
#check @N11Formalization.DSHTopologyHubFanConsumer.hub_pair_rows_exact
#check @N11Formalization.DSHTopologyHubFanConsumer.hub_site_rows_exact
#check @N11Formalization.DSHTopologyHubFanConsumer.no_hub_site_boundary_rows
#check @N11Formalization.DSHTopologyHubFanConsumer.sourceImageFaces_exact
#check @N11Formalization.DSHTopologyHubFanConsumer.source_complement_exact
#check @N11Formalization.DSHTopologyHubFanConsumer.fanB_source_complement
#check @N11Formalization.DSHTopologyHubFanConsumer.fanA_inside_source_image
#check @N11Formalization.DSHTopologyHubFanConsumer.slackFace_exact
#check @N11Formalization.DSHTopologyHubFanConsumer.face_mem_source_or_slack
#check @N11Formalization.DSHTopologyHubFanConsumer.completion_must_contain_slack
#check @N11Formalization.DSHTopologyHubFanConsumer.source_image_not_all_faces
#check @N11Formalization.DSHTopologyHubFanConsumer.fanA_plus_central_not_all_faces
#check @N11Formalization.DSHTopologyHubFanConsumer.hub_pair_rows_are_in_source_image
#check @N11Formalization.DSHTopologyHubFanConsumer.row_pair_image_eq_c3_faceRows
#check @N11Formalization.DSHTopologyHubFanConsumer.row_pair_image_distinct
#check @N11Formalization.DSHTopologyHubFanConsumer.feasible_of_faceWitness_covering_list
#check @N11Formalization.DSHTopologyHubFanConsumer.oracle_le_of_faceWitness_covering_list
#check @N11Formalization.DSHTopologyHubFanConsumer.source_plus_slack_covers
#check @N11Formalization.DSHTopologyHubFanConsumer.faceWitness_split_source_image_and_slack
#check @N11Formalization.DSHTopologyHubFanConsumer.feasible_of_source_image_and_fanB_completion
#check @N11Formalization.DSHTopologyHubFanConsumer.oracle_le_of_source_image_and_fanB_completion
#check @N11Formalization.DSHTopologyHubFanConsumer.feasible_of_all_face_witnesses
#check @N11Formalization.DSHTopologyHubFanConsumer.rowConstraints_of_source_image_and_fanB_completion

#print axioms N11Formalization.DSHTopologyHubFanConsumer.interiorRow_edge_row
#print axioms N11Formalization.DSHTopologyHubFanConsumer.rowConstraint_edgeLength
#print axioms N11Formalization.DSHTopologyHubFanConsumer.row_counts
#print axioms N11Formalization.DSHTopologyHubFanConsumer.frozen_rows_covered
#print axioms N11Formalization.DSHTopologyHubFanConsumer.face_boundary_rows_disjoint
#print axioms N11Formalization.DSHTopologyHubFanConsumer.fan_row_counts
#print axioms N11Formalization.DSHTopologyHubFanConsumer.fan_row_blocks_disjoint
#print axioms N11Formalization.DSHTopologyHubFanConsumer.fan_row_blocks_exhaust
#print axioms N11Formalization.DSHTopologyHubFanConsumer.fanA_rows_are_hub9_side
#print axioms N11Formalization.DSHTopologyHubFanConsumer.fanB_rows_are_hub10_side
#print axioms N11Formalization.DSHTopologyHubFanConsumer.hub_pair_rows_exact
#print axioms N11Formalization.DSHTopologyHubFanConsumer.hub_site_rows_exact
#print axioms N11Formalization.DSHTopologyHubFanConsumer.no_hub_site_boundary_rows
#print axioms N11Formalization.DSHTopologyHubFanConsumer.hub_site_rows_card
#print axioms N11Formalization.DSHTopologyHubFanConsumer.sourceImageFaces_exact
#print axioms N11Formalization.DSHTopologyHubFanConsumer.source_complement_exact
#print axioms N11Formalization.DSHTopologyHubFanConsumer.fanB_source_complement
#print axioms N11Formalization.DSHTopologyHubFanConsumer.fanA_inside_source_image
#print axioms N11Formalization.DSHTopologyHubFanConsumer.slackFace_exact
#print axioms N11Formalization.DSHTopologyHubFanConsumer.face_mem_source_or_slack
#print axioms N11Formalization.DSHTopologyHubFanConsumer.face_mem_source_or_slack
#print axioms N11Formalization.DSHTopologyHubFanConsumer.completion_must_contain_slack
#print axioms N11Formalization.DSHTopologyHubFanConsumer.source_image_not_all_faces
#print axioms N11Formalization.DSHTopologyHubFanConsumer.fanA_plus_central_not_all_faces
#print axioms N11Formalization.DSHTopologyHubFanConsumer.hub_pair_rows_are_in_source_image
#print axioms N11Formalization.DSHTopologyHubFanConsumer.row_pair_image_eq_c3_faceRows
#print axioms N11Formalization.DSHTopologyHubFanConsumer.row_pair_image_distinct
#print axioms N11Formalization.DSHTopologyHubFanConsumer.feasible_of_faceWitness_covering_list
#print axioms N11Formalization.DSHTopologyHubFanConsumer.oracle_le_of_faceWitness_covering_list
#print axioms N11Formalization.DSHTopologyHubFanConsumer.source_plus_slack_covers
#print axioms N11Formalization.DSHTopologyHubFanConsumer.faceWitness_split_source_image_and_slack
#print axioms N11Formalization.DSHTopologyHubFanConsumer.feasible_of_source_image_and_fanB_completion
#print axioms N11Formalization.DSHTopologyHubFanConsumer.oracle_le_of_source_image_and_fanB_completion
#print axioms N11Formalization.DSHTopologyHubFanConsumer.feasible_of_all_face_witnesses
#print axioms N11Formalization.DSHTopologyHubFanConsumer.rowConstraints_of_source_image_and_fanB_completion