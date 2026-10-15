/-
n11-formalization — DSH line C4 groundwork, part 2 (teammate `topo-interior`, task-4).

# DSHTopologyInteriorInterface — the exact face-witness interface C1–C3/C5 must supply

Scope: **local groundwork, standalone**; lead integrates. No `Covers` premise is discharged and
no `Covers → Feasible` implication is claimed (that is C5, lead-side). This file only turns the
33-row enumeration of `DSHTopologyInteriorRows` into the *minimal, exactly typed* interface that
a canonical-cover construction must produce, using the frozen `Feasible` / `edgeLength` / `face`
objects verbatim.

The interface has three groups, matching the verified `27 + 6` split of the 33 interior rows:

1. `Fin 9` **source-face witnesses** — one point within `r` of the three canonical sites of each
   canonical face in the `faceMap` image (equivalently: of each raw source face's three sites);
2. **two hub-10 fan witnesses** — one point within `r` of the three sites of canonical face
   `5 = [5,6,10]` and of canonical face `7 = [7,8,10]`;
3. the **18 boundary rows** (frozen `anchorIndex` incidence).

This is strictly sharper than the single opaque hypothesis used inside the frozen witness table
(`FlashBoundaryCapsFaces.FaceCoverable u 0 1 10`, consumed by `faceOK_table`): here the two
non-source faces are named individually in the canonical `face` indexing, and the source faces
are named in the frozen source indexing, so no raw/canonical label confusion can enter.
-/
import N11Formalization.DSHTopologyInteriorRows

set_option autoImplicit false

namespace N11Formalization.DSHTopologyInterior

open N11Formalization ResumeNetwork ResumeLocalIncidence

/-! ## 1. One point per canonical face (the frozen `FaceCoverable` shape, canonical indexing) -/

/-- A face witness for the canonical face `f`: one point within `r` of all three of its sites.
This is the content of `FlashBoundaryCapsFaces.FaceCoverable` restricted to a canonical face
(its `Z f`, the free node of `edgeLength`). -/
def FaceWitness (C : Fin 11 → Point) (f : Fin 11) (r : ℝ) : Prop :=
  ∃ z : Point, ∀ v : Fin 3, dist (C (face f v)) z ≤ r

/-- Same shape, but indexed by a *raw* source face (the frozen `sourceFaces` table). -/
def RawFaceWitness (C : Fin 11 → Point) (g : Fin 9) (r : ℝ) : Prop :=
  ∃ z : Point, ∀ v : Fin 3, dist (C (ResumeGlobal.rawToCanon (sourceFaces g v))) z ≤ r

/-- The two indexings agree: a raw witness is a canonical witness for `faceMap g`. -/
theorem rawFaceWitness_iff (C : Fin 11 → Point) (g : Fin 9) (r : ℝ) :
    RawFaceWitness C g r ↔ FaceWitness C (faceMap g) r := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun v => ?_⟩
    rw [← faceMap_exact g v]
    exact hz v
  · rintro ⟨z, hz⟩
    refine ⟨z, fun v => ?_⟩
    rw [faceMap_exact g v]
    exact hz v

/-- A tag for the three kinds of rows, decided by the frozen source-table complement. -/
inductive RowKind
  | sourceFace
  | hub10Fan
deriving DecidableEq

theorem rowKind_decision (f : Fin 11) :
    ((∃ g : Fin 9, faceMap g = f) ∨ f = 5 ∨ f = 7) := by
  revert f
  decide

/-! ## 2. 33 rows from 11 face witnesses (one `Z` serves all rows of a face) -/

/-- All 33 canonical interior rows from one witness per canonical face. -/
theorem exists_Z_of_faceWitnesses {C : Fin 11 → Point} {r : ℝ}
    (h : ∀ f : Fin 11, FaceWitness C f r) :
    ∃ Z : Fin 11 → Point, ∀ f : Fin 11, ∀ v : Fin 3, dist (C (face f v)) (Z f) ≤ r := by
  choose Z hZ using h
  exact ⟨Z, fun f v => hZ f v⟩

/-- The 33 rows in the frozen `RowConstraint` shape, from the face witnesses. -/
theorem rowConstraints_of_faceWitnesses {U : Fin 9 → Point} {C : Fin 11 → Point} {r : ℝ}
    (h : ∀ f : Fin 11, FaceWitness C f r) :
    ∃ Z : Fin 11 → Point, ∀ w : InteriorRow, RowConstraint U C Z r w := by
  obtain ⟨Z, hZ⟩ := exists_Z_of_faceWitnesses h
  refine ⟨Z, fun w => ?_⟩
  rw [RowConstraint]
  exact hZ (rowFace w) (rowVertex w)

/-! ## 3. The exact C5-facing interface: 9 source-face + 2 hub-10-fan witnesses + 18 boundary -/

/-- Boundary half of `Feasible`, in the frozen `anchorIndex` incidence. -/
def BoundaryRows (U : Fin 9 → Point) (C : Fin 11 → Point) (r : ℝ) : Prop :=
  ∀ i : Fin 9, ∀ side : Fin 2, dist (C ⟨i.val, by omega⟩) (U (anchorIndex i side)) ≤ r

/-- **Main interface theorem.** The 9 source-face witnesses (raw source indexing), the two
hub-10 fan witnesses for canonical faces `5` and `7`, the 18 boundary rows and `0 ≤ r` produce
the frozen `Feasible U C Z r` for an explicit `Z`. Nothing else about the cover is used, and no
interior row is dropped: the six non-source rows are named separately and cannot be omitted. -/
theorem feasible_of_source_and_hub10_fan_witnesses {U : Fin 9 → Point} {C : Fin 11 → Point}
    {r : ℝ} (hr : 0 ≤ r) (hb : BoundaryRows U C r)
    (hsource : ∀ g : Fin 9, RawFaceWitness C g r)
    (hfan5 : FaceWitness C 5 r) (hfan7 : FaceWitness C 7 r) :
    ∃ Z : Fin 11 → Point, Feasible U C Z r := by
  have hAll : ∀ f : Fin 11, FaceWitness C f r := by
    intro f
    rcases rowKind_decision f with ⟨g, rfl⟩ | h57
    · exact (rawFaceWitness_iff C g r).1 (hsource g)
    · rcases h57 with rfl | rfl
      · exact hfan5
      · exact hfan7
  obtain ⟨Z, hZ⟩ := exists_Z_of_faceWitnesses hAll
  refine ⟨Z, feasible_iff_canonical_rows.2 ⟨hr, ?_, ?_⟩⟩
  · intro p
    obtain ⟨i, side⟩ := p
    simpa [edgeLength, BoundaryRows] using hb i side
  · intro f v
    exact hZ f v

/-- Variant with the source witnesses already given in canonical indexing. -/
theorem feasible_of_canonical_source_and_hub10_fan_witnesses {U : Fin 9 → Point}
    {C : Fin 11 → Point} {r : ℝ} (hr : 0 ≤ r) (hb : BoundaryRows U C r)
    (hsource : ∀ g : Fin 9, FaceWitness C (faceMap g) r)
    (hfan5 : FaceWitness C 5 r) (hfan7 : FaceWitness C 7 r) :
    ∃ Z : Fin 11 → Point, Feasible U C Z r :=
  feasible_of_source_and_hub10_fan_witnesses hr hb
    (fun g => (rawFaceWitness_iff C g r).2 (hsource g)) hfan5 hfan7

/-- Variant isolating the two rows that the source table does not realize: supplying **only**
the two hub-10 fan witnesses is enough on top of the source faces. (Restatement of the main
interface with the split made explicit.) -/
theorem hub10_fan_witnesses_needed (C : Fin 11 → Point) (r : ℝ) :
    (∀ f : Fin 11, FaceWitness C f r) ↔
      (∀ g : Fin 9, FaceWitness C (faceMap g) r) ∧ FaceWitness C 5 r ∧ FaceWitness C 7 r := by
  constructor
  · intro h
    exact ⟨fun g => h (faceMap g), h 5, h 7⟩
  · rintro ⟨hsrc, h5, h7⟩ f
    rcases rowKind_decision f with ⟨g, rfl⟩ | h57
    · exact hsrc g
    · rcases h57 with rfl | rfl
      · exact h5
      · exact h7

/-- **Frozen consumer**: the interface above drives `ResumeNetwork.oracle_le_feasible`, i.e. it
is exactly what C5 must instantiate to conclude `V2 U ≤ r²` for an arbitrary cover. -/
theorem oracle_le_of_source_and_hub10_fan_witnesses {U : Fin 9 → Point} {C : Fin 11 → Point}
    {r : ℝ} (hr : 0 ≤ r) (hb : BoundaryRows U C r)
    (hsource : ∀ g : Fin 9, RawFaceWitness C g r)
    (hfan5 : FaceWitness C 5 r) (hfan7 : FaceWitness C 7 r) :
    V2 U ≤ r ^ 2 := by
  obtain ⟨Z, hZ⟩ :=
    feasible_of_source_and_hub10_fan_witnesses hr hb hsource hfan5 hfan7
  exact ResumeNetwork.oracle_le_feasible hZ

/-- Negative control for the interface: dropping the two hub-10 fan witnesses makes the
hypothesis strictly weaker and the conclusion false in general (re-exported from the row module:
all 45 source-image rows can hold while a non-source row fails). -/
theorem hub10_fan_witness_not_removable :
    ∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
      (∀ e : Edge, (∃ s : SourceEdge, edgeMap s = e) → edgeLength U C Z e ≤ r) ∧
        ¬ (∀ w : InteriorRow, RowConstraint U C Z r w) :=
  slack_rows_not_implied_by_source_rows'

/-! ## 4. Verbatim types and axiom prints -/

#check @N11Formalization.DSHTopologyInterior.FaceWitness
#check @N11Formalization.DSHTopologyInterior.RawFaceWitness
#check @N11Formalization.DSHTopologyInterior.BoundaryRows
#check @N11Formalization.DSHTopologyInterior.rowKind_decision
#check @N11Formalization.DSHTopologyInterior.exists_Z_of_faceWitnesses
#check @N11Formalization.DSHTopologyInterior.rowConstraints_of_faceWitnesses
#check @N11Formalization.DSHTopologyInterior.feasible_of_source_and_hub10_fan_witnesses
#check @N11Formalization.DSHTopologyInterior.feasible_of_canonical_source_and_hub10_fan_witnesses
#check @N11Formalization.DSHTopologyInterior.hub10_fan_witnesses_needed
#check @N11Formalization.DSHTopologyInterior.oracle_le_of_source_and_hub10_fan_witnesses
#check @N11Formalization.DSHTopologyInterior.hub10_fan_witness_not_removable

#print axioms N11Formalization.DSHTopologyInterior.rawFaceWitness_iff
#print axioms N11Formalization.DSHTopologyInterior.rowKind_decision
#print axioms N11Formalization.DSHTopologyInterior.exists_Z_of_faceWitnesses
#print axioms N11Formalization.DSHTopologyInterior.rowConstraints_of_faceWitnesses
#print axioms N11Formalization.DSHTopologyInterior.feasible_of_source_and_hub10_fan_witnesses
#print axioms N11Formalization.DSHTopologyInterior.feasible_of_canonical_source_and_hub10_fan_witnesses
#print axioms N11Formalization.DSHTopologyInterior.hub10_fan_witnesses_needed
#print axioms N11Formalization.DSHTopologyInterior.oracle_le_of_source_and_hub10_fan_witnesses

end N11Formalization.DSHTopologyInterior
