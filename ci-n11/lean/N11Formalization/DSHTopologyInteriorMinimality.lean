/-
n11-formalization — DSH line C4 groundwork, part 4 (teammate `topo-interior`, task-4).

# DSHTopologyInteriorMinimality — no face block and neither half of the 51 rows is redundant

Scope: **local groundwork, standalone**; lead integrates. No `Covers` premise, no
`Covers → Feasible` claim (C5, lead-side).

The C4 obligations forbid deleting rows from the canonical51 table (in particular the six primal
rows of the two slack faces). Prose prohibitions are not kernel evidence, so this file supplies
the kernel certificates that each block of the table is *load-bearing*:

* `face_block_not_redundant` — for **each** of the 11 canonical faces, there is a configuration
  in which every row of every *other* face holds while some row of that face fails. So no face
  block (hence none of the 33 rows as a block) can be dropped from the table.
* `interior_not_implied_by_boundary` / `boundary_not_implied_by_interior` — the 18 boundary rows
  and the 33 interior rows are mutually independent: either half can hold while the other fails.
  Hence neither half may be dropped, and the source's 45 carrying rows cannot stand in for the
  interior half (complementing `slack_rows_not_implied_by_source_rows'`).

All witnesses are explicit and interval-free; the only non-degeneracy fact used is
`one_zero_ne : (!₂[1,0] : Point) ≠ 0`, proved in the row module.
-/
import N11Formalization.DSHTopologyInteriorInterface

set_option autoImplicit false

namespace N11Formalization.DSHTopologyInterior

open N11Formalization ResumeNetwork ResumeLocalIncidence

/-- A ready-made nonzero point of the frozen `Point` type. -/
def probePoint : Point := !₂[(1 : ℝ), 0]

theorem probePoint_ne : probePoint ≠ 0 := one_zero_ne

theorem dist_probePoint_pos : 0 < dist (0 : Point) probePoint :=
  dist_pos.mpr (Ne.symm probePoint_ne)

/-! ## 1. No canonical face block is redundant -/

/-- **Per-face non-redundancy.** For every canonical face `f` there is `(U, C, Z, r)` such that
all rows of the *other* 10 faces hold while some row of face `f` fails. The witness is explicit:
`r = 0`, all centres at the origin, and only the free node `Z f` displaced. -/
theorem face_block_not_redundant (f : Fin 11) :
    ∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
      (∀ g : Fin 11, g ≠ f → ∀ v : Fin 3, dist (C (face g v)) (Z g) ≤ r) ∧
        ¬ (∀ v : Fin 3, dist (C (face f v)) (Z f) ≤ r) := by
  refine ⟨fun _ => 0, fun _ => 0, fun g => if g = f then probePoint else 0, 0, ?_, ?_⟩
  · intro g hg v
    have h : (if g = f then probePoint else (0 : Point)) = 0 := by simp [hg]
    simp [h]
  · intro h
    have h0 := h 0
    have hZ : (if f = f then probePoint else (0 : Point)) = probePoint := by simp
    have h0' : dist (0 : Point) probePoint ≤ 0 := by simpa [hZ] using h0
    exact absurd h0' (not_le.mpr dist_probePoint_pos)

/-- Existential form: some face block is load-bearing. -/
theorem some_face_block_not_redundant :
    ∃ f : Fin 11, ∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
      (∀ g : Fin 11, g ≠ f → ∀ v : Fin 3, dist (C (face g v)) (Z g) ≤ r) ∧
        ¬ (∀ v : Fin 3, dist (C (face f v)) (Z f) ≤ r) :=
  ⟨5, face_block_not_redundant 5⟩

/-- **Both slack faces are load-bearing in particular**: for `f = 5` and `f = 7` the other 30
interior rows can hold while a row of that face fails. Zero stress weight does not make the
primal row removable. -/
theorem slack_face_blocks_not_redundant :
    (∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
      (∀ g : Fin 11, g ≠ 5 → ∀ v : Fin 3, dist (C (face g v)) (Z g) ≤ r) ∧
        ¬ (∀ v : Fin 3, dist (C (face 5 v)) (Z 5) ≤ r)) ∧
      (∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
        (∀ g : Fin 11, g ≠ 7 → ∀ v : Fin 3, dist (C (face g v)) (Z g) ≤ r) ∧
          ¬ (∀ v : Fin 3, dist (C (face 7 v)) (Z 7) ≤ r)) :=
  ⟨face_block_not_redundant 5, face_block_not_redundant 7⟩

/-! ## 2. The 18 boundary rows and the 33 interior rows are mutually independent -/

/-- **The interior half does not imply the boundary half**: all 33 interior rows can hold while a
boundary row fails (`r = 0`, centres at the origin, one displaced anchor). -/
theorem interior_not_implied_by_boundary :
    ∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
      (∀ w : InteriorRow, RowConstraint U C Z r w) ∧ ¬ BoundaryRows U C r := by
  refine ⟨fun _ => probePoint, fun _ => 0, fun _ => 0, 0, ?_, ?_⟩
  · intro w
    rw [RowConstraint]
    simp only [edgeLength, dist_self, le_refl]
  · intro h
    have h0 := h 0 0
    have h0' : dist (0 : Point) probePoint ≤ 0 := by simpa using h0
    exact absurd h0' (not_le.mpr dist_probePoint_pos)

/-- **The boundary half does not imply the interior half**: all 18 boundary rows can hold while an
interior row fails (`r = 0`, centres and anchors at the origin, one displaced free node). -/
theorem boundary_not_implied_by_interior :
    ∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
      BoundaryRows U C r ∧ ¬ (∀ w : InteriorRow, RowConstraint U C Z r w) := by
  refine ⟨fun _ => 0, fun _ => 0, fun g => if g = 5 then probePoint else 0, 0, ?_, ?_⟩
  · intro i side
    simp
  · intro h
    have h5 := h (Sum.inr ((0 : Fin 2), (0 : Fin 3)))
    have hZ : (if (5 : Fin 11) = 5 then probePoint else (0 : Point)) = probePoint := by simp
    have h' : dist (0 : Point) probePoint ≤ 0 := by
      simpa [RowConstraint, rowIdx, slackFace, edgeLength, hZ] using h5
    exact absurd h' (not_le.mpr dist_probePoint_pos)

/-! ## 3. Summary certificate -/

/-- **Load-bearing certificate for the canonical51 table.** Each of the 11 face blocks is
non-redundant, and the boundary/interior halves are mutually independent — so the frozen
`Feasible` is not equivalent to any table obtained by dropping a face block or either half. -/
theorem all_rows_load_bearing :
    (∀ f : Fin 11, ∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
      (∀ g : Fin 11, g ≠ f → ∀ v : Fin 3, dist (C (face g v)) (Z g) ≤ r) ∧
        ¬ (∀ v : Fin 3, dist (C (face f v)) (Z f) ≤ r)) ∧
      (∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
        (∀ w : InteriorRow, RowConstraint U C Z r w) ∧ ¬ BoundaryRows U C r) ∧
      (∃ (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ),
        BoundaryRows U C r ∧ ¬ (∀ w : InteriorRow, RowConstraint U C Z r w)) :=
  ⟨face_block_not_redundant, interior_not_implied_by_boundary,
    boundary_not_implied_by_interior⟩

/-! ## 4. Verbatim types and axiom prints -/

#check @N11Formalization.DSHTopologyInterior.probePoint
#check @N11Formalization.DSHTopologyInterior.face_block_not_redundant
#check @N11Formalization.DSHTopologyInterior.slack_face_blocks_not_redundant
#check @N11Formalization.DSHTopologyInterior.interior_not_implied_by_boundary
#check @N11Formalization.DSHTopologyInterior.boundary_not_implied_by_interior
#check @N11Formalization.DSHTopologyInterior.all_rows_load_bearing

#print axioms N11Formalization.DSHTopologyInterior.face_block_not_redundant
#print axioms N11Formalization.DSHTopologyInterior.slack_face_blocks_not_redundant
#print axioms N11Formalization.DSHTopologyInterior.interior_not_implied_by_boundary
#print axioms N11Formalization.DSHTopologyInterior.boundary_not_implied_by_interior
#print axioms N11Formalization.DSHTopologyInterior.all_rows_load_bearing

end N11Formalization.DSHTopologyInterior