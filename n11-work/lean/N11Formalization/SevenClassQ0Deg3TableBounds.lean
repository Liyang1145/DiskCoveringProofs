import N11Formalization.SevenClassQ0Deg3EdgeShape
import N11Formalization.SevenClassQ0Deg3SectorAssembler

/-! Lane A: the nine sector and twenty-one edge table families in one interface.

The edge shape proof and the sector-bin assembler establish the two independent
2049-point tables.  This module combines them without identifying either with
an actual refinement edge set; that geometric identification remains explicit
at the consumer.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3TableBounds

open MetricAreaRationalCertificate
open SevenClassQ0Deg3EdgeShape
open SevenClassQ0Deg3EndpointChecks
open SevenClassQ0Deg3SectorAssembler
open SevenClassQ0Deg3UpperTables

theorem tableEdges_injective : Function.Injective tableEdges := by
  decide

theorem edgeMax_tableEdges (i : Fin 21) : edgeMax (tableEdges i) = edgeMaxAt i := by
  unfold edgeMax
  rw [dif_pos ⟨i, rfl⟩]
  congr 1
  exact tableEdges_injective (Classical.choose_spec ⟨i, rfl⟩).symm

/-- All table maxima hold at every node of the fixed `2048`-grid, and every
node satisfies the exact piecewise-constant `NodeValid` table. -/
structure TableBounds : Prop where
  edge : EdgeValid
  sector : SectorValid
  node : ∀ k : Fin 2049,
    NodeValid (nodeQ RatInterval.piHi 2048 k) (nodeBin k)

theorem tableBounds : TableBounds :=
  ⟨edgeValid, sectorValid, allNodeValid⟩

end N11Formalization.SevenClassQ0Deg3TableBounds
#check @N11Formalization.SevenClassQ0Deg3TableBounds.edgeMax_tableEdges
#check @N11Formalization.SevenClassQ0Deg3TableBounds.tableBounds
#print axioms N11Formalization.SevenClassQ0Deg3TableBounds.edgeMax_tableEdges
#print axioms N11Formalization.SevenClassQ0Deg3TableBounds.tableBounds
