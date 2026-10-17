import N11Formalization.ActualRefinementFacetRetention

/-! The graph of the actual finite nearest-triangle refinement is connected
on ALL11 actual sites. Every true positive facet is retained, so the actual
connected positive-facet graph is a subgraph. No added connectedness premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementGraphConnected
open ActualVoronoiCells ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualPositiveFacetGraph ActualRefinementFacetRetention

def triangleGraph {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    SimpleGraph (Fin 11) where
  Adj i j := i ≠ j ∧ ∃ a : R.Index, i ∈ Set.range (R.labels a) ∧ j ∈ Set.range (R.labels a)
  symm := ⟨fun _ _ h => ⟨h.1.symm,by obtain ⟨a,hi,hj⟩ := h.2; exact ⟨a,hj,hi⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem positive_graph_subgraph {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    graph c ≤ triangleGraph R := by
  intro i j hij
  exact ⟨hij.1,Refinement.positive_pair_retained R h hr hij⟩

theorem actual_triangle_graph_connected {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (triangleGraph R).Connected :=
  SimpleGraph.Connected.mono (positive_graph_subgraph h hr R) (actual_graph_connected h)

end N11Formalization.ActualRefinementGraphConnected
#check @N11Formalization.ActualRefinementGraphConnected.actual_triangle_graph_connected
#print axioms N11Formalization.ActualRefinementGraphConnected.actual_triangle_graph_connected
