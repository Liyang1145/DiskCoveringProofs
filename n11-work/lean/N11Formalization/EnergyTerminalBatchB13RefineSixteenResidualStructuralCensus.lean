import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCard

/-! Lane-B structural interface to the 373-id refined residual.

The previous literal census repeated a full `residualIDs` kernel decision over
501 ten-index sub-blocks and exceeded the CI runner's memory budget.  The
terminal-census bridge now derives the same cardinality from twenty bounded
blocks, so this module only re-exports that result.  It pays no radius. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus
open Finset
noncomputable section

def residual373 : Finset (Fin 5011) :=
  EnergyTerminalBatchB13RefineSixteenResidual.residualIDs

theorem residualIDs_eq_residual373 :
    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs = residual373 := rfl

theorem residual373_card : residual373.card = 373 :=
  EnergyTerminalBatchB13RefineSixteenResidual.residualIDs_card

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.residualIDs_eq_residual373
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.residual373_card
