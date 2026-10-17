import N11Formalization.SourceFineCompactStressIntervals
import N11Formalization.SourceH20ResidualProposal

/-! ALL180 kernel integer checks for the same correlated C(rhs-M*y) residual.
Only certified stress endpoints are refined; C, y, incidence, column order
and true source matrix remain unchanged. Real semantics are a separate layer. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineH20ResidualProposal
open N11Formalization ResumeLocalIncidence HarmonicSourceTransport
open SourceFineCompactStressIntervals SourceH20ResidualProposal

def EL (i : Fin 20) (j : Fin 9) : ℤ :=
  -(∑ e : SourceEdge,
    if 0 ≤ multiplierN i j e then hiN (srcFlat e)*multiplierN i j e
    else loN (srcFlat e)*multiplierN i j e)
def EH (i : Fin 20) (j : Fin 9) : ℤ :=
  -(∑ e : SourceEdge,
    if 0 ≤ multiplierN i j e then loN (srcFlat e)*multiplierN i j e
    else hiN (srcFlat e)*multiplierN i j e)
def columnCheck (j : Fin 9) : Prop :=
  ∀ i : Fin 20,max |EL i j| |EH i j| ≤ 62500000000000000000

private theorem col0 : columnCheck 0 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col1 : columnCheck 1 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col2 : columnCheck 2 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col3 : columnCheck 3 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col4 : columnCheck 4 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col5 : columnCheck 5 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col6 : columnCheck 6 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col7 : columnCheck 7 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col8 : columnCheck 8 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel

theorem all_columns (i : Fin 20) (j : Fin 9) :
    max |EL i j| |EH i j| ≤ 62500000000000000000 := by
  fin_cases j
  · exact col0 i
  · exact col1 i
  · exact col2 i
  · exact col3 i
  · exact col4 i
  · exact col5 i
  · exact col6 i
  · exact col7 i
  · exact col8 i

end N11Formalization.SourceFineH20ResidualProposal
#check @N11Formalization.SourceFineH20ResidualProposal.all_columns
#print axioms N11Formalization.SourceFineH20ResidualProposal.all_columns
