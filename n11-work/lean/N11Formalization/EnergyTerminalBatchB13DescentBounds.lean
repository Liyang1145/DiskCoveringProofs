import N11Formalization.Paid16GeneralG03
import N11Formalization.Paid16GeneralG04
import N11Formalization.Paid16GeneralG05
import N11Formalization.Paid16GeneralG06
import N11Formalization.Paid16GeneralG07
import N11Formalization.Paid16GeneralG08
import N11Formalization.Paid16GeneralG09
import N11Formalization.Paid16GeneralG10
import N11Formalization.Paid16GeneralG11
import N11Formalization.Paid16GeneralG12
import N11Formalization.EnergyTerminalBatchB10
import N11Formalization.Paid16GeneralRemaining210

/-! Bounded descent facts used by B13. Each kernel decision covers at most
58 literal ids; the 210-id remainder is assembled from ten 21-id blocks. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13DescentBounds
open Finset
noncomputable section

private theorem g03_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG03.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG03.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g04_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG04.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG04.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g05_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG05.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG05.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g06_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG06.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG06.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g07_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG07.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG07.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g08_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG08.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG08.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g09_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG09.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG09.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g10_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG10.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG10.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g11_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG11.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG11.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g12_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG12.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG12.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

theorem b09_lt (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB09.paidIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ EnergyTerminalBatchB09.paidIDs, m.val < 2565 := by
    decide +kernel
  exact h n hn

theorem first42_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralFirst42.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralFirst42.newIDs, m.val < 2565 := by
    decide +kernel
  exact h n hn

theorem b10_lt (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB10.paidIDs) :
    n.val < 2565 := by
  rw [EnergyTerminalBatchB10.paidIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact b09_lt n hn
  · exact first42_lt n hn

theorem remaining210_lt (n : Fin 5011)
    (hn : n ∈ Paid16GeneralRemaining210.newIDs) : n.val < 2565 := by
  have hm : n ∈ Paid16GeneralG03.newIDs ∨
      n ∈ Paid16GeneralG04.newIDs ∨
      n ∈ Paid16GeneralG05.newIDs ∨
      n ∈ Paid16GeneralG06.newIDs ∨
      n ∈ Paid16GeneralG07.newIDs ∨
      n ∈ Paid16GeneralG08.newIDs ∨
      n ∈ Paid16GeneralG09.newIDs ∨
      n ∈ Paid16GeneralG10.newIDs ∨
      n ∈ Paid16GeneralG11.newIDs ∨
      n ∈ Paid16GeneralG12.newIDs := by
    simpa only [Paid16GeneralRemaining210.newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact g03_lt n hn
  · exact g04_lt n hn
  · exact g05_lt n hn
  · exact g06_lt n hn
  · exact g07_lt n hn
  · exact g08_lt n hn
  · exact g09_lt n hn
  · exact g10_lt n hn
  · exact g11_lt n hn
  · exact g12_lt n hn

end
end N11Formalization.EnergyTerminalBatchB13DescentBounds
#check @N11Formalization.EnergyTerminalBatchB13DescentBounds.b10_lt
#check @N11Formalization.EnergyTerminalBatchB13DescentBounds.remaining210_lt
#print axioms N11Formalization.EnergyTerminalBatchB13DescentBounds.b10_lt
#print axioms N11Formalization.EnergyTerminalBatchB13DescentBounds.remaining210_lt
