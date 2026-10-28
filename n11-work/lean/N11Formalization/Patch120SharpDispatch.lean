import N11Formalization.Patch120DomainPacket
import N11Formalization.DBMTreeChartConsumer

/-! Actual dispatch of all120 frozen sharp cells. All other terminal semantics
remain EXPLICIT, not inferred from tree validity or numerical status labels.
Arbitrary Covers->chart/all51 Feasible is still a separate global obligation. -/
set_option autoImplicit false
namespace N11Formalization.Patch120SharpDispatch
open N11Formalization SourceChartIsometry Patch120DomainPacket
noncomputable section

def sharpIDs : Finset (Fin 5011) := Finset.univ.image patchID

theorem sharp_count : sharpIDs.card=120 := by
  rw [sharpIDs,Finset.card_image_of_injective _ patchID_injective]
  decide

theorem sharp_terminal (n : Fin 5011) (hn : n∈sharpIDs) :
    (DBMSourceTree.data n).terminal=true := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hn
  exact (all_members p).1

theorem sharp_norm (n : Fin 5011) (hn : n∈sharpIDs) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ j : Fin 9,displacement y j^2)≤(729/50000 : ℝ) := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hn
  exact actual_norm p y hc

theorem sharp_gain (n : Fin 5011) (hn : n∈sharpIDs) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) :
    (∑ j : Fin 9,displacement y j^2)/100000≤
      ResumeNetwork.V2 (chartAnchors y)-SourceExactRoot.sourceRadius^2 := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hn
  exact actual_gain p y hc

/-- Actual branch consumer indexed by real source tree ID, not a given local
norm or an unproved geometric gain hypothesis. -/
theorem sharp_radius (n : Fin 5011) (hn : n∈sharpIDs) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius≤r := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hn
  exact actual_radius p y hc C Z r hf

/-- Exact remaining semantic interface. No claim that non-sharp terminals are
paid by numerical terminal flags, branch status or previous three examples. -/
def OtherTerminalRadius : Prop :=
  ∀ n : Fin 5011,(DBMSourceTree.data n).terminal=true → n∉sharpIDs →
    ∀ (y : Fin 9 → ℝ),
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius≤r

/-- Sharp branch is fully discharged; OTHER terminal semantics remain honest.
This conditional whole-simplex theorem is NOT an unconditional global bound. -/
theorem chart_radius_of_other_terminals (hother : OtherTerminalRadius)
    (y : Fin 9 → ℝ) (hy0 : ∀ i,0≤y i) (hy1 : ∑ i,y i=1)
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius≤r := by
  obtain ⟨n,ht,hc⟩ := DBMTreeChartConsumer.chart9_terminal_cover y hy0 hy1
  by_cases hn : n∈sharpIDs
  · exact sharp_radius n hn y hc C Z r hf
  · exact hother n ht hn y hc C Z r hf

end
end N11Formalization.Patch120SharpDispatch
#check @N11Formalization.Patch120SharpDispatch.sharp_count
#check @N11Formalization.Patch120SharpDispatch.sharp_radius
#check @N11Formalization.Patch120SharpDispatch.chart_radius_of_other_terminals
#print axioms N11Formalization.Patch120SharpDispatch.sharp_radius
