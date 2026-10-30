import N11Formalization.EnergyTerminalBatchB13
import N11Formalization.EnergyRefineN2341

/-! Refine the B13 paid set by the validated split certificate for source
terminal 2341.  This raises the paid count from 1997 to 1998 and removes exactly
the newly paid singleton from the explicit remaining-radius premise.  The
389-to-388 census cardinality is diagnostic and is not proved here. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13Refine2341
open Finset
noncomputable section

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13.paidIDs ∪ EnergyRefineN2341.newIDs

theorem not_paid_2341 : (2341 : Fin 5011) ∉ EnergyTerminalBatchB13.paidIDs := by
  intro h
  rw [EnergyTerminalBatchB13.paidIDs, Finset.mem_union] at h
  rcases h with h12 | h1182
  · rw [EnergyTerminalBatchB12.paidIDs, Finset.mem_union] at h12
    rcases h12 with h11 | h505
    · have h11' : (2341 : Fin 5011) ∉ EnergyTerminalBatchB11.paidIDs := by
        decide +kernel
      exact h11' h11
    · have h505' : (2341 : Fin 5011) ∉ Paid16GeneralNext505.newIDs := by
        decide +kernel
      exact h505' h505
  · have hge := Paid16GeneralNext1182.lower_bound (2341 : Fin 5011) h1182
    have hval : (2341 : Fin 5011).val = 2341 := rfl
    omega

theorem new_disjoint_old :
    Disjoint EnergyTerminalBatchB13.paidIDs EnergyRefineN2341.newIDs := by
  rw [EnergyRefineN2341.newIDs, Finset.disjoint_left]
  intro a ha hb
  have ha' : a = 2341 := by simpa using hb
  subst a
  exact not_paid_2341 ha

theorem new_count : EnergyRefineN2341.newIDs.card = 1 := by
  simp [EnergyRefineN2341.newIDs]

theorem paid_count : paidIDs.card = 1998 := by
  rw [paidIDs, Finset.card_union_of_disjoint new_disjoint_old,
    EnergyTerminalBatchB13.paid_count, new_count]

theorem paid_terminal (n : Fin 5011) (hn : n ∈ paidIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13.paid_terminal n hn
  · exact EnergyRefineN2341.new_terminal n hn

theorem paid_radius (n : Fin 5011) (hn : n ∈ paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13.paid_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN2341.new_radius n hn y hy0 hy1 hc C Z r hf

def residualIDs : Finset (Fin 5011) :=
  (Finset.univ.filter fun n => (DBMSourceTree.data n).terminal = true).filter
    fun n => n ∉ Patch120SharpDispatch.sharpIDs ∧ n ∉ paidIDs

theorem not_sharp_2341 :
    (2341 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  decide +kernel

theorem residualIDs_eq_b13_erase :
    residualIDs = EnergyTerminalBatchB13.residualIDs.erase 2341 := by
  ext n
  simp [residualIDs, paidIDs, EnergyTerminalBatchB13.residualIDs,
    and_assoc, and_left_comm, and_comm]

/-- The 389-to-388 census count, conditional on the explicit B13 census.  The
count itself is not used as a cached proof of any residual radius bound. -/
theorem residual_card_of_census
    (hcensus : EnergyTerminalBatchB13.residualIDs.card = 389) :
    residualIDs.card = 388 := by
  have hmem : (2341 : Fin 5011) ∈ EnergyTerminalBatchB13.residualIDs := by
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff]
    exact ⟨EnergyRefineN2341.terminal, not_sharp_2341, not_paid_2341⟩
  rw [residualIDs_eq_b13_erase, Finset.card_erase_of_mem hmem, hcensus]
  norm_num

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011, (DBMSourceTree.data n).terminal = true →
    n ∉ Patch120SharpDispatch.sharpIDs → n ∉ paidIDs →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r →
          SourceExactRoot.sourceRadius ≤ r

/-- The refined premise implies the B13 premise: the newly paid singleton is
discharged by its split certificate. -/
theorem remaining_of (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  intro n ht hs hp y hy0 hy1 hc C Z r hf
  by_cases hn : n ∈ EnergyRefineN2341.newIDs
  · exact (EnergyRefineN2341.new_radius n hn y hy0 hy1 hc C Z r hf).le
  · have hrest := h n ht hs (by
      intro hpn
      rcases Finset.mem_union.mp hpn with hpb | hpn
      · exact hp hpb
      · exact hn hpn)
    exact hrest y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13Refine2341
#check @N11Formalization.EnergyTerminalBatchB13Refine2341.paid_count
#check @N11Formalization.EnergyTerminalBatchB13Refine2341.paid_radius
#check @N11Formalization.EnergyTerminalBatchB13Refine2341.remaining_of
#check @N11Formalization.EnergyTerminalBatchB13Refine2341.residual_card_of_census
#print axioms N11Formalization.EnergyTerminalBatchB13Refine2341.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB13Refine2341.remaining_of
