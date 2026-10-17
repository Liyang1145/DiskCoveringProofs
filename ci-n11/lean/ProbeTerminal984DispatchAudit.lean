import N11Formalization

/-! Root imported own984 semantic chain/commonchart/dispatch and real controls.
All51 primal witnesses retained, remaining-terminal premise printed in full. -/
set_option autoImplicit false
open N11Formalization SourceChartIsometry
#check @EnergyCommonChart.actual_L
#check @EnergyCommonChart.actual_D
#check @EnergyCommonChart.anchors_identity
#check @EnergyCommonChart.paid_energy_radius
#check @DSHTerminalBatchL0G1Zplus984.all_lines
#check @DSHTerminalBatchL0G1Zplus984.pair_minorant
#check @Terminal984Angles.endpoint_binding
#check @Terminal984Angles.angles_in_cell
#check @Terminal984Oracle.cl_nonpos
#check @Terminal984Oracle.f0_lower
#check @Terminal984Oracle.g_nonneg
#check @Terminal562Oracle.W_field10
#check @Leaf4348Fields7.source_energy_le_oracle
#check @Terminal984Oracle.energy_gt_on_cell
#check @Terminal984Oracle.energy_le_oracle
#check @Terminal984Oracle.common_chart_radius
#check @EnergyTerminalDispatch.paid_count
#check @EnergyTerminalDispatch.paid_not_sharp
#check @EnergyTerminalDispatch.paid_terminal
#check @EnergyTerminalDispatch.paid_radius
#check @EnergyTerminalDispatch.chart_radius_of_remaining
#print EnergyTerminalDispatch.RemainingTerminalRadius
#print Terminal984Oracle.energy
#print SourceChartIsometry.chartAnchors
#print ResumeNetwork.Feasible
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms EnergyCommonChart.paid_energy_radius
#print axioms DSHTerminalBatchL0G1Zplus984.pair_minorant
#print axioms Terminal984Angles.angles_in_cell
#print axioms Terminal984Oracle.energy_gt_on_cell
#print axioms Terminal984Oracle.energy_le_oracle
#print axioms Terminal984Oracle.common_chart_radius
#print axioms EnergyTerminalDispatch.paid_radius
#print axioms EnergyTerminalDispatch.chart_radius_of_remaining

example (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 984)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius<r :=
  Terminal984Oracle.common_chart_radius y hy0 hc C Z r hf

example (n : Fin 5011) (hn : n∈EnergyTerminalDispatch.paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius<r :=
  EnergyTerminalDispatch.paid_radius n hn y hy0 hy1 hc C Z r hf

section
-- Finite calibration only; default heartbeats/kernel unchanged.
set_option maxRecDepth 10000
namespace Terminal984Nonempty
def YN : Fin 9 → ℚ := ![1,0,0,2,1,1,0,0,3]/8
def y : Fin 9 → ℝ := fun i => (YN i : ℝ)
private theorem rational_rows (i j : Fin 10) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),YN q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),YN q)≤
        (DBMSourceTree.node984.db i j : ℚ)/4096 := by
  fin_cases i <;> fin_cases j <;> decide +kernel
theorem real_cell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 984)
    (FlashLeafSplit.tlift y) := by
  have he : DBMSourceTree.data (984 : Fin 5011)=DBMSourceTree.node984 := rfl
  intro i j
  rw [show DBMTreeKernel.matrix DBMSourceTree.data 4096 984 i j=
    (DBMSourceTree.node984.db i j : ℝ)/4096 from by rw [DBMTreeKernel.matrix,he]; norm_num]
  change (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),(YN q : ℝ))-
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),(YN q : ℝ))≤
      (DBMSourceTree.node984.db i j : ℝ)/4096
  exact_mod_cast rational_rows i j
theorem simplex : (∀ i,0≤y i) ∧ ∑ i : Fin 9,y i=1 := by
  have h0 : ∀ i : Fin 9,(0 : ℚ)≤YN i := by decide +kernel
  have h1 : (∑ i : Fin 9,YN i)=1 := by decide +kernel
  constructor
  · intro i; change (0 : ℝ)≤(YN i : ℝ); exact_mod_cast h0 i
  · change (∑ i : Fin 9,(YN i : ℝ))=1
    have h := congrArg (fun q : ℚ => (q : ℝ)) h1
    simpa only [Rat.cast_sum,Rat.cast_one] using h
end Terminal984Nonempty
#check @Terminal984Nonempty.real_cell
#print axioms Terminal984Nonempty.real_cell
example : (FlashCosineLeaf284Bridge.T : ℝ)^2<
    ResumeNetwork.V2 (chartAnchors Terminal984Nonempty.y) :=
  Terminal984Oracle.common_chart_oracle_gt Terminal984Nonempty.y
    Terminal984Nonempty.simplex.1 Terminal984Nonempty.real_cell

example : EnergyTerminalDispatch.paidIDs.card=4 := EnergyTerminalDispatch.paid_count
example : (984 : Fin 5011)∈EnergyTerminalDispatch.paidIDs := by decide +kernel
example : (984 : Fin 5011)∉Patch120SharpDispatch.sharpIDs := by decide +kernel
example : (1112 : Fin 5011)∉EnergyTerminalDispatch.paidIDs := by decide +kernel
example : (DBMSourceTree.data (984 : Fin 5011)).db≠(DBMSourceTree.data (562 : Fin 5011)).db :=
  Terminal984Oracle.wrong_cell_rejected
example : DSHTerminalBatchL0G1Zplus984.PA 0≠DSHTerminalBatchL0G1Zplus562.PA 0 ∨
    DSHTerminalBatchL0G1Zplus984.PB 0≠DSHTerminalBatchL0G1Zplus562.PB 0 := by decide +kernel
-- True field weight comparison is universal, not a given source premise.
example (k : Fin 36) :
    (Terminal562Oracle.W k : ℝ)≤2*Leaf4348Fields7.weight 0 k :=
  Terminal562Oracle.W_field10 k
example : ¬ ((FlashCosineLeaf284Bridge.T : ℚ)^2<
    ∑ k : Fin 36,(0 : ℚ)*(1-(0 : ℚ))) := by decide +kernel
example : (ResumeNetwork.face 5 2).val=10 := by decide
example : Fintype.card ResumeNetwork.Edge=51 := by decide
example : SourceExactRoot.sourceRadius=SourceExactRoot.sourceRoot 6 := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment
end
