import N11Formalization

/-! Root imported REAL convex/DBM/angular core and actual2162/2166 consumers.
Remaining closed-chart semantics and original global Covers premise explicit. -/
set_option autoImplicit false
open N11Formalization SourceChartIsometry
#check @ConvexMinorantCore.endpointLo_sound
#check @ConvexMinorantCore.affine_identity
#check @ConvexMinorantCore.affine_f0_lower
#check @ConvexMinorantCore.mixWeight_cast
#check @ConvexMinorantCore.energy_eq_mixture
#check @ConvexMinorantCore.weightedEnergy_le_oracle
#check @ConvexMinorantCore.radius_of_minorants
#print ConvexMinorantCore.weightQ
#print ConvexMinorantCore.mixWeight
#check @DBMMinorantDual.row_sum
#check @DBMMinorantDual.rows_of_cell
#check @DBMMinorantDual.reduced_cost
#check @DBMMinorantDual.affine_lower_of_dual
#check @DBMMinorantDual.radius_of_dual
#print DBMMinorantDual.rowA
#print DBMMinorantDual.db
#print DBMMinorantDual.lower
#check @DBMAngleProvider.angles_of_endpoints
#check @Terminal2162Minorants.right_sin_bound
#check @Terminal2162Minorants.all_lines
#check @Terminal2162Minorants.pair_minorant
#check @TerminalDualConsumers.W_mix
#check @TerminalDualConsumers.Own2162.endpoint_binding
#check @TerminalDualConsumers.Own2162.numeric_check
#check @TerminalDualConsumers.Own2162.oracle_gt
#check @TerminalDualConsumers.Own2162.common_chart_radius
#check @TerminalDualConsumers.Own2166.lam_pos
#check @TerminalDualConsumers.Own2166.zero_dual_fails
#check @TerminalDualConsumers.Own2166.common_chart_radius
#check @EnergyTerminalBatchB02.paid_count
#check @EnergyTerminalBatchB02.paid_not_sharp
#check @EnergyTerminalBatchB02.paid_terminal
#check @EnergyTerminalBatchB02.paid_radius
#check @EnergyTerminalBatchB02.chart_radius_of_remaining
#print EnergyTerminalBatchB02.RemainingTerminalRadius
#print ResumeNetwork.Feasible
#check @Leaf4348Fields7.source_energy_le_oracle
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms ConvexMinorantCore.weightedEnergy_le_oracle
#print axioms ConvexMinorantCore.radius_of_minorants
#print axioms DBMMinorantDual.row_sum
#print axioms DBMMinorantDual.affine_lower_of_dual
#print axioms DBMMinorantDual.radius_of_dual
#print axioms DBMAngleProvider.angles_of_endpoints
#print axioms Terminal2162Minorants.right_sin_bound
#print axioms Terminal2162Minorants.pair_minorant
#print axioms TerminalDualConsumers.Own2162.common_chart_radius
#print axioms TerminalDualConsumers.Own2166.common_chart_radius
#print axioms EnergyTerminalBatchB02.paid_radius
#print axioms EnergyTerminalBatchB02.chart_radius_of_remaining

example (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2162)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  TerminalDualConsumers.Own2162.common_chart_radius y hy0 hy1 hc C Z r hf
example (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2166)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  TerminalDualConsumers.Own2166.common_chart_radius y hy0 hy1 hc C Z r hf
example (n : Fin 5011) (hn : n∈EnergyTerminalBatchB02.paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  EnergyTerminalBatchB02.paid_radius n hn y hy0 hy1 hc C Z r hf

section
set_option maxRecDepth 10000
namespace DualNonempty2162
def Y : Fin 9 → ℚ := ![1,1,0,94,32,0,18,14,96]/256
def y : Fin 9 → ℝ := fun q => (Y q : ℝ)
private theorem rational_rows (i j : Fin 10) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y q)≤
        (DBMSourceTree.node2162.db i j : ℚ)/4096 := by
  fin_cases i <;> fin_cases j <;> decide +kernel
theorem real_cell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2162)
    (FlashLeafSplit.tlift y) := by
  have he : DBMSourceTree.data (2162 : Fin 5011)=DBMSourceTree.node2162 := rfl
  intro i j
  rw [show DBMTreeKernel.matrix DBMSourceTree.data 4096 2162 i j=
    (DBMSourceTree.node2162.db i j : ℝ)/4096 from by rw [DBMTreeKernel.matrix,he]; norm_num]
  change (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),(Y q : ℝ))-
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),(Y q : ℝ))≤
      (DBMSourceTree.node2162.db i j : ℝ)/4096
  exact_mod_cast rational_rows i j
theorem simplex : (∀ q,0≤y q) ∧ ∑ q : Fin 9,y q=1 := by
  have h0 : ∀ q : Fin 9,(0 : ℚ)≤Y q := by decide +kernel
  have h1 : (∑ q : Fin 9,Y q)=1 := by decide +kernel
  constructor
  · intro q; change (0 : ℝ)≤(Y q : ℝ); exact_mod_cast h0 q
  · change (∑ q : Fin 9,(Y q : ℝ))=1
    have h := congrArg (fun t : ℚ => (t : ℝ)) h1
    simpa only [Rat.cast_sum,Rat.cast_one] using h
end DualNonempty2162
#print axioms DualNonempty2162.real_cell
example : (FlashCosineLeaf284Bridge.T : ℝ)^2 <
    ResumeNetwork.V2 (chartAnchors DualNonempty2162.y) :=
  TerminalDualConsumers.Own2162.oracle_gt _ DualNonempty2162.simplex.1
    DualNonempty2162.simplex.2 DualNonempty2162.real_cell
example : DualNonempty2162.Y 2=0 ∧ DualNonempty2162.Y 5=0 := by decide +kernel

-- A genuinely nontrivial convex combination of two actual paid fields.
def twoFields : Fin 7 → ℚ := ![1/2,1/2,0,0,0,0,0]
theorem twoFields_energy (y : Fin 9 → ℝ) :
    ConvexMinorantCore.weightedEnergy (ConvexMinorantCore.mixWeight twoFields) y≤
      ResumeNetwork.V2 (chartAnchors y) :=
  ConvexMinorantCore.weightedEnergy_le_oracle twoFields (ConvexMinorantCore.mixWeight twoFields)
    (by decide +kernel) (by decide +kernel) (fun _ => le_rfl) y
#print axioms twoFields_energy
example : ¬((∑ f : Fin 7,(![1,1,0,0,0,0,0] : Fin 7 → ℚ) f)=1) := by decide +kernel
example : ConvexMinorantCore.endpointLo 1 2 (-3)=(-6 : ℚ) := by decide +kernel
example : ¬((-3 : ℚ)*1≤(-3 : ℚ)*2) := by decide +kernel
example : DBMMinorantDual.rowA 4 3 3=(-1 : ℚ) := by decide +kernel
example : DBMMinorantDual.rowA 3 4 3=(1 : ℚ) := by decide +kernel
example : DBMMinorantDual.db 2166 4 3=(-1/4 : ℚ) := by decide +kernel
example : (0 : ℚ)<TerminalDualConsumers.Own2166.lam 0 := TerminalDualConsumers.Own2166.lam_pos
example : ¬(FlashCosineLeaf284Bridge.T^2 <
    DBMMinorantDual.lower Terminal562Oracle.W DSHTerminalBatchL0G1Zplus2166.slopeQ
      DSHTerminalBatchL0G1Zplus2166.interQ 2166
      TerminalDualConsumers.Own2166.rowFrom TerminalDualConsumers.Own2166.rowTo (fun _ => 0) 0) :=
  TerminalDualConsumers.Own2166.zero_dual_fails
example : ∀ k : Fin 36,Terminal2162Minorants.NK k=1 := by decide +kernel
example : Terminal2162Minorants.PL 0 < (0 : ℚ) := by decide +kernel
example : Terminal2162Minorants.PA 0≠DSHTerminalBatchL0G1Zplus2166.PA 0 ∨
    Terminal2162Minorants.PB 0≠DSHTerminalBatchL0G1Zplus2166.PB 0 := by decide +kernel
example : EnergyTerminalBatchB02.paidIDs.card=7 := EnergyTerminalBatchB02.paid_count
example : (2162 : Fin 5011)∈EnergyTerminalBatchB02.paidIDs := by decide +kernel
example : (3 : Fin 5011)∉EnergyTerminalBatchB02.paidIDs := by decide +kernel
example : Fintype.card ResumeNetwork.Edge=51 := by decide
example : (ResumeNetwork.face 5 2).val=10 := by decide
example : SourceExactRoot.sourceRadius=SourceExactRoot.sourceRoot 6 := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment
end
