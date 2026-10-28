import N11Formalization

/-! Real root-imported applications/nonempty owncells/negative controls.
No claim that closed-chart witness production or remaining terminals are paid. -/
set_option autoImplicit false
open N11Formalization SourceChartIsometry
#check @Field10MinorantCore.affine_identity
#check @Field10MinorantCore.g_sum_single_lower
#check @Field10MinorantCore.affine_le_oracle
#check @Field10MinorantCore.radius_of_minorants
#check @DSHTerminalBatchL0G1Zplus1112.pair_minorant
#check @DSHTerminalBatchL0G1Zplus2166.pair_minorant
#check @Terminal1112Angles.endpoint_binding
#check @Terminal1112Angles.angles_in_cell
#check @Terminal2166Angles.endpoint_binding
#check @Terminal2166Angles.angles_in_cell
#check @Terminal1112Oracle.cl_nonpos
#check @Terminal1112Oracle.f0_lower
#check @Terminal1112Oracle.g_nonneg
#check @Terminal2166Oracle.cl_nonpos
#check @Terminal2166Oracle.f0_lower
#check @Terminal2166Oracle.g_nonneg
#check @Terminal2166Oracle.g3_lower
#check @Terminal2166Oracle.y3_lower
#check @Terminal2166Oracle.g_sum_lower
#check @Terminal1112Oracle.oracle_gt
#check @Terminal1112Oracle.common_chart_radius
#check @Terminal2166Oracle.oracle_gt
#check @Terminal2166Oracle.common_chart_radius
#check @EnergyTerminalBatchB01.paid_count
#check @EnergyTerminalBatchB01.paid_terminal
#check @EnergyTerminalBatchB01.paid_not_sharp
#check @EnergyTerminalBatchB01.paid_radius
#check @EnergyTerminalBatchB01.chart_radius_of_remaining
#print EnergyTerminalBatchB01.RemainingTerminalRadius
#print Field10MinorantCore.affine
#print SourceChartIsometry.chartAnchors
#print ResumeNetwork.Feasible
#check @Terminal562Oracle.W_field10
#check @Leaf4348Fields7.source_energy_le_oracle
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms Field10MinorantCore.affine_identity
#print axioms Field10MinorantCore.radius_of_minorants
#print axioms DSHTerminalBatchL0G1Zplus1112.pair_minorant
#print axioms DSHTerminalBatchL0G1Zplus2166.pair_minorant
#print axioms Terminal1112Angles.angles_in_cell
#print axioms Terminal2166Angles.angles_in_cell
#print axioms Terminal2166Oracle.y3_lower
#print axioms Terminal1112Oracle.common_chart_radius
#print axioms Terminal2166Oracle.common_chart_radius
#print axioms EnergyTerminalBatchB01.paid_radius
#print axioms EnergyTerminalBatchB01.chart_radius_of_remaining

example (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 1112)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  Terminal1112Oracle.common_chart_radius y hy0 hc C Z r hf

example (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2166)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  Terminal2166Oracle.common_chart_radius y hy0 hc C Z r hf

example (n : Fin 5011) (hn : n∈EnergyTerminalBatchB01.paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  EnergyTerminalBatchB01.paid_radius n hn y hy0 hy1 hc C Z r hf

section
set_option maxRecDepth 10000
namespace B01Nonempty
-- Source row0 potentials, in lowest common denominator; not sampled angles.
def Y1112 : Fin 9 → ℚ := ![1,0,0,6,2,2,0,0,5]/16
def Y2166 : Fin 9 → ℚ := ![4,0,0,8,3,5,0,0,12]/32
def y1112 : Fin 9 → ℝ := fun i => (Y1112 i : ℝ)
def y2166 : Fin 9 → ℝ := fun i => (Y2166 i : ℝ)

private theorem rows1112 (i j : Fin 10) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y1112 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y1112 q)≤
        (DBMSourceTree.node1112.db i j : ℚ)/4096 := by
  fin_cases i <;> fin_cases j <;> decide +kernel
private theorem rows2166 (i j : Fin 10) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y2166 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y2166 q)≤
        (DBMSourceTree.node2166.db i j : ℚ)/4096 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem cell1112 : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 1112)
    (FlashLeafSplit.tlift y1112) := by
  have he : DBMSourceTree.data (1112 : Fin 5011)=DBMSourceTree.node1112 := rfl
  intro i j
  rw [show DBMTreeKernel.matrix DBMSourceTree.data 4096 1112 i j=
    (DBMSourceTree.node1112.db i j : ℝ)/4096 from by rw [DBMTreeKernel.matrix,he]; norm_num]
  change (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),(Y1112 q : ℝ))-
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),(Y1112 q : ℝ))≤
      (DBMSourceTree.node1112.db i j : ℝ)/4096
  exact_mod_cast rows1112 i j

theorem cell2166 : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2166)
    (FlashLeafSplit.tlift y2166) := by
  have he : DBMSourceTree.data (2166 : Fin 5011)=DBMSourceTree.node2166 := rfl
  intro i j
  rw [show DBMTreeKernel.matrix DBMSourceTree.data 4096 2166 i j=
    (DBMSourceTree.node2166.db i j : ℝ)/4096 from by rw [DBMTreeKernel.matrix,he]; norm_num]
  change (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),(Y2166 q : ℝ))-
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),(Y2166 q : ℝ))≤
      (DBMSourceTree.node2166.db i j : ℝ)/4096
  exact_mod_cast rows2166 i j

theorem simplex1112 : (∀ i,0≤y1112 i) ∧ ∑ i : Fin 9,y1112 i=1 := by
  have h0 : ∀ i : Fin 9,(0 : ℚ)≤Y1112 i := by decide +kernel
  have h1 : (∑ i : Fin 9,Y1112 i)=1 := by decide +kernel
  constructor
  · intro i; change (0 : ℝ)≤(Y1112 i : ℝ); exact_mod_cast h0 i
  · change (∑ i : Fin 9,(Y1112 i : ℝ))=1
    have h := congrArg (fun q : ℚ => (q : ℝ)) h1
    simpa only [Rat.cast_sum,Rat.cast_one] using h
theorem simplex2166 : (∀ i,0≤y2166 i) ∧ ∑ i : Fin 9,y2166 i=1 := by
  have h0 : ∀ i : Fin 9,(0 : ℚ)≤Y2166 i := by decide +kernel
  have h1 : (∑ i : Fin 9,Y2166 i)=1 := by decide +kernel
  constructor
  · intro i; change (0 : ℝ)≤(Y2166 i : ℝ); exact_mod_cast h0 i
  · change (∑ i : Fin 9,(Y2166 i : ℝ))=1
    have h := congrArg (fun q : ℚ => (q : ℝ)) h1
    simpa only [Rat.cast_sum,Rat.cast_one] using h
end B01Nonempty
#print axioms B01Nonempty.cell1112
#print axioms B01Nonempty.cell2166

example : (FlashCosineLeaf284Bridge.T : ℝ)^2 <
    ResumeNetwork.V2 (chartAnchors B01Nonempty.y1112) :=
  Terminal1112Oracle.oracle_gt _ B01Nonempty.simplex1112.1 B01Nonempty.cell1112
example : (FlashCosineLeaf284Bridge.T : ℝ)^2 <
    ResumeNetwork.V2 (chartAnchors B01Nonempty.y2166) :=
  Terminal2166Oracle.oracle_gt _ B01Nonempty.simplex2166.1 B01Nonempty.cell2166

-- Closed-simplex witnesses really include zero coordinates.
example : B01Nonempty.Y1112 1=0 ∧ B01Nonempty.Y2166 1=0 := by decide +kernel
example : B01Nonempty.y2166 3=(1/4 : ℝ) := by
  have h : B01Nonempty.Y2166 3=(1/4 : ℚ) := by decide +kernel
  change (B01Nonempty.Y2166 3 : ℝ)=(1/4 : ℝ)
  rw [h]
  norm_num
example : Field10MinorantCore.f0 DSHTerminalBatchL0G1Zplus2166.slopeQ
    DSHTerminalBatchL0G1Zplus2166.interQ < (FlashCosineLeaf284Bridge.T : ℚ)^2 := by
  decide +kernel
example (y : Fin 9 → ℝ) (hzero : y 3=0) :
    ¬ FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2166)
      (FlashLeafSplit.tlift y) := by
  intro hc
  have h := Terminal2166Oracle.y3_lower y hc
  rw [hzero] at h
  norm_num at h
example : (DBMSourceTree.data (1112 : Fin 5011)).db≠
    (DBMSourceTree.data (984 : Fin 5011)).db := by
  intro h
  have he := congrArg (fun f => f 0 1) h
  norm_num [DBMSourceTree.data,DBMSourceTree.node1112,DBMSourceTree.node984] at he
example : (DBMSourceTree.data (2166 : Fin 5011)).db≠
    (DBMSourceTree.data (1112 : Fin 5011)).db := by
  intro h
  have he := congrArg (fun f => f 0 1) h
  norm_num [DBMSourceTree.data,DBMSourceTree.node2166,DBMSourceTree.node1112] at he
example : DSHTerminalBatchL0G1Zplus1112.PA 0≠DSHTerminalBatchL0G1Zplus984.PA 0 ∨
    DSHTerminalBatchL0G1Zplus1112.PB 0≠DSHTerminalBatchL0G1Zplus984.PB 0 := by decide +kernel
example : DSHTerminalBatchL0G1Zplus2166.PA 0≠DSHTerminalBatchL0G1Zplus1112.PA 0 ∨
    DSHTerminalBatchL0G1Zplus2166.PB 0≠DSHTerminalBatchL0G1Zplus1112.PB 0 := by decide +kernel
example : EnergyTerminalBatchB01.paidIDs.card=6 := EnergyTerminalBatchB01.paid_count
example : (1112 : Fin 5011)∈EnergyTerminalBatchB01.paidIDs := by decide +kernel
example : (2166 : Fin 5011)∈EnergyTerminalBatchB01.paidIDs := by decide +kernel
example : (3 : Fin 5011)∉EnergyTerminalBatchB01.paidIDs := by decide +kernel
example : Disjoint EnergyTerminalBatchB01.paidIDs Patch120SharpDispatch.sharpIDs :=
  EnergyTerminalBatchB01.paid_not_sharp
example (k : Fin 36) :
    (Terminal562Oracle.W k : ℝ)≤2*Leaf4348Fields7.weight 0 k :=
  Terminal562Oracle.W_field10 k
example : ¬ ((FlashCosineLeaf284Bridge.T : ℚ)^2 <
    ∑ k : Fin 36,(0 : ℚ)*(1-(0 : ℚ))) := by decide +kernel
example : Fintype.card ResumeNetwork.Edge=51 := by decide
example : (ResumeNetwork.face 5 2).val=10 := by decide
example : SourceExactRoot.sourceRadius=SourceExactRoot.sourceRoot 6 := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment
end
