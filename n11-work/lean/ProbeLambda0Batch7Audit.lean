import N11Formalization

/-! Actual root imported seven-cell/convex/fullDBM/continuum proof.
ALL700 own rows/nonempty closed cells, real feasible assignment and controls.
Original unrestricted main and remaining terminal premise printed in full. -/
set_option autoImplicit false
open N11Formalization SourceChartIsometry
open _root_.N11Formalization.Lambda0Batch7Packet (Case Row nodeID beta packet PA PB slopeQ interQ W rowFrom rowTo lam rmin)
#check @CosineLinePacket.incArc_sound
#check @CosineLinePacket.decArc_sound
#check @CosineLinePacket.minorant
#print CosineLinePacket.Valid
#check @RoundedFieldWeights.weight_le
#check @RoundedFieldWeights.mix_le
#print Lambda0Batch7Packet.nodeID
#check @Lambda0Batch7Packet.beta_nonneg
#check @Lambda0Batch7Packet.beta_sum
#check @Lambda0Batch7Packet.lam_nonneg
#check @Lambda0Batch7Packet.terminal
#check @Lambda0Batch7Packet.all_valid
#check @Lambda0Batch7Packet.endpoint_binding
#check @Lambda0Batch7Packet.reduced
#check @Lambda0Batch7Packet.numeric_check
#check @Lambda0Batch7Packet.pair_minorant
#check @Lambda0Batch7Consumer.W_mix
#check @Lambda0Batch7Consumer.angles_in_cell
#check @Lambda0Batch7Consumer.oracle_gt
#check @Lambda0Batch7Consumer.common_chart_radius
#check @Lambda0Batch7Consumer.node_injective
#check @Lambda0Batch7Consumer.new_count
#check @Lambda0Batch7Consumer.new_radius
#check @EnergyTerminalBatchB03.paid_count
#check @EnergyTerminalBatchB03.new_disjoint_old
#check @EnergyTerminalBatchB03.paid_not_sharp
#check @EnergyTerminalBatchB03.paid_radius
#check @EnergyTerminalBatchB03.chart_radius_of_remaining
#print EnergyTerminalBatchB03.RemainingTerminalRadius
#print ResumeNetwork.Feasible
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms CosineLinePacket.minorant
#print axioms RoundedFieldWeights.mix_le
#print axioms Lambda0Batch7Packet.all_valid
#print axioms Lambda0Batch7Packet.endpoint_binding
#print axioms Lambda0Batch7Packet.reduced
#print axioms Lambda0Batch7Packet.numeric_check
#print axioms Lambda0Batch7Packet.pair_minorant
#print axioms Lambda0Batch7Consumer.common_chart_radius
#print axioms Lambda0Batch7Consumer.new_radius
#print axioms EnergyTerminalBatchB03.paid_radius
#print axioms EnergyTerminalBatchB03.chart_radius_of_remaining

example (i : Case) (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID i))
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  Lambda0Batch7Consumer.common_chart_radius i y hy0 hy1 hc C Z r hf
example (n : Fin 5011) (hn : n∈EnergyTerminalBatchB03.paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  EnergyTerminalBatchB03.paid_radius n hn y hy0 hy1 hc C Z r hf

section
set_option maxRecDepth 10000
namespace Batch7Nonempty
-- Exact potentials read from each ACTUAL node, not numerical angle samples.
def Y (ci : Case) (q : Fin 9) : ℚ :=
  DBMMinorantDual.db (nodeID ci) 0 q.succ-DBMMinorantDual.db (nodeID ci) 0 q.castSucc
def y (ci : Case) (q : Fin 9) : ℝ := (Y ci q : ℝ)
private theorem rows0 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 0 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 0 q)≤
        DBMMinorantDual.db (nodeID 0) i j := by decide +kernel
private theorem rows1 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 1 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 1 q)≤
        DBMMinorantDual.db (nodeID 1) i j := by decide +kernel
private theorem rows2 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 2 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 2 q)≤
        DBMMinorantDual.db (nodeID 2) i j := by decide +kernel
private theorem rows3 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 3 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 3 q)≤
        DBMMinorantDual.db (nodeID 3) i j := by decide +kernel
private theorem rows4 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 4 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 4 q)≤
        DBMMinorantDual.db (nodeID 4) i j := by decide +kernel
private theorem rows5 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 5 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 5 q)≤
        DBMMinorantDual.db (nodeID 5) i j := by decide +kernel
private theorem rows6 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 6 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 6 q)≤
        DBMMinorantDual.db (nodeID 6) i j := by decide +kernel
private theorem rational_rows (ci : Case) (i j : Fin 10) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y ci q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y ci q)≤
        DBMMinorantDual.db (nodeID ci) i j := by
  fin_cases ci
  · exact rows0 i j
  · exact rows1 i j
  · exact rows2 i j
  · exact rows3 i j
  · exact rows4 i j
  · exact rows5 i j
  · exact rows6 i j
theorem real_cell (ci : Case) :
    FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID ci))
      (FlashLeafSplit.tlift (y ci)) := by
  intro i j
  have h := (Rat.cast_le (K := ℝ)).mpr (rational_rows ci i j)
  simpa only [DBMMinorantDual.db,DBMTreeKernel.matrix,Rat.cast_sub,Rat.cast_sum,
    Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat,Int.cast_ofNat,
    FlashLeafSplit.tlift,y] using h
theorem simplex (ci : Case) : (∀ q,0 ≤ y ci q) ∧ ∑ q : Fin 9,y ci q=1 := by
  have h0 : ∀ ci : Case,∀ q : Fin 9,(0 : ℚ)≤Y ci q := by decide +kernel
  have h1 : ∀ ci : Case,(∑ q : Fin 9,Y ci q)=1 := by decide +kernel
  constructor
  · intro q; change (0 : ℝ)≤(Y ci q : ℝ); exact_mod_cast h0 ci q
  · change (∑ q : Fin 9,(Y ci q : ℝ))=1
    have h := congrArg (fun t : ℚ => (t : ℝ)) (h1 ci)
    simpa only [Rat.cast_sum,Rat.cast_one] using h
theorem oracle_strict (ci : Case) : (FlashCosineLeaf284Bridge.T : ℝ)^2 <
    ResumeNetwork.V2 (chartAnchors (y ci)) :=
  Lambda0Batch7Consumer.oracle_gt ci (y ci) (simplex ci).1 (simplex ci).2 (real_cell ci)
theorem zero_feasible (ci : Case) :
    ResumeNetwork.Feasible (chartAnchors (y ci)) (fun _ => 0) (fun _ => 0) 1 :=
  ResumeNetwork.feasible_unit (fun j => by
    simpa only [chartAnchors] using (circleMap_norm (cellAngles (y ci) j)).le)
theorem actual_radius_application (ci : Case) : SourceExactRoot.sourceRadius < 1 :=
  Lambda0Batch7Consumer.common_chart_radius ci (y ci) (simplex ci).1 (simplex ci).2
    (real_cell ci) (fun _ => 0) (fun _ => 0) 1 (zero_feasible ci)
end Batch7Nonempty
#print axioms Batch7Nonempty.real_cell
#print axioms Batch7Nonempty.oracle_strict
#print axioms Batch7Nonempty.actual_radius_application

def badLine : CosineLinePacket.Packet := ⟨0,1,1,0,0,0,0,.left⟩
example : ¬CosineLinePacket.Valid badLine := by decide +kernel
example : ¬CosineLinePacket.Valid {packet 1 0 with shift:=97} := by decide +kernel
example : (∑ f : Fin 7,(beta 1 f+(if f=0 then 1 else 0)))≠1 := by decide +kernel
example : ∃ i : Case,∃ j : Fin 7,i≠j ∧ 0 < beta 1 i ∧ 0 < beta 1 j := by decide +kernel
example : ∃ i : Case,¬(∀ q : Fin 9,rmin i ≤
    ConvexMinorantCore.endpointLo FlashCosine.Dq FlashCosine.DQ (ConvexMinorantCore.g (W i) (slopeQ i) q)+
      DBMMinorantDual.rho (rowFrom i) (rowTo i) (fun _ => 0) q) := by decide +kernel
example : ∃ k : Fin 36,PA 1 k≠PA 2 k ∨ PB 1 k≠PB 2 k := by decide +kernel
example : ∃ i : Case,∃ q : Fin 9,Batch7Nonempty.Y i q=0 := by decide +kernel
example : Lambda0Batch7Consumer.newIDs.card=7 := Lambda0Batch7Consumer.new_count
example : EnergyTerminalBatchB03.paidIDs.card=14 := EnergyTerminalBatchB03.paid_count
example : (3842 : Fin 5011)∈EnergyTerminalBatchB03.paidIDs := by decide +kernel
example : (3 : Fin 5011)∉EnergyTerminalBatchB03.paidIDs := by decide +kernel
example : Disjoint EnergyTerminalBatchB02.paidIDs Lambda0Batch7Consumer.newIDs :=
  EnergyTerminalBatchB03.new_disjoint_old
example : Fintype.card ResumeNetwork.Edge=51 := by decide
example : (ResumeNetwork.face 5 2).val=10 := by decide
example : SourceExactRoot.sourceRadius=SourceExactRoot.sourceRoot 6 := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment
example : Covers (fun _ : Fin 11 => (0 : Point)) 1 := by
  intro x hx
  change ‖x‖≤(1 : ℝ) at hx
  exact ⟨0,by simpa only [dist_zero_right] using hx⟩
end
