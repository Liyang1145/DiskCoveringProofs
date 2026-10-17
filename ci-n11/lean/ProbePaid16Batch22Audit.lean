import N11Formalization

/-! Actual root imported22-cell/convex/fullDBM/continuum proof.
ALL2200 own rows/nonempty closed cells, real feasible assignment and controls.
Original unrestricted main and remaining terminal premise printed in full. -/
set_option autoImplicit false
open N11Formalization SourceChartIsometry
open _root_.N11Formalization.Paid16Batch22Packet (Case Row nodeID beta packet PA PB slopeQ interQ W rowFrom rowTo lam rmin)
#check @HarmonicFieldsPaid16.all_valid
#print HarmonicFieldsPaid16.sourceID
#print axioms HarmonicFieldsPaid16.all_valid
#print axioms HarmonicFieldsPaid16.oracle
#check @CosineLinePacket.incArc_sound
#check @CosineLinePacket.decArc_sound
#check @CosineLinePacket.minorant
#print CosineLinePacket.Valid
#check @RoundedPaid16.weight_le
#check @RoundedPaid16.mix_le
#print Paid16Batch22Packet.nodeID
#check @Paid16Batch22Packet.beta_nonneg
#check @Paid16Batch22Packet.beta_sum
#check @Paid16Batch22Packet.lam_nonneg
#check @Paid16Batch22Packet.terminal
#check @Paid16Batch22Packet.all_valid
#check @Paid16Batch22Packet.endpoint_binding
#check @Paid16Batch22Packet.reduced
#check @Paid16Batch22Packet.numeric_check
#check @Paid16Batch22Packet.pair_minorant
#check @Paid16Batch22Consumer.W_mix
#check @Paid16Batch22Consumer.angles_in_cell
#check @Paid16Batch22Consumer.oracle_gt
#check @Paid16Batch22Consumer.common_chart_radius
#check @Paid16Batch22Consumer.node_injective
#check @Paid16Batch22Consumer.new_count
#check @Paid16Batch22Consumer.new_radius
#check @EnergyTerminalBatchB09.paid_count
#check @EnergyTerminalBatchB09.new_disjoint_old
#check @EnergyTerminalBatchB09.paid_not_sharp
#check @EnergyTerminalBatchB09.paid_radius
#check @EnergyTerminalBatchB09.chart_radius_of_remaining
#print EnergyTerminalBatchB09.RemainingTerminalRadius
#print ResumeNetwork.Feasible
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms CosineLinePacket.minorant
#print axioms RoundedPaid16.mix_le
#print axioms Paid16Batch22Packet.all_valid
#print axioms Paid16Batch22Packet.endpoint_binding
#print axioms Paid16Batch22Packet.reduced
#print axioms Paid16Batch22Packet.numeric_check
#print axioms Paid16Batch22Packet.pair_minorant
#print axioms Paid16Batch22Consumer.common_chart_radius
#print axioms Paid16Batch22Consumer.new_radius
#print axioms EnergyTerminalBatchB09.paid_radius
#print axioms EnergyTerminalBatchB09.chart_radius_of_remaining

example (i : Case) (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID i))
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  Paid16Batch22Consumer.common_chart_radius i y hy0 hy1 hc C Z r hf
example (n : Fin 5011) (hn : n∈EnergyTerminalBatchB09.paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  EnergyTerminalBatchB09.paid_radius n hn y hy0 hy1 hc C Z r hf

section
set_option maxRecDepth 10000
namespace Paid16Nonempty
-- Exact potentials read from each ACTUAL node, not numerical angle samples.
def Y (ci : Case) (q : Fin 9) : ℚ :=
  DBMMinorantDual.db (nodeID ci) 0 q.succ-DBMMinorantDual.db (nodeID ci) 0 q.castSucc
def y (ci : Case) (q : Fin 9) : ℝ := (Y ci q : ℝ)
private theorem rows0 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 0 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 0 q) ≤
        DBMMinorantDual.db (nodeID 0) i j := by decide +kernel
private theorem rows1 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 1 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 1 q) ≤
        DBMMinorantDual.db (nodeID 1) i j := by decide +kernel
private theorem rows2 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 2 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 2 q) ≤
        DBMMinorantDual.db (nodeID 2) i j := by decide +kernel
private theorem rows3 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 3 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 3 q) ≤
        DBMMinorantDual.db (nodeID 3) i j := by decide +kernel
private theorem rows4 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 4 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 4 q) ≤
        DBMMinorantDual.db (nodeID 4) i j := by decide +kernel
private theorem rows5 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 5 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 5 q) ≤
        DBMMinorantDual.db (nodeID 5) i j := by decide +kernel
private theorem rows6 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 6 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 6 q) ≤
        DBMMinorantDual.db (nodeID 6) i j := by decide +kernel
private theorem rows7 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 7 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 7 q) ≤
        DBMMinorantDual.db (nodeID 7) i j := by decide +kernel
private theorem rows8 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 8 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 8 q) ≤
        DBMMinorantDual.db (nodeID 8) i j := by decide +kernel
private theorem rows9 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 9 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 9 q) ≤
        DBMMinorantDual.db (nodeID 9) i j := by decide +kernel
private theorem rows10 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 10 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 10 q) ≤
        DBMMinorantDual.db (nodeID 10) i j := by decide +kernel
private theorem rows11 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 11 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 11 q) ≤
        DBMMinorantDual.db (nodeID 11) i j := by decide +kernel
private theorem rows12 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 12 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 12 q) ≤
        DBMMinorantDual.db (nodeID 12) i j := by decide +kernel
private theorem rows13 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 13 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 13 q) ≤
        DBMMinorantDual.db (nodeID 13) i j := by decide +kernel
private theorem rows14 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 14 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 14 q) ≤
        DBMMinorantDual.db (nodeID 14) i j := by decide +kernel
private theorem rows15 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 15 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 15 q) ≤
        DBMMinorantDual.db (nodeID 15) i j := by decide +kernel
private theorem rows16 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 16 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 16 q) ≤
        DBMMinorantDual.db (nodeID 16) i j := by decide +kernel
private theorem rows17 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 17 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 17 q) ≤
        DBMMinorantDual.db (nodeID 17) i j := by decide +kernel
private theorem rows18 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 18 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 18 q) ≤
        DBMMinorantDual.db (nodeID 18) i j := by decide +kernel
private theorem rows19 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 19 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 19 q) ≤
        DBMMinorantDual.db (nodeID 19) i j := by decide +kernel
private theorem rows20 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 20 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 20 q) ≤
        DBMMinorantDual.db (nodeID 20) i j := by decide +kernel
private theorem rows21 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 21 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 21 q) ≤
        DBMMinorantDual.db (nodeID 21) i j := by decide +kernel
private theorem rational_rows (ci : Case) (i j : Fin 10) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y ci q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y ci q) ≤
        DBMMinorantDual.db (nodeID ci) i j := by
  fin_cases ci
  · exact rows0 i j
  · exact rows1 i j
  · exact rows2 i j
  · exact rows3 i j
  · exact rows4 i j
  · exact rows5 i j
  · exact rows6 i j
  · exact rows7 i j
  · exact rows8 i j
  · exact rows9 i j
  · exact rows10 i j
  · exact rows11 i j
  · exact rows12 i j
  · exact rows13 i j
  · exact rows14 i j
  · exact rows15 i j
  · exact rows16 i j
  · exact rows17 i j
  · exact rows18 i j
  · exact rows19 i j
  · exact rows20 i j
  · exact rows21 i j
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
  Paid16Batch22Consumer.oracle_gt ci (y ci) (simplex ci).1 (simplex ci).2 (real_cell ci)
theorem zero_feasible (ci : Case) :
    ResumeNetwork.Feasible (chartAnchors (y ci)) (fun _ => 0) (fun _ => 0) 1 :=
  ResumeNetwork.feasible_unit (fun j => by
    simpa only [chartAnchors] using (circleMap_norm (cellAngles (y ci) j)).le)
theorem actual_radius_application (ci : Case) : SourceExactRoot.sourceRadius < 1 :=
  Paid16Batch22Consumer.common_chart_radius ci (y ci) (simplex ci).1 (simplex ci).2
    (real_cell ci) (fun _ => 0) (fun _ => 0) 1 (zero_feasible ci)
end Paid16Nonempty
#print axioms Paid16Nonempty.real_cell
#print axioms Paid16Nonempty.oracle_strict
#print axioms Paid16Nonempty.actual_radius_application

def badLine : CosineLinePacket.Packet := ⟨0,1,1,0,0,0,0,.left⟩
example : ¬CosineLinePacket.Valid badLine := by decide +kernel
example : ¬CosineLinePacket.Valid {packet 1 0 with shift:=97} := by decide +kernel
example : (∑ f : Fin 16,(beta 1 f+(if f=0 then 1 else 0)))≠1 := by decide +kernel
example : ∃ i : Fin 16,∃ j : Fin 16,i≠j ∧ 0 < beta 1 i ∧ 0 < beta 1 j := by decide +kernel
example : ∃ i : Case,¬(∀ q : Fin 9,rmin i ≤
    ConvexMinorantCore.endpointLo FlashCosine.Dq FlashCosine.DQ (ConvexMinorantCore.g (W i) (slopeQ i) q)+
      DBMMinorantDual.rho (rowFrom i) (rowTo i) (fun _ => 0) q) := by decide +kernel
example : ∃ k : Fin 36,PA 1 k≠PA 2 k ∨ PB 1 k≠PB 2 k := by decide +kernel
example : ∃ i : Case,∃ q : Fin 9,Paid16Nonempty.Y i q=0 := by decide +kernel
example : Paid16Batch22Consumer.newIDs.card=22 := Paid16Batch22Consumer.new_count
example : EnergyTerminalBatchB09.paidIDs.card=58 := EnergyTerminalBatchB09.paid_count
example : (3842 : Fin 5011)∈EnergyTerminalBatchB09.paidIDs := by decide +kernel
example : (3 : Fin 5011)∉EnergyTerminalBatchB09.paidIDs := by decide +kernel
example : Disjoint EnergyTerminalBatchB08.paidIDs Paid16Batch22Consumer.newIDs :=
  EnergyTerminalBatchB09.new_disjoint_old
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
