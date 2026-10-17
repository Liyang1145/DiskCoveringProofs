import N11Formalization

/-! Root-imported audit for the eleven tangent/chord consumers.
The finite witnesses below are actual DBM potentials, not sampled angles or
host-solver output.  RemainingTerminalRadius and the arbitrary-Covers
reduction remain explicit in the imported root. -/
set_option autoImplicit false
set_option maxRecDepth 10000
open N11Formalization SourceChartIsometry
open _root_.N11Formalization.Lambda0TangentChordC01Packet

#check @Lambda0TangentChordC01Packet.all_valid
#check @Lambda0TangentChordC01Packet.endpoint_binding
#check @Lambda0TangentChordC01Packet.reduced
#check @Lambda0TangentChordC01Packet.numeric_check
#check @Lambda0TangentChordC01Packet.pair_minorant
#check @Lambda0TangentChordC01Consumer.oracle_gt
#check @Lambda0TangentChordC01Consumer.common_chart_radius
#check @Lambda0TangentChordC01Consumer.new_radius
#check @EnergyTerminalBatchB04.paid_count
#check @EnergyTerminalBatchB04.paid_radius
#check @EnergyTerminalBatchB04.chart_radius_of_remaining
#print axioms Lambda0TangentChordC01Consumer.common_chart_radius
#print axioms Lambda0TangentChordC01Consumer.new_radius
#print axioms EnergyTerminalBatchB04.paid_radius

example : Lambda0TangentChordC01Consumer.newIDs.card = 11 :=
  Lambda0TangentChordC01Consumer.new_count
example : EnergyTerminalBatchB04.paidIDs.card = 25 :=
  EnergyTerminalBatchB04.paid_count
example : (2675 : Fin 5011) ∈ EnergyTerminalBatchB04.paidIDs := by decide +kernel
example : (4485 : Fin 5011) ∈ EnergyTerminalBatchB04.paidIDs := by decide +kernel
example : (3 : Fin 5011) ∉ EnergyTerminalBatchB04.paidIDs := by decide +kernel
example : Function.Injective Lambda0TangentChordC01Packet.nodeID :=
  Lambda0TangentChordC01Consumer.node_injective
example : (SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6) := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment

section ActualCells
abbrev TCcase := Lambda0TangentChordC01Packet.Case
def Y (ci : TCcase) (q : Fin 9) : ℚ :=
  DBMMinorantDual.db (nodeID ci) 0 q.succ -
    DBMMinorantDual.db (nodeID ci) 0 q.castSucc
def y (ci : TCcase) (q : Fin 9) : ℝ := (Y ci q : ℝ)

private theorem rows0 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 0 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 0 q) ≤
        DBMMinorantDual.db (nodeID 0) i j := by decide +kernel
private theorem rows1 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 1 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 1 q) ≤
        DBMMinorantDual.db (nodeID 1) i j := by decide +kernel
private theorem rows2 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 2 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 2 q) ≤
        DBMMinorantDual.db (nodeID 2) i j := by decide +kernel
private theorem rows3 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 3 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 3 q) ≤
        DBMMinorantDual.db (nodeID 3) i j := by decide +kernel
private theorem rows4 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 4 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 4 q) ≤
        DBMMinorantDual.db (nodeID 4) i j := by decide +kernel
private theorem rows5 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 5 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 5 q) ≤
        DBMMinorantDual.db (nodeID 5) i j := by decide +kernel
private theorem rows6 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 6 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 6 q) ≤
        DBMMinorantDual.db (nodeID 6) i j := by decide +kernel
private theorem rows7 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 7 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 7 q) ≤
        DBMMinorantDual.db (nodeID 7) i j := by decide +kernel
private theorem rows8 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 8 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 8 q) ≤
        DBMMinorantDual.db (nodeID 8) i j := by decide +kernel
private theorem rows9 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 9 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 9 q) ≤
        DBMMinorantDual.db (nodeID 9) i j := by decide +kernel
private theorem rows10 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 10 q) -
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 10 q) ≤
        DBMMinorantDual.db (nodeID 10) i j := by decide +kernel

theorem rational_rows (ci : TCcase) (i j : Fin 10) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y ci q) -
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

theorem real_cell (ci : TCcase) :
    FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID ci))
      (FlashLeafSplit.tlift (y ci)) := by
  intro i j
  have h := (Rat.cast_le (K := ℝ)).mpr (rational_rows ci i j)
  simpa only [DBMMinorantDual.db,DBMTreeKernel.matrix,Rat.cast_sub,Rat.cast_sum,
    Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat,Int.cast_ofNat,
    FlashLeafSplit.tlift,y] using h

theorem simplex (ci : TCcase) : (∀ q,0 ≤ y ci q) ∧ ∑ q : Fin 9,y ci q=1 := by
  have h0 : ∀ ci : TCcase,∀ q : Fin 9,(0 : ℚ)≤Y ci q := by decide +kernel
  have h1 : ∀ ci : TCcase,(∑ q : Fin 9,Y ci q)=1 := by decide +kernel
  constructor
  · intro q
    change (0 : ℝ)≤(Y ci q : ℝ)
    exact_mod_cast h0 ci q
  · change (∑ q : Fin 9,(Y ci q : ℝ))=1
    have h := congrArg (fun t : ℚ => (t : ℝ)) (h1 ci)
    simpa only [Rat.cast_sum,Rat.cast_one] using h

theorem oracle_strict (ci : TCcase) : (FlashCosineLeaf284Bridge.T : ℝ)^2 <
    ResumeNetwork.V2 (chartAnchors (y ci)) :=
  Lambda0TangentChordC01Consumer.oracle_gt ci (y ci) (simplex ci).1
    (simplex ci).2 (real_cell ci)

theorem zero_feasible (ci : TCcase) :
    ResumeNetwork.Feasible (chartAnchors (y ci)) (fun _ => 0) (fun _ => 0) 1 :=
  ResumeNetwork.feasible_unit (fun j => by
    simpa only [chartAnchors] using (circleMap_norm (cellAngles (y ci) j)).le)

theorem actual_radius_application (ci : TCcase) :
    SourceExactRoot.sourceRadius < 1 :=
  Lambda0TangentChordC01Consumer.common_chart_radius ci (y ci)
    (simplex ci).1 (simplex ci).2 (real_cell ci)
    (fun _ => 0) (fun _ => 0) 1 (zero_feasible ci)
end ActualCells

example : ¬CosineLinePacket.Valid (⟨0,1,1,0,0,0,0,.left⟩ :
    CosineLinePacket.Packet) := by decide +kernel
example : ¬CosineLinePacket.Valid
    {Lambda0TangentChordC01Packet.packet 1 0 with shift:=97} := by decide +kernel
example : (∑ f : Fin 7,
    (Lambda0TangentChordC01Packet.beta 1 f + if f=0 then 1 else 0)) ≠ 1 := by
  decide +kernel
example : ∃ i j : Fin 7,i≠j ∧
    0 < beta 1 i ∧ 0 < beta 1 j := by decide +kernel
example : ∃ i : TCcase,¬(∀ q : Fin 9,
    rmin i ≤ ConvexMinorantCore.endpointLo FlashCosine.Dq FlashCosine.DQ
      (ConvexMinorantCore.g (W i) (slopeQ i) q) +
      DBMMinorantDual.rho (rowFrom i) (rowTo i) (fun _ => 0) q) := by
  decide +kernel
example : ∃ k : Fin 36,
    PA 1 k ≠ PA 2 k ∨ PB 1 k ≠ PB 2 k := by decide +kernel
example : ∃ i : TCcase,∃ q : Fin 9,Y i q=0 := by decide +kernel
example : EnergyTerminalBatchB04.paidIDs.card=25 :=
  EnergyTerminalBatchB04.paid_count
