import N11Formalization

/-! Root actual ALL120-domain/rotation/radius consumer and controls.
No norm/gain/rotation premise is passed to the real branch application. -/
set_option autoImplicit false
open N11Formalization SourceChartIsometry Patch120DomainPacket
#check @SourceChartIsometry.rotate_dist
#check @SourceChartIsometry.rotation_chart
#check @SourceChartIsometry.displacement_eq_h
#check @Patch120IntervalCore.xInput_mem
#check @Patch120DomainPacket.all_members
#check @Patch120DomainPacket.patchID_injective
#check @Patch120DomainPacket.X_contains
#check @Patch120DomainPacket.all_norms
#check @Patch120DomainPacket.actual_norm
#check @Patch120DomainPacket.actual_gain
#check @Patch120DomainPacket.actual_radius
#check @Patch120SharpDispatch.sharp_count
#check @Patch120SharpDispatch.sharp_radius
#check @Patch120SharpDispatch.chart_radius_of_other_terminals
#print Patch120SharpDispatch.OtherTerminalRadius
#print SourceChartIsometry.gauge
#print SourceChartIsometry.chartAnchors
#print SourceChartIsometry.displacement
#print ResumeNetwork.Feasible
#check @SourceExactRoot.main_of_lower_bound
#check @SourceExactRoot.source_attainment
#print axioms SourceChartIsometry.rotate_dist
#print axioms SourceChartIsometry.rotation_chart
#print axioms Patch120DomainPacket.all_members
#print axioms Patch120DomainPacket.X_contains
#print axioms Patch120DomainPacket.all_norms
#print axioms Patch120DomainPacket.actual_norm
#print axioms Patch120DomainPacket.actual_gain
#print axioms Patch120DomainPacket.actual_radius
#print axioms Patch120SharpDispatch.sharp_radius
#print axioms Patch120SharpDispatch.chart_radius_of_other_terminals

example (p : Fin 120) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (patchID p))
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius≤r :=
  Patch120DomainPacket.actual_radius p y hc C Z r hf

example (n : Fin 5011) (hn : n∈Patch120SharpDispatch.sharpIDs) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius≤r :=
  Patch120SharpDispatch.sharp_radius n hn y hc C Z r hf

-- One actual cell nonempty: source row0 upper potential, independent of root.
-- Local finite table evaluation only; default heartbeats/kernel unchanged.
section
set_option maxRecDepth 10000
namespace Patch120Nonempty
def YN : Fin 9 → ℚ := ![25,0,19,304,136,50,50,137,303]/1024
def y : Fin 9 → ℝ := fun i => (YN i : ℝ)
private theorem rational_rows (i j : Fin 10) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),YN q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),YN q)≤
        (DBMSourceTree.node4935.db i j : ℚ)/4096 := by
  fin_cases i <;> fin_cases j <;> decide +kernel
theorem real_cell :
    FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 4935)
      (FlashLeafSplit.tlift y) := by
  have he : DBMSourceTree.data (4935 : Fin 5011)=DBMSourceTree.node4935 := rfl
  intro i j
  rw [show DBMTreeKernel.matrix DBMSourceTree.data 4096 4935 i j=
    (DBMSourceTree.node4935.db i j : ℝ)/4096 from by rw [DBMTreeKernel.matrix,he]; norm_num]
  change (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),(YN q : ℝ))-
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),(YN q : ℝ))≤
      (DBMSourceTree.node4935.db i j : ℝ)/4096
  exact_mod_cast rational_rows i j
theorem simplex : (∀ i,0≤y i) ∧ ∑ i : Fin 9,y i=1 := by
  have h0 : ∀ i : Fin 9,(0 : ℚ)≤YN i := by decide +kernel
  have h1 : (∑ i : Fin 9,YN i)=1 := by decide +kernel
  constructor
  · intro i
    change (0 : ℝ)≤(YN i : ℝ)
    exact_mod_cast h0 i
  · change (∑ i : Fin 9,(YN i : ℝ))=1
    have h := congrArg (fun q : ℚ => (q : ℝ)) h1
    simpa only [Rat.cast_sum,Rat.cast_one] using h
end Patch120Nonempty
#check @Patch120Nonempty.real_cell
#print axioms Patch120Nonempty.real_cell

example : patchID (94 : Fin 120)=4935 := rfl
example : patchID (97 : Fin 120)=4957 := rfl
example : patchID (0 : Fin 120)=4436 := rfl
example : patchID (119 : Fin 120)=5010 := rfl
example : (∑ j : Fin 9,displacement Patch120Nonempty.y j^2)/100000≤
    ResumeNetwork.V2 (chartAnchors Patch120Nonempty.y)-SourceExactRoot.sourceRadius^2 := by
  exact actual_gain 94 Patch120Nonempty.y Patch120Nonempty.real_cell

-- Wrong DBM orientation cannot masquerade as a cluster hull certificate.
example : ¬(∀ i : Fin 9,i≠6 →
    UL (group (94 : Fin 120)) i≤-DBMSourceTree.node4935.db 6 (Patch120K5.f9 i) ∧
    DBMSourceTree.node4935.db (Patch120K5.f9 i) 6≤UH (group (94 : Fin 120)) i) := by
  decide +kernel
example : (562 : Fin 5011)∉Patch120SharpDispatch.sharpIDs := by decide +kernel
example : (Patch120SharpDispatch.sharpIDs).card=120 := Patch120SharpDispatch.sharp_count
example (y : Fin 9 → ℝ) : displacement y 6=0 := displacement_pin y
example : ResumeLocalIncidence.siteMap 8=(6 : Fin 9) := by decide
example : ResumeLocalIncidence.siteMap 8≠(8 : Fin 9) := by decide
example : (ResumeNetwork.face 5 2).val=10 := by decide
example : Fintype.card ResumeNetwork.Edge=51 := by decide
example : SourceExactRoot.sourceRadius=SourceExactRoot.sourceRoot 6 := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment
end
