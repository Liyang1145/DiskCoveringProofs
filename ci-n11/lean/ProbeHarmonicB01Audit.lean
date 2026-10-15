import N11Formalization

/-! Actual root-imported generic/concrete harmonic witnesses and OWN3436.
ALL100 actual DBM rows, a nonempty closed simplex, ALL51 feasible application.
RemainingTerminalRadius and unrestricted lower bound are still explicit. -/
set_option autoImplicit false
open N11Formalization SourceChartIsometry
open Finset
set_option maxRecDepth 10000
#print CertifiedHarmonicField.Packet
#print CertifiedHarmonicField.Valid
#check @CertifiedHarmonicField.hs
#check @CertifiedHarmonicField.hbal
#check @CertifiedHarmonicField.hH
#check @CertifiedHarmonicField.weight_eq_neg_gram
#check @CertifiedHarmonicField.source_energy_le_oracle
#check @CertifiedHarmonicField.chart_energy_le_oracle
#check @CertifiedFieldMixtures.weightedEnergy_le_oracle
#check @CertifiedFieldMixtures.radius_of_dual
#print HarmonicFieldsB01.sourceID
#check @HarmonicFieldsB01.all_valid
#check @HarmonicFieldsB01.sourceID_injective
#check @HarmonicFieldsB01.oracle
#check @HarmonicFieldsB01.mixture_oracle
#check @Terminal3436Packet.beta_sum
#check @Terminal3436Packet.all_valid
#check @Terminal3436Packet.endpoint_binding
#check @Terminal3436Packet.reduced
#check @Terminal3436Packet.numeric_check
#check @Terminal3436Packet.pair_minorant
#check @Terminal3436Consumer.rounded_le
#check @Terminal3436Consumer.W_mix
#check @Terminal3436Consumer.angles_in_cell
#check @Terminal3436Consumer.oracle_gt
#check @Terminal3436Consumer.common_chart_radius
#check @EnergyTerminalBatchB06.paid_count
#check @EnergyTerminalBatchB06.new_not_old
#check @EnergyTerminalBatchB06.paid_not_sharp
#check @EnergyTerminalBatchB06.paid_radius
#check @EnergyTerminalBatchB06.chart_radius_of_remaining
#print EnergyTerminalBatchB06.RemainingTerminalRadius
#print ResumeNetwork.Feasible
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms CertifiedHarmonicField.source_energy_le_oracle
#print axioms CertifiedFieldMixtures.radius_of_dual
#print axioms HarmonicFieldsB01.all_valid
#print axioms HarmonicFieldsB01.oracle
#print axioms HarmonicFieldsB01.mixture_oracle
#print axioms Terminal3436Packet.all_valid
#print axioms Terminal3436Packet.endpoint_binding
#print axioms Terminal3436Packet.reduced
#print axioms Terminal3436Packet.numeric_check
#print axioms Terminal3436Packet.pair_minorant
#print axioms Terminal3436Consumer.rounded_le
#print axioms Terminal3436Consumer.common_chart_radius
#print axioms EnergyTerminalBatchB06.paid_radius
#print axioms EnergyTerminalBatchB06.chart_radius_of_remaining

namespace HarmonicB01Actual
theorem mass_one (f : Fin 8) :
    ∑ e, CertifiedHarmonicField.αR (HarmonicFieldsB01.packet f) e = 1 :=
  CertifiedHarmonicField.hs _ (HarmonicFieldsB01.all_valid f)
theorem free_balance (f : Fin 8) :
    ∀ v j, ∑ e,
      (CertifiedHarmonicField.αR (HarmonicFieldsB01.packet f) e *
        ResumeDirichlet.incidence e v) *
        ResumeHarmonic.coeff (CertifiedHarmonicField.HR (HarmonicFieldsB01.packet f)) e j = 0 :=
  CertifiedHarmonicField.hbal _ (HarmonicFieldsB01.all_valid f)
theorem harmonic_rows (f : Fin 8) :
    ∀ v, ∑ j, CertifiedHarmonicField.HR (HarmonicFieldsB01.packet f) v j = 1 :=
  CertifiedHarmonicField.hH _ (HarmonicFieldsB01.all_valid f)
theorem actual_oracle (f : Fin 8) (y : Fin 9 → ℝ) :
    CertifiedHarmonicField.fieldEnergy (HarmonicFieldsB01.packet f) (FlashCosine.theta y) ≤
      ResumeNetwork.V2 (chartAnchors y) := HarmonicFieldsB01.oracle f y

def Y (q : Fin 9) : ℚ :=
  DBMMinorantDual.db Terminal3436Packet.nodeID 0 q.succ -
    DBMMinorantDual.db Terminal3436Packet.nodeID 0 q.castSucc
def y (q : Fin 9) : ℝ := (Y q : ℝ)
theorem rational_rows : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y q) ≤
        DBMMinorantDual.db Terminal3436Packet.nodeID i j := by decide +kernel
theorem real_cell :
    FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 Terminal3436Packet.nodeID)
      (FlashLeafSplit.tlift y) := by
  intro i j
  have h := (Rat.cast_le (K := ℝ)).mpr (rational_rows i j)
  simpa only [DBMMinorantDual.db, DBMTreeKernel.matrix, Rat.cast_sub, Rat.cast_sum,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, Int.cast_ofNat,
    FlashLeafSplit.tlift, y] using h
theorem simplex : (∀ q, 0 ≤ y q) ∧ ∑ q : Fin 9, y q = 1 := by
  have h0 : ∀ q : Fin 9, (0 : ℚ) ≤ Y q := by decide +kernel
  have h1 : (∑ q : Fin 9, Y q) = 1 := by decide +kernel
  constructor
  · intro q
    change (0 : ℝ) ≤ (Y q : ℝ)
    exact_mod_cast h0 q
  · change (∑ q : Fin 9, (Y q : ℝ)) = 1
    have h := congrArg (fun t : ℚ => (t : ℝ)) h1
    simpa only [Rat.cast_sum, Rat.cast_one] using h
theorem oracle_strict : (FlashCosineLeaf284Bridge.T : ℝ)^2 <
    ResumeNetwork.V2 (chartAnchors y) :=
  Terminal3436Consumer.oracle_gt y simplex.1 simplex.2 real_cell
theorem zero_feasible :
    ResumeNetwork.Feasible (chartAnchors y) (fun _ => 0) (fun _ => 0) 1 :=
  ResumeNetwork.feasible_unit (fun j => by
    simpa only [chartAnchors] using (circleMap_norm (cellAngles y j)).le)
theorem actual_radius_application : SourceExactRoot.sourceRadius < 1 :=
  Terminal3436Consumer.common_chart_radius y simplex.1 simplex.2 real_cell
    (fun _ => 0) (fun _ => 0) 1 zero_feasible
theorem actual_dispatch_application : SourceExactRoot.sourceRadius < 1 :=
  EnergyTerminalBatchB06.paid_radius 3436 (by decide +kernel)
    y simplex.1 simplex.2 real_cell (fun _ => 0) (fun _ => 0) 1 zero_feasible
end HarmonicB01Actual
#print axioms HarmonicB01Actual.mass_one
#print axioms HarmonicB01Actual.free_balance
#print axioms HarmonicB01Actual.harmonic_rows
#print axioms HarmonicB01Actual.actual_oracle
#print axioms HarmonicB01Actual.real_cell
#print axioms HarmonicB01Actual.oracle_strict
#print axioms HarmonicB01Actual.actual_radius_application
#print axioms HarmonicB01Actual.actual_dispatch_application

example (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 3436)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  Terminal3436Consumer.common_chart_radius y hy0 hy1 hc C Z r hf
example : EnergyTerminalBatchB06.paidIDs.card = 33 := EnergyTerminalBatchB06.paid_count
example : (3436 : Fin 5011) ∉ EnergyTerminalBatchB05.paidIDs := EnergyTerminalBatchB06.new_not_old
example : Disjoint EnergyTerminalBatchB06.paidIDs Patch120SharpDispatch.sharpIDs :=
  EnergyTerminalBatchB06.paid_not_sharp
example : Fintype.card ResumeNetwork.Edge = 51 := by decide
example : (ResumeNetwork.face 5 2).val = 10 := by decide
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment
example : Covers (fun _ : Fin 11 => (0 : Point)) 1 := by
  intro x hx
  change ‖x‖ ≤ (1 : ℝ) at hx
  exact ⟨0, by simpa only [dist_zero_right] using hx⟩
