import N11Formalization.ActualDBMCellEnergyAdapter
import N11Formalization.Paid16GeneralG12

set_option autoImplicit false
noncomputable section
namespace N11Formalization.RecoveryDBMCellEnergyAudit
open Finset FlashCosine ConvexMinorantCore ActualDBMCellEnergyAdapter
open FlashCosineLeaf284Bridge (iOf jOf)

def ofPaid16 (p : Paid16CellCertificate.Packet) : Packet 16 7 :=
  ⟨p.beta, Paid16CellCertificate.W p, p.line, p.rowFrom, p.rowTo, p.lam, p.rmin⟩

theorem valid_of_paid16 (p : Paid16CellCertificate.Packet)
    (hp : Paid16CellCertificate.Valid p) :
    Valid HarmonicFieldsPaid16.packet (matrixQ DBMSourceTree.data 4096 p.nodeID)
      (ofPaid16 p) := by
  refine ⟨hp.beta_nonneg, hp.beta_sum, Paid16CellCertificate.W_nonneg p hp,
    Paid16CellCertificate.W_mix p hp, hp.lines, ?_, hp.lam_nonneg, ?_, ?_⟩
  · simpa only [PA, PB, ofPaid16, matrixQ, slo, shi,
      Paid16CellCertificate.PA, Paid16CellCertificate.PB,
      DBMAngleProvider.slo, DBMAngleProvider.shi, DBMMinorantDual.db,
      Int.cast_ofNat] using hp.endpoints
  · exact hp.reduced
  · have hs : slopeQ (ofPaid16 p) = Paid16CellCertificate.slopeQ p := rfl
    have hi : interQ (ofPaid16 p) = Paid16CellCertificate.interQ p := rfl
    rw [dualLower, hs, hi]
    simpa only [ofPaid16, matrixQ,
      DBMMinorantDual.lower, DBMMinorantDual.lamB, DBMMinorantDual.db,
      Int.cast_ofNat] using hp.numeric

/-- Reusing a true certificate on a tighter child matrix preserves all
exact checks; it does not invent a new energy premise. -/
theorem valid_on_tighter_matrix {nf nd : ℕ}
    (fields : Fin nf → CertifiedHarmonicField.Packet) (d d' : RatDBM)
    (p : Packet nf nd) (hp : Valid fields d p) (hle : ∀ a b, d' a b ≤ d a b) :
    Valid fields d' p := by
  refine ⟨hp.beta_nonneg, hp.beta_sum, hp.weight_nonneg, hp.weight_mix,
    hp.lines, ?_, hp.lam_nonneg, hp.reduced, ?_⟩
  · intro k
    have hDq : (0 : ℚ) ≤ Dq := by exact_mod_cast Dq_pos.le
    have hDQ : (0 : ℚ) ≤ DQ := by
      have h : (0 : ℝ) ≤ (DQ : ℝ) := Dq_pos.le.trans (D_mem.1.trans D_mem.2)
      exact_mod_cast h
    have hlo : slo d k ≤ slo d' k :=
      max_le_max (neg_le_neg (hle (jOf k).castSucc (iOf k).castSucc)) le_rfl
    have hhi : shi d' k ≤ shi d k := hle _ _
    exact ⟨(hp.endpoints k).1.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlo hDq)),
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hhi hDQ)).trans
        (hp.endpoints k).2⟩
  · have hcost : (∑ a, p.lam a * d' (p.rowFrom a) (p.rowTo a)) ≤
        (∑ a, p.lam a * d (p.rowFrom a) (p.rowTo a)) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hle _ _) (hp.lam_nonneg a))
    have hnum := hp.numeric
    unfold dualLower at hnum ⊢
    linarith

def basePacket : Packet 16 7 := ofPaid16 Paid16GeneralG12.packet1
def parentDBM : Fin 10 → Fin 10 → ℤ := (DBMSourceTree.data (1066 : Fin 5011)).db
def leftDBM (a b : Fin 10) : ℤ :=
  min (parentDBM a b) (parentDBM a 0 + 2048 + parentDBM 4 b)
def rightDBM (a b : Fin 10) : ℤ :=
  min (parentDBM a b) (parentDBM a 4 - 2048 + parentDBM 0 b)
def rootNode : DBMTreeKernel.Node 3 := ⟨parentDBM, false, 0, 4, 2048, 1, 2⟩
def leftNode : DBMTreeKernel.Node 3 := ⟨leftDBM, true, 0, 0, 0, 1, 2⟩
def rightNode : DBMTreeKernel.Node 3 := ⟨rightDBM, true, 0, 0, 0, 1, 2⟩
def tree : Fin 3 → DBMTreeKernel.Node 3 := ![rootNode, leftNode, rightNode]

theorem tree_valid (l : Fin 3) : DBMTreeKernel.Valid tree l := by
  fin_cases l
  · refine Or.inr ⟨by decide, by decide, ?_⟩
    intro a b
    exact ⟨le_rfl, le_rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem root_binding (a b : Fin 10) :
    4096 * (tree 0).db a b = 4096 * (DBMSourceTree.data (1066 : Fin 5011)).db a b := rfl

theorem child_tighter (l : Fin 3) (hl : (tree l).terminal = true) :
    ∀ a b, matrixQ tree 4096 l a b ≤ matrixQ DBMSourceTree.data 4096 1066 a b := by
  fin_cases l
  · change false = true at hl
    contradiction
  · intro a b
    change (leftDBM a b : ℚ) / 4096 ≤ (parentDBM a b : ℚ) / 4096
    apply div_le_div_of_nonneg_right ?_ (by norm_num : (0 : ℚ) ≤ 4096)
    exact_mod_cast (min_le_left (parentDBM a b) (parentDBM a 0 + 2048 + parentDBM 4 b))
  · intro a b
    change (rightDBM a b : ℚ) / 4096 ≤ (parentDBM a b : ℚ) / 4096
    apply div_le_div_of_nonneg_right ?_ (by norm_num : (0 : ℚ) ≤ 4096)
    exact_mod_cast (min_le_left (parentDBM a b) (parentDBM a 4 - 2048 + parentDBM 0 b))

theorem base_valid :
    Valid HarmonicFieldsPaid16.packet (matrixQ DBMSourceTree.data 4096 1066) basePacket :=
  valid_of_paid16 Paid16GeneralG12.packet1 Paid16GeneralG12.valid1

theorem all_leaves_paid (l : Fin 3) (hl : (tree l).terminal = true) :
    Valid HarmonicFieldsPaid16.packet (matrixQ tree 4096 l) basePacket :=
  valid_on_tighter_matrix HarmonicFieldsPaid16.packet
    (matrixQ DBMSourceTree.data 4096 1066) (matrixQ tree 4096 l) basePacket
    base_valid (child_tighter l hl)

theorem actual_1066_matrix_consumer (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 1066)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  apply matrix_cell_radius HarmonicFieldsPaid16.packet HarmonicFieldsPaid16.all_valid
    (matrixQ DBMSourceTree.data 4096 1066) basePacket base_valid y hy0 hy1 ?_ C Z r hf
  rwa [real_matrixQ]

/-- True local two-child split; the entire original source1066 closed cell
is consumed via terminal_cover. No ChildCover assumption is provided. -/
theorem actual_1066_refinement_consumer (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 1066)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  source_cell_radius_of_refinement HarmonicFieldsPaid16.packet
    HarmonicFieldsPaid16.all_valid tree 4096 (by norm_num) tree_valid 0 1066
    root_binding (fun _ => basePacket) all_leaves_paid y hy0 hy1 hc C Z r hf

def zeroBeta : Packet 16 7 := {basePacket with beta := fun _ => 0}
theorem reject_zero_beta :
    ¬ Valid HarmonicFieldsPaid16.packet (matrixQ DBMSourceTree.data 4096 1066) zeroBeta := by
  intro hp
  have h := hp.beta_sum
  simp only [zeroBeta, Finset.sum_const_zero] at h
  norm_num at h

def zeroWeights : Packet 16 7 :=
  {basePacket with weight := fun _ => 0, lam := fun _ => 0, rmin := 0}
theorem reject_zero_energy :
    ¬ Valid HarmonicFieldsPaid16.packet (matrixQ DBMSourceTree.data 4096 1066) zeroWeights := by
  intro hp
  have h := hp.numeric
  simp only [dualLower, zeroWeights, f0Lo, cv, cl, mul_zero, zero_mul,
    Finset.sum_const_zero, endpointLo, le_refl, if_true, sub_zero, add_zero] at h
  exact (sq_nonneg (FlashCosineLeaf284Bridge.T : ℚ)).not_gt h

#print Valid
#check @matrix_cell_radius
#check @source_cell_radius_of_refinement
#check @actual_1066_matrix_consumer
#check @actual_1066_refinement_consumer
#print axioms actual_1066_matrix_consumer
#print axioms actual_1066_refinement_consumer
#print axioms reject_zero_beta
#print axioms reject_zero_energy
#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment

end N11Formalization.RecoveryDBMCellEnergyAudit
