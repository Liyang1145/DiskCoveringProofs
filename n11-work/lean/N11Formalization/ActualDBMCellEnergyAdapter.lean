import N11Formalization.CertifiedFieldMixtures
import N11Formalization.CosineLinePacket
import N11Formalization.DBMAngleProvider

/-! Exact energy certificates on arbitrary rational DBM cells, including
newly refined cells. All packet checks are rational; actual field validity
and finite-tree validity are paid inputs, never stored energy or solver values.
The finite-tree consumer covers the entire original closed source cell.
No concrete unpaid terminal is certified by this generic adapter alone. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualDBMCellEnergyAdapter
open Finset FlashCosine ConvexMinorantCore
open FlashCosineLeaf284Bridge (iOf jOf)

abbrev RatDBM := Fin 10 → Fin 10 → ℚ

def realMatrix (d : RatDBM) : FlashLeafSplit.M := fun a b => (d a b : ℝ)

def matrixQ {N : ℕ} (tree : Fin N → DBMTreeKernel.Node N)
    (scale : ℤ) (l : Fin N) : RatDBM :=
  fun a b => ((tree l).db a b : ℚ) / (scale : ℚ)

structure Packet (nf nd : ℕ) where
  beta : Fin nf → ℚ
  weight : Fin 36 → ℚ
  line : Fin 36 → CosineLinePacket.Packet
  rowFrom : Fin nd → Fin 10
  rowTo : Fin nd → Fin 10
  lam : Fin nd → ℚ
  rmin : ℚ

def PA {nf nd : ℕ} (p : Packet nf nd) (k : Fin 36) : ℚ := (p.line k).a
def PB {nf nd : ℕ} (p : Packet nf nd) (k : Fin 36) : ℚ := (p.line k).b
def slopeQ {nf nd : ℕ} (p : Packet nf nd) (k : Fin 36) : ℚ := (p.line k).s
def interQ {nf nd : ℕ} (p : Packet nf nd) (k : Fin 36) : ℚ := (p.line k).c
def slo (d : RatDBM) (k : Fin 36) : ℚ :=
  max (-d (jOf k).castSucc (iOf k).castSucc) 0
def shi (d : RatDBM) (k : Fin 36) : ℚ := d (iOf k).castSucc (jOf k).castSucc

def dualLower {nf nd : ℕ} (d : RatDBM) (p : Packet nf nd) : ℚ :=
  f0Lo p.weight (slopeQ p) (interQ p) -
    (∑ a, p.lam a * d (p.rowFrom a) (p.rowTo a)) + p.rmin

/-- Only finite rational comparisons and genuine cosine-line certificate
checks occur in Valid. It has no energy, oracle, radius, or coverage field. -/
structure Valid {nf nd : ℕ}
    (fields : Fin nf → CertifiedHarmonicField.Packet) (d : RatDBM)
    (p : Packet nf nd) : Prop where
  beta_nonneg : ∀ f, 0 ≤ p.beta f
  beta_sum : (∑ f, p.beta f) = 1
  weight_nonneg : ∀ k, 0 ≤ p.weight k
  weight_mix : ∀ k,
    p.weight k ≤ CertifiedFieldMixtures.mixWeight fields p.beta k
  lines : ∀ k, CosineLinePacket.Valid (p.line k)
  endpoints : ∀ k,
    PA p k ≤ ((iOf k).val - (jOf k).val : ℚ) * LQ + Dq * slo d k ∧
    ((iOf k).val - (jOf k).val : ℚ) * Lq + DQ * shi d k ≤ PB p k
  lam_nonneg : ∀ a, 0 ≤ p.lam a
  reduced : ∀ q : Fin 9,
    p.rmin ≤ endpointLo Dq DQ (g p.weight (slopeQ p) q) +
      DBMMinorantDual.rho p.rowFrom p.rowTo p.lam q
  numeric : FlashCosineLeaf284Bridge.T ^ 2 < dualLower d p

theorem rows_of_matrix (d : RatDBM) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (realMatrix d) (FlashLeafSplit.tlift y))
    (i j : Fin 10) :
    (∑ q : Fin 9, (DBMMinorantDual.rowA i j q : ℝ) * y q) ≤ (d i j : ℝ) := by
  rw [DBMMinorantDual.row_sum]
  exact hc i j

theorem angles_of_endpoints (d : RatDBM) (A B : Fin 36 → ℚ)
    (he : ∀ k,
      A k ≤ ((iOf k).val - (jOf k).val : ℚ) * LQ + Dq * slo d k ∧
      ((iOf k).val - (jOf k).val : ℚ) * Lq + DQ * shi d k ≤ B k)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hc : FlashLeafSplit.Cell (realMatrix d) (FlashLeafSplit.tlift y)) :
    ∀ k : Fin 36, zval y (iOf k) (jOf k) ∈ Set.Icc (A k : ℝ) (B k : ℝ) := by
  intro k
  have hu := hc (iOf k).castSucc (jOf k).castSucc
  have hl := hc (jOf k).castSucc (iOf k).castSucc
  simp only [realMatrix, ← FlashCosineLeaf284Bridge.tval_eq_tlift] at hu hl
  have hsig0 : 0 ≤ tval y (jOf k).castSucc - tval y (iOf k).castSucc := by
    rw [tval_sub y (Nat.le_of_lt (Terminal562SimplexEnergy.pair_order k))]
    exact Finset.sum_nonneg (fun q _ => by
      split_ifs <;> first | exact hy0 q | exact le_rfl)
  have hsl : (slo d k : ℝ) ≤
      tval y (jOf k).castSucc - tval y (iOf k).castSucc := by
    simp only [slo, Rat.cast_max, Rat.cast_neg, Rat.cast_zero, max_le_iff]
    exact ⟨by linarith, hsig0⟩
  have hsh : tval y (jOf k).castSucc - tval y (iOf k).castSucc ≤ (shi d k : ℝ) := hu
  have h := cell_bound (Terminal562SimplexEnergy.pair_order k)
    (show (0 : ℚ) ≤ slo d k from le_max_right _ _)
    L_mem.1 L_mem.2 D_mem.1 D_mem.2 hsl hsh
  rw [← zval_eq] at h
  have hlo : (A k : ℝ) ≤
      (((iOf k).val - (jOf k).val : ℚ) * LQ + Dq * slo d k : ℚ) := by
    exact_mod_cast (he k).1
  have hhi : (((iOf k).val - (jOf k).val : ℚ) * Lq + DQ * shi d k : ℚ) ≤
      (B k : ℝ) := by exact_mod_cast (he k).2
  exact ⟨hlo.trans h.1, h.2.trans hhi⟩

theorem affine_lower_of_matrix {nf nd : ℕ}
    (fields : Fin nf → CertifiedHarmonicField.Packet) (d : RatDBM)
    (p : Packet nf nd) (hp : Valid fields d p)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (realMatrix d) (FlashLeafSplit.tlift y)) :
    (dualLower d p : ℝ) ≤ affine p.weight (slopeQ p) (interQ p) y := by
  have h := lp_step9
    (fun a => DBMMinorantDual.rowA (p.rowFrom a) (p.rowTo a))
    (fun a => d (p.rowFrom a) (p.rowTo a)) p.lam
    (fun q => Dc * (g p.weight (slopeQ p) q : ℝ)) (p.rmin : ℝ) y
    (fun a => by exact_mod_cast hp.lam_nonneg a)
    (fun a => rows_of_matrix d y hc (p.rowFrom a) (p.rowTo a)) hy0 hy1
    (DBMMinorantDual.reduced_cost p.weight (slopeQ p)
      p.rowFrom p.rowTo p.lam p.rmin hp.reduced)
  simp_rw [mul_assoc] at h
  rw [← Finset.mul_sum] at h
  have hf := affine_f0_lower p.weight (slopeQ p) (interQ p) y
  have he : (dualLower d p : ℝ) =
      (f0Lo p.weight (slopeQ p) (interQ p) : ℝ) -
        (∑ a, (p.lam a : ℝ) * (d (p.rowFrom a) (p.rowTo a) : ℝ)) +
          (p.rmin : ℝ) := by
    simp only [dualLower, Rat.cast_add, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul]
  rw [he]
  linarith

theorem matrix_cell_oracle_gt {nf nd : ℕ}
    (fields : Fin nf → CertifiedHarmonicField.Packet)
    (hfields : ∀ f, CertifiedHarmonicField.Valid (fields f))
    (d : RatDBM) (p : Packet nf nd) (hp : Valid fields d p)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (realMatrix d) (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ) ^ 2 <
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
  have hnum : (FlashCosineLeaf284Bridge.T : ℝ) ^ 2 < (dualLower d p : ℝ) := by
    exact_mod_cast hp.numeric
  have ha := hnum.trans_le (affine_lower_of_matrix fields d p hp y hy0 hy1 hc)
  have ho := CertifiedFieldMixtures.affine_le_oracle fields hfields p.beta
    p.weight (slopeQ p) (interQ p) (PA p) (PB p)
    hp.beta_nonneg hp.beta_sum hp.weight_nonneg hp.weight_mix
    (fun k => CosineLinePacket.minorant (p.line k) (hp.lines k))
    y (angles_of_endpoints d (PA p) (PB p) hp.endpoints y hy0 hc)
  exact ha.trans_le ho

theorem matrix_cell_radius {nf nd : ℕ}
    (fields : Fin nf → CertifiedHarmonicField.Packet)
    (hfields : ∀ f, CertifiedHarmonicField.Valid (fields f))
    (d : RatDBM) (p : Packet nf nd) (hp : Valid fields d p)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (realMatrix d) (FlashLeafSplit.tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hlo := matrix_cell_oracle_gt fields hfields d p hp y hy0 hy1 hc
  have hhi := ResumeNetwork.oracle_le_feasible hf
  have ht : (0 : ℝ) ≤ FlashCosineLeaf284Bridge.T := by
    norm_num [FlashCosineLeaf284Bridge.T]
  have hT : (FlashCosineLeaf284Bridge.T : ℝ) < r := by nlinarith [hf.1]
  exact Terminal562Oracle.sourceRadius_lt_T.trans hT

theorem real_matrixQ {N : ℕ} (tree : Fin N → DBMTreeKernel.Node N)
    (scale : ℤ) (l : Fin N) :
    realMatrix (matrixQ tree scale l) = DBMTreeKernel.matrix tree scale l := by
  funext a b
  simp only [realMatrix, matrixQ, DBMTreeKernel.matrix, Rat.cast_div, Rat.cast_intCast]

/-- Finite valid splits choose a real closed leaf for every parent point.
There is no externally assumed ChildCover or terminal energy field. -/
theorem finite_refinement_radius {N nf nd : ℕ}
    (fields : Fin nf → CertifiedHarmonicField.Packet)
    (hfields : ∀ f, CertifiedHarmonicField.Valid (fields f))
    (tree : Fin N → DBMTreeKernel.Node N) (scale : ℤ) (hs : 0 < scale)
    (htree : ∀ l, DBMTreeKernel.Valid tree l)
    (root : Fin N) (packets : Fin N → Packet nf nd)
    (hpaid : ∀ l, (tree l).terminal = true →
      Valid fields (matrixQ tree scale l) (packets l))
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix tree scale root)
      (FlashLeafSplit.tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  obtain ⟨l, hl, hcell⟩ := DBMTreeKernel.terminal_cover tree scale hs htree
    (FlashLeafSplit.tlift y) root hc
  have hcQ : FlashLeafSplit.Cell (realMatrix (matrixQ tree scale l))
      (FlashLeafSplit.tlift y) := by
    rwa [real_matrixQ]
  exact matrix_cell_radius fields hfields (matrixQ tree scale l) (packets l)
    (hpaid l hl) y hy0 hy1 hcQ C Z r hf

theorem source_root_matrix_binding {N : ℕ}
    (tree : Fin N → DBMTreeKernel.Node N) (scale : ℤ) (hs : 0 < scale)
    (root : Fin N) (sourceNode : Fin 5011)
    (hroot : ∀ a b : Fin 10,
      4096 * (tree root).db a b = scale * (DBMSourceTree.data sourceNode).db a b) :
    DBMTreeKernel.matrix tree scale root =
      DBMTreeKernel.matrix DBMSourceTree.data 4096 sourceNode := by
  have hscale : (scale : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  funext a b
  have hb : (4096 : ℝ) * ((tree root).db a b : ℝ) =
      (scale : ℝ) * ((DBMSourceTree.data sourceNode).db a b : ℝ) := by
    exact_mod_cast hroot a b
  unfold DBMTreeKernel.matrix
  apply (div_eq_div_iff hscale (by norm_num : (4096 : ℝ) ≠ 0)).mpr
  nlinarith only [hb]

/-- The integer binding retains the full original source-node closed cell;
every child leaf must pass genuine rational/field/minorant certificate checks. -/
theorem source_cell_radius_of_refinement {N nf nd : ℕ}
    (fields : Fin nf → CertifiedHarmonicField.Packet)
    (hfields : ∀ f, CertifiedHarmonicField.Valid (fields f))
    (tree : Fin N → DBMTreeKernel.Node N) (scale : ℤ) (hs : 0 < scale)
    (htree : ∀ l, DBMTreeKernel.Valid tree l)
    (root : Fin N) (sourceNode : Fin 5011)
    (hroot : ∀ a b : Fin 10,
      4096 * (tree root).db a b = scale * (DBMSourceTree.data sourceNode).db a b)
    (packets : Fin N → Packet nf nd)
    (hpaid : ∀ l, (tree l).terminal = true →
      Valid fields (matrixQ tree scale l) (packets l))
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell
      (DBMTreeKernel.matrix DBMSourceTree.data 4096 sourceNode)
      (FlashLeafSplit.tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hcRoot : FlashLeafSplit.Cell (DBMTreeKernel.matrix tree scale root)
      (FlashLeafSplit.tlift y) := by
    rwa [source_root_matrix_binding tree scale hs root sourceNode hroot]
  exact finite_refinement_radius fields hfields tree scale hs htree root packets
    hpaid y hy0 hy1 hcRoot C Z r hf

end N11Formalization.ActualDBMCellEnergyAdapter
#check @N11Formalization.ActualDBMCellEnergyAdapter.matrix_cell_oracle_gt
#check @N11Formalization.ActualDBMCellEnergyAdapter.matrix_cell_radius
#check @N11Formalization.ActualDBMCellEnergyAdapter.finite_refinement_radius
#check @N11Formalization.ActualDBMCellEnergyAdapter.source_cell_radius_of_refinement
#print axioms N11Formalization.ActualDBMCellEnergyAdapter.matrix_cell_radius
#print axioms N11Formalization.ActualDBMCellEnergyAdapter.finite_refinement_radius
#print axioms N11Formalization.ActualDBMCellEnergyAdapter.source_cell_radius_of_refinement
