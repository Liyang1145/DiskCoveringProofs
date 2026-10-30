import N11Formalization.Paid16CellCertificate

/-! DRAFT (energy line, 2026-10-15) — NOT COMPILED (no Mathlib toolchain on the producing
machine). Generalises `Paid16CellCertificate` from a source-tree node to an EXPLICIT integer
DBM matrix `D` at positive scale `S`, so that refinement leaves (sub-cells produced by the
`DBMTreeKernel.Valid` split rule) can carry their own packets. Proofs are line-by-line copies of
DBMMinorantDual.rows_of_cell / affine_lower_of_dual, DBMAngleProvider.angles_of_endpoints and
CertifiedFieldMixtures.radius_of_dual with `DBMSourceTree.data n` replaced by `D`; expect
simp-lemma-name repairs when first compiled. Nothing here is paid. -/
set_option autoImplicit false
namespace N11Formalization.Paid16MatrixCellCertificate
open Finset FlashCosine
open FlashCosineLeaf284Bridge (iOf jOf)
open ConvexMinorantCore DBMMinorantDual
noncomputable section

def mdb (D : Fin 10 → Fin 10 → ℤ) (S : ℕ) (i j : Fin 10) : ℚ := (D i j : ℚ) / (S : ℚ)
def mMatrix (D : Fin 10 → Fin 10 → ℤ) (S : ℕ) : Fin 10 → Fin 10 → ℝ :=
  fun a b => (D a b : ℝ) / (S : ℝ)
def mslo (D : Fin 10 → Fin 10 → ℤ) (S : ℕ) (k : Fin 36) : ℚ :=
  max (-mdb D S (jOf k).castSucc (iOf k).castSucc) 0
def mshi (D : Fin 10 → Fin 10 → ℤ) (S : ℕ) (k : Fin 36) : ℚ :=
  mdb D S (iOf k).castSucc (jOf k).castSucc
def mlamB {m : ℕ} (D : Fin 10 → Fin 10 → ℤ) (S : ℕ) (rowFrom rowTo : Fin m → Fin 10)
    (lam : Fin m → ℚ) : ℚ := ∑ a : Fin m, lam a * mdb D S (rowFrom a) (rowTo a)
def mlower {m : ℕ} (w s c : Fin 36 → ℚ) (D : Fin 10 → Fin 10 → ℤ) (S : ℕ)
    (rowFrom rowTo : Fin m → Fin 10) (lam : Fin m → ℚ) (rmin : ℚ) : ℚ :=
  f0Lo w s c - mlamB D S rowFrom rowTo lam + rmin

structure MPacket where
  D : Fin 10 → Fin 10 → ℤ
  S : ℕ
  beta : Fin 16 → ℚ
  line : Fin 36 → CosineLinePacket.Packet
  rowFrom : Fin 7 → Fin 10
  rowTo : Fin 7 → Fin 10
  lam : Fin 7 → ℚ
  rmin : ℚ

def PA (p : MPacket) (k : Fin 36) : ℚ := (p.line k).a
def PB (p : MPacket) (k : Fin 36) : ℚ := (p.line k).b
def slopeQ (p : MPacket) (k : Fin 36) : ℚ := (p.line k).s
def interQ (p : MPacket) (k : Fin 36) : ℚ := (p.line k).c
def W (p : MPacket) (k : Fin 36) : ℚ := RoundedPaid16.mix p.beta k

structure MValid (p : MPacket) : Prop where
  S_pos : 0 < p.S
  beta_nonneg : ∀ f : Fin 16, 0 ≤ p.beta f
  beta_sum : (∑ f : Fin 16, p.beta f) = 1
  lines : ∀ k : Fin 36, CosineLinePacket.Valid (p.line k)
  endpoints : ∀ k : Fin 36,
    PA p k ≤ ((iOf k).val - (jOf k).val : ℚ) * LQ + Dq * mslo p.D p.S k ∧
    ((iOf k).val - (jOf k).val : ℚ) * Lq + DQ * mshi p.D p.S k ≤ PB p k
  lam_nonneg : ∀ a : Fin 7, 0 ≤ p.lam a
  reduced : ∀ q : Fin 9, p.rmin ≤
    endpointLo Dq DQ (g (W p) (slopeQ p) q) + rho p.rowFrom p.rowTo p.lam q
  numeric : FlashCosineLeaf284Bridge.T ^ 2 <
    mlower (W p) (slopeQ p) (interQ p) p.D p.S p.rowFrom p.rowTo p.lam p.rmin

theorem m_rows_of_cell (D : Fin 10 → Fin 10 → ℤ) (S : ℕ) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (mMatrix D S) (FlashLeafSplit.tlift y)) (i j : Fin 10) :
    (∑ q : Fin 9, (rowA i j q : ℝ) * y q) ≤ (mdb D S i j : ℝ) := by
  rw [row_sum]
  have h := hc i j
  simpa only [mdb, mMatrix, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using h

theorem m_affine_lower_of_dual {m : ℕ} (w s c : Fin 36 → ℚ) (D : Fin 10 → Fin 10 → ℤ) (S : ℕ)
    (rowFrom rowTo : Fin m → Fin 10) (lam : Fin m → ℚ) (rmin : ℚ)
    (hlam : ∀ a, 0 ≤ lam a)
    (hr : ∀ q : Fin 9, rmin ≤ endpointLo Dq DQ (g w s q) + rho rowFrom rowTo lam q)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (mMatrix D S) (FlashLeafSplit.tlift y)) :
    (mlower w s c D S rowFrom rowTo lam rmin : ℝ) ≤ affine w s c y := by
  have h := lp_step9 (fun a => rowA (rowFrom a) (rowTo a))
    (fun a => mdb D S (rowFrom a) (rowTo a)) lam (fun q => Dc * (g w s q : ℝ)) (rmin : ℝ) y
    (fun a => by exact_mod_cast hlam a)
    (fun a => m_rows_of_cell D S y hc (rowFrom a) (rowTo a)) hy0 hy1
    (reduced_cost w s rowFrom rowTo lam rmin hr)
  simp_rw [mul_assoc] at h
  rw [← Finset.mul_sum] at h
  have hf := affine_f0_lower w s c y
  have he : (mlower w s c D S rowFrom rowTo lam rmin : ℝ) =
      (f0Lo w s c : ℝ) - (∑ a : Fin m, (lam a : ℝ) * (mdb D S (rowFrom a) (rowTo a) : ℝ)) +
        (rmin : ℝ) := by
    simp only [mlower, mlamB, Rat.cast_add, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul]
  rw [he]
  linarith

theorem m_angles_of_endpoints (D : Fin 10 → Fin 10 → ℤ) (S : ℕ) (hS : 0 < S)
    (A B : Fin 36 → ℚ)
    (he : ∀ k, A k ≤ ((iOf k).val - (jOf k).val : ℚ) * LQ + Dq * mslo D S k ∧
      ((iOf k).val - (jOf k).val : ℚ) * Lq + DQ * mshi D S k ≤ B k)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hc : FlashLeafSplit.Cell (mMatrix D S) (FlashLeafSplit.tlift y)) :
    ∀ k : Fin 36, zval y (iOf k) (jOf k) ∈ Set.Icc (A k : ℝ) (B k : ℝ) := by
  intro k
  have hu := hc (iOf k).castSucc (jOf k).castSucc
  have hl := hc (jOf k).castSucc (iOf k).castSucc
  simp only [← FlashCosineLeaf284Bridge.tval_eq_tlift] at hu hl
  have hsig0 : 0 ≤ tval y (jOf k).castSucc - tval y (iOf k).castSucc := by
    rw [tval_sub y (Nat.le_of_lt (Terminal562SimplexEnergy.pair_order k))]
    exact Finset.sum_nonneg (fun q _ => by split_ifs <;> first | exact hy0 q | exact le_rfl)
  have hsl : (mslo D S k : ℝ) ≤ tval y (jOf k).castSucc - tval y (iOf k).castSucc := by
    simp only [mslo, mdb, Rat.cast_max, Rat.cast_neg, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_natCast, Rat.cast_zero, max_le_iff]
    constructor
    · simp only [mMatrix] at hl
      linarith
    · exact hsig0
  have hsh : tval y (jOf k).castSucc - tval y (iOf k).castSucc ≤ (mshi D S k : ℝ) := by
    simpa only [mshi, mdb, mMatrix, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using hu
  have h := cell_bound (Terminal562SimplexEnergy.pair_order k)
    (show (0 : ℚ) ≤ mslo D S k from le_max_right _ _)
    L_mem.1 L_mem.2 D_mem.1 D_mem.2 hsl hsh
  rw [← zval_eq] at h
  have hlo : (A k : ℝ) ≤ (((iOf k).val - (jOf k).val : ℚ) * LQ + Dq * mslo D S k : ℚ) := by
    exact_mod_cast (he k).1
  have hhi : (((iOf k).val - (jOf k).val : ℚ) * Lq + DQ * mshi D S k : ℚ) ≤ (B k : ℝ) := by
    exact_mod_cast (he k).2
  exact ⟨hlo.trans h.1, h.2.trans hhi⟩

theorem oracle_gt (p : MPacket) (hp : MValid p)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (mMatrix p.D p.S) (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ) ^ 2 <
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
  have hnum : (FlashCosineLeaf284Bridge.T : ℝ) ^ 2 <
      (mlower (W p) (slopeQ p) (interQ p) p.D p.S p.rowFrom p.rowTo p.lam p.rmin : ℝ) := by
    exact_mod_cast hp.numeric
  have hlo := hnum.trans_le
    (m_affine_lower_of_dual (W p) (slopeQ p) (interQ p) p.D p.S
      p.rowFrom p.rowTo p.lam p.rmin hp.lam_nonneg hp.reduced y hy0 hy1 hc)
  exact hlo.trans_le
    (CertifiedFieldMixtures.affine_le_oracle HarmonicFieldsPaid16.packet
      HarmonicFieldsPaid16.all_valid p.beta (W p) (slopeQ p) (interQ p) (PA p) (PB p)
      hp.beta_nonneg hp.beta_sum (fun k => RoundedPaid16.mix_nonneg p.beta hp.beta_nonneg k)
      (fun k => RoundedPaid16.mix_le p.beta hp.beta_nonneg k)
      (fun k => CosineLinePacket.minorant (p.line k) (hp.lines k))
      y (m_angles_of_endpoints p.D p.S hp.S_pos (PA p) (PB p) hp.endpoints y hy0 hc))

/-- Same final step as `CertifiedFieldMixtures.radius_of_dual` (lines 103-…). -/
theorem radius (p : MPacket) (hp : MValid p)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (mMatrix p.D p.S) (FlashLeafSplit.tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have ho := oracle_gt p hp y hy0 hy1 hc
  have hhi := ResumeNetwork.oracle_le_feasible hf
  have ht : (0 : ℝ) ≤ FlashCosineLeaf284Bridge.T := by
    norm_num [FlashCosineLeaf284Bridge.T]
  have hT : (FlashCosineLeaf284Bridge.T : ℝ) < r := by nlinarith [hf.1]
  exact Terminal562Oracle.sourceRadius_lt_T.trans hT

/-- A refinement of source node `n`: a local DBM tree whose root has the node's matrix
scaled by `2^8` (scale 4096·2^8) and whose terminal leaves each carry an `MPacket`. -/
theorem node_radius_of_refinement {K : ℕ} (n : Fin 5011)
    (sub : Fin K → DBMTreeKernel.Node K) (root : Fin K) (hv : ∀ l, DBMTreeKernel.Valid sub l)
    (hroot : ∀ a b, (sub root).db a b = 256 * (DBMSourceTree.data n).db a b)
    (pk : Fin K → MPacket)
    (hpk : ∀ l, (sub l).terminal = true → MValid (pk l) ∧ (pk l).D = (sub l).db ∧ (pk l).S = 1048576)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hc0 : FlashLeafSplit.Cell (DBMTreeKernel.matrix sub 1048576 root) (FlashLeafSplit.tlift y) := by
    intro a b
    have h := hc a b
    simp only [DBMTreeKernel.matrix, hroot] at h ⊢
    push_cast at h ⊢
    have : ((256 : ℝ) * ((DBMSourceTree.data n).db a b : ℝ)) / 1048576 =
        ((DBMSourceTree.data n).db a b : ℝ) / 4096 := by ring
    linarith [this ▸ h]
  obtain ⟨l, hl, hcl⟩ := DBMTreeKernel.terminal_cover sub 1048576 (by norm_num) hv _ root hc0
  obtain ⟨hvl, hD, hS⟩ := hpk l hl
  refine radius (pk l) hvl y hy0 hy1 ?_ C Z r hf
  intro a b
  have h := hcl a b
  simpa only [mMatrix, DBMTreeKernel.matrix, hD, hS, Nat.cast_ofNat, Int.cast_ofNat] using h

end
end N11Formalization.Paid16MatrixCellCertificate
