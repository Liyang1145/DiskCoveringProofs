import N11Formalization.EnergyTerminalBatchB13
import N11Formalization.PaidCellCertificateM

/-! Exact certificate interface for the 389-id B13 residual.

`ResidualRadiusCertificate n` records precisely the radius obligation that
`EnergyTerminalBatchB13.RemainingTerminalRadius` assigns to a residual id.
The equivalence below is exact: this interface neither weakens the remaining
energy premise nor asserts that any certificate exists. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

/-- The full chart-radius obligation for one residual terminal id. -/
structure ResidualRadiusCertificate (n : Fin 5011) : Prop where
  radius : ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
    FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y) →
    ∀ (C Z : Fin 11 → Point) (r : ℝ),
      Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius ≤ r

/-- The missing geometric producer, stated only on the counter-radius branch.
For a residual terminal, every feasible configuration with `r < sourceRadius`
must produce a valid packet based at that same frozen node.  Packet validity
then contradicts the strict radius bound. -/
structure ResidualPacketProducer (n : Fin 5011) : Prop where
  exists_valid_packet : ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) →
    (∑ q, y q = 1) →
    FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y) →
    ∀ (C Z : Fin 11 → Point) (r : ℝ),
      Feasible (chartAnchors y) C Z r → r < SourceExactRoot.sourceRadius →
      ∃ (m : ℕ) (p : PaidCellCertificateM.Packet m),
        p.nodeID = n ∧ PaidCellCertificateM.Valid p

/-- A family of packets which are known to be impossible by a frozen row-cap
certificate. Keeping this predicate abstract lets the public exclusions be
consumed without asserting that every packet is canonical. -/
structure CanonicalPacketExclusion (n : Fin 5011)
    (canonical : ∀ m : ℕ, PaidCellCertificateM.Packet m → Prop) : Prop where
  not_valid : ∀ (m : ℕ) (p : PaidCellCertificateM.Packet m),
    p.nodeID = n → canonical m p → PaidCellCertificateM.Valid p → False

/-- The missing novelty: a counter-radius configuration must produce a packet
at the frozen node together with the canonical data required by the row caps. -/
structure CanonicalPacketProducer (n : Fin 5011)
    (canonical : ∀ m : ℕ, PaidCellCertificateM.Packet m → Prop) : Prop where
  exists_canonical_packet : ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) →
    (∑ q, y q = 1) →
    FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y) →
    ∀ (C Z : Fin 11 → Point) (r : ℝ),
      Feasible (chartAnchors y) C Z r → r < SourceExactRoot.sourceRadius →
      ∃ (m : ℕ) (p : PaidCellCertificateM.Packet m),
        p.nodeID = n ∧ canonical m p ∧ PaidCellCertificateM.Valid p

theorem residual_packet_producer_of_canonical {n : Fin 5011}
    {canonical : ∀ m : ℕ, PaidCellCertificateM.Packet m → Prop}
    (h : CanonicalPacketProducer n canonical) : ResidualPacketProducer n := by
  constructor
  intro y hy0 hy1 hc C Z r hf hr
  obtain ⟨m, p, hnode, -, hp⟩ :=
    h.exists_canonical_packet y hy0 hy1 hc C Z r hf hr
  exact ⟨m, p, hnode, hp⟩

theorem residual_radius_certificate_of_canonical_packet_producer
    {n : Fin 5011} {canonical : ∀ m : ℕ, PaidCellCertificateM.Packet m → Prop}
    (hprod : CanonicalPacketProducer n canonical)
    (hexcl : CanonicalPacketExclusion n canonical) : ResidualRadiusCertificate n := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  by_contra hle
  push_neg at hle
  obtain ⟨m, p, hnode, hcanon, hp⟩ :=
    hprod.exists_canonical_packet y hy0 hy1 hc C Z r hf hle
  exact hexcl.not_valid m p hnode hcanon hp

theorem residual_radius_certificate_of_packet_producer {n : Fin 5011}
    (h : ResidualPacketProducer n) : ResidualRadiusCertificate n := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  by_contra hle
  push_neg at hle
  obtain ⟨m, p, hnode, hp⟩ :=
    h.exists_valid_packet y hy0 hy1 hc C Z r hf hle
  have hnc : FlashLeafSplit.Cell
      (DBMTreeKernel.matrix DBMSourceTree.data 4096 p.nodeID)
      (FlashLeafSplit.tlift y) := by
    simpa only [← hnode] using hc
  have hlt := PaidCellCertificateM.common_chart_radius p hp y hy0 hy1 hnc C Z r hf
  linarith

theorem residual_radius_certificate_of_remaining
    (h : RemainingTerminalRadius) (n : Fin 5011) (hn : n ∈ residualIDs) :
    ResidualRadiusCertificate n :=
  ⟨fun y hy0 hy1 hc C Z r hf =>
    (remaining_iff.mp h) n hn y hy0 hy1 hc C Z r hf⟩

theorem remaining_of_residual_radius_certificates
    (h : ∀ n : Fin 5011, n ∈ residualIDs → ResidualRadiusCertificate n) :
    RemainingTerminalRadius := by
  rw [remaining_iff]
  intro n hn y hy0 hy1 hc C Z r hf
  exact (h n hn).radius y hy0 hy1 hc C Z r hf

theorem remaining_of_packet_producers
    (h : ∀ n : Fin 5011, n ∈ residualIDs → ResidualPacketProducer n) :
    RemainingTerminalRadius :=
  remaining_of_residual_radius_certificates
    (fun n hn => residual_radius_certificate_of_packet_producer (h n hn))

theorem remaining_of_canonical_packet_producers
    {canonical : ∀ m : ℕ, PaidCellCertificateM.Packet m → Prop}
    (hprod : ∀ n : Fin 5011, n ∈ residualIDs → CanonicalPacketProducer n canonical)
    (hexcl : ∀ n : Fin 5011, n ∈ residualIDs → CanonicalPacketExclusion n canonical) :
    RemainingTerminalRadius :=
  remaining_of_residual_radius_certificates
    (fun n hn => residual_radius_certificate_of_canonical_packet_producer
      (hprod n hn) (hexcl n hn))

theorem remaining_iff_residual_radius_certificates :
    RemainingTerminalRadius ↔
      ∀ n : Fin 5011, n ∈ residualIDs → ResidualRadiusCertificate n :=
  ⟨residual_radius_certificate_of_remaining,
    remaining_of_residual_radius_certificates⟩

theorem chart_radius_of_residual_radius_certificates
    (h : ∀ n : Fin 5011, n ∈ residualIDs → ResidualRadiusCertificate n)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (C Z : Fin 11 → Point) (r : ℝ) (hf : Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius ≤ r :=
  chart_radius_of_remaining
    (remaining_of_residual_radius_certificates h) y hy0 hy1 C Z r hf

theorem chart_radius_of_packet_producers
    (h : ∀ n : Fin 5011, n ∈ residualIDs → ResidualPacketProducer n)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (C Z : Fin 11 → Point) (r : ℝ) (hf : Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius ≤ r :=
  chart_radius_of_residual_radius_certificates
    (fun n hn => residual_radius_certificate_of_packet_producer (h n hn))
    y hy0 hy1 C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13
#check @N11Formalization.EnergyTerminalBatchB13.residual_radius_certificate_of_remaining
#check @N11Formalization.EnergyTerminalBatchB13.residual_radius_certificate_of_packet_producer
#check @N11Formalization.EnergyTerminalBatchB13.residual_packet_producer_of_canonical
#check @N11Formalization.EnergyTerminalBatchB13.residual_radius_certificate_of_canonical_packet_producer
#check @N11Formalization.EnergyTerminalBatchB13.remaining_of_canonical_packet_producers
#check @N11Formalization.EnergyTerminalBatchB13.remaining_of_residual_radius_certificates
#check @N11Formalization.EnergyTerminalBatchB13.remaining_of_packet_producers
#check @N11Formalization.EnergyTerminalBatchB13.remaining_iff_residual_radius_certificates
#check @N11Formalization.EnergyTerminalBatchB13.chart_radius_of_residual_radius_certificates
#check @N11Formalization.EnergyTerminalBatchB13.chart_radius_of_packet_producers
#print axioms N11Formalization.EnergyTerminalBatchB13.remaining_of_residual_radius_certificates
#print axioms N11Formalization.EnergyTerminalBatchB13.remaining_of_packet_producers
#print axioms N11Formalization.EnergyTerminalBatchB13.chart_radius_of_residual_radius_certificates
