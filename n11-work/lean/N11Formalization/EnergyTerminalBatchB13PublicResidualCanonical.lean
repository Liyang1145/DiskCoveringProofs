import N11Formalization.EnergyTerminalBatchB13ResidualCertificates
import N11Formalization.FrozenCapPublicExcludedAggregate

/-! The seven public frozen-cap exclusions as canonical packet exclusions.

This closes the interface gap between the residual radius certificate consumer
and the existing public exclusion tree.  It does not assert that a canonical
packet producer exists; it only removes that exclusion hypothesis from future
producers for the seven public residual ids. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13.PublicResidualCanonical
open N11Formalization
noncomputable section

/-- Packet data covered by one of the seven public frozen-cap exclusions. -/
def Canonical {m : ℕ} (p : PaidCellCertificateM.Packet m) : Prop :=
  FrozenCapPublicExcludedAggregate.PublicResidualData p

/-- Any valid packet with public residual data is impossible.  The node id is
not needed separately because `PublicResidualData` already pins it to one of
the seven public ids. -/
theorem canonical_exclusion (n : Fin 5011) :
    CanonicalPacketExclusion n
      (fun _ p => FrozenCapPublicExcludedAggregate.PublicResidualData p) := by
  constructor
  intro m p _ hcanon hp
  exact FrozenCapPublicExcludedAggregate.not_valid_of_public_residual p hp hcanon

/-- For every node, canonical production under the public exclusion is exactly
the same residual radius obligation as before.  In particular, the public
exclusion supplies no packet and pays no residual id by itself. -/
theorem canonical_producer_iff_radius_certificate (n : Fin 5011) :
    CanonicalPacketProducer n
        (fun _ p => FrozenCapPublicExcludedAggregate.PublicResidualData p) ↔
      ResidualRadiusCertificate n :=
  canonical_packet_producer_iff_residual_radius_certificate
    (canonical_exclusion n)

/-- A producer under the public canonicality condition is a genuine residual
radius certificate. -/
theorem radius_certificate_of_canonical_producer {n : Fin 5011}
    (h : CanonicalPacketProducer n
      (fun _ p => FrozenCapPublicExcludedAggregate.PublicResidualData p)) :
    ResidualRadiusCertificate n :=
  (canonical_producer_iff_radius_certificate n).mp h

/-- Conversely, an already-proved residual radius certificate makes the
counter-radius producer branch vacuous. -/
theorem canonical_producer_of_radius_certificate {n : Fin 5011}
    (h : ResidualRadiusCertificate n) :
    CanonicalPacketProducer n
      (fun _ p => FrozenCapPublicExcludedAggregate.PublicResidualData p) :=
  (canonical_producer_iff_radius_certificate n).mpr h

end
end N11Formalization.EnergyTerminalBatchB13.PublicResidualCanonical

#check @N11Formalization.EnergyTerminalBatchB13.PublicResidualCanonical.canonical_exclusion
#check @N11Formalization.EnergyTerminalBatchB13.PublicResidualCanonical.canonical_producer_iff_radius_certificate
#check @N11Formalization.EnergyTerminalBatchB13.PublicResidualCanonical.radius_certificate_of_canonical_producer
#check @N11Formalization.EnergyTerminalBatchB13.PublicResidualCanonical.canonical_producer_of_radius_certificate
#print axioms N11Formalization.EnergyTerminalBatchB13.PublicResidualCanonical.canonical_exclusion
#print axioms N11Formalization.EnergyTerminalBatchB13.PublicResidualCanonical.canonical_producer_iff_radius_certificate
