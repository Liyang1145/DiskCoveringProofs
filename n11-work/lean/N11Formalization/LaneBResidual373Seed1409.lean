import N11Formalization.LaneBResidual373Incremental
import N11Formalization.FrozenCapResidualMembership
import N11Formalization.EnergyTerminalBatchB13PublicResidualCanonical

/-! First singleton of the refined 373-id residual.

The frozen node `1409` is an exact member of the base residual and is not one
of the sixteen ids removed by the repair.  The public canonical row-cap tree
excludes every valid packet carrying its frozen `f0Lo`/`g` data.  Accordingly,
the only remaining obligation for this id is production of such a canonical
packet on the counter-radius branch; the other 372 certificates stay explicit.
-/
set_option autoImplicit false
namespace N11Formalization.LaneBResidual373Seed1409
open Finset
noncomputable section

theorem mem_1409 :
    (1409 : Fin 5011) ∈ LaneBResidual373Incremental.residual373 := by
  rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff]
  obtain ⟨hterminal, hsharp, hbase⟩ :=
    (EnergyTerminalBatchB13.mem_residualIDs_iff (1409 : Fin 5011)).mp
      FrozenCapResidualMembership.mem_1409
  refine ⟨hterminal, hsharp, ?_⟩
  rw [EnergyTerminalBatchB13RefineSixteenResidual.paidIDs_eq_base_union_removed]
  intro hpaid
  rcases Finset.mem_union.mp hpaid with hpaid | hremoved
  · exact hbase hpaid
  · exact (by decide +kernel : (1409 : Fin 5011) ∉
      EnergyTerminalBatchB13RefineSixteenResidual.removedIDs) hremoved

theorem residual373_eq_insert_1409 :
    LaneBResidual373Incremental.residual373 =
      insert (1409 : Fin 5011)
        (LaneBResidual373Incremental.residual373.erase (1409 : Fin 5011)) :=
  LaneBResidual373Incremental.residual373_eq_insert_erase (1409 : Fin 5011) mem_1409

theorem certificate_of_canonical_producer
    (h : EnergyTerminalBatchB13.CanonicalPacketProducer (1409 : Fin 5011)
      (fun _ p => FrozenCapPublicExcludedAggregate.PublicResidualData p)) :
    EnergyTerminalBatchB13.ResidualRadiusCertificate (1409 : Fin 5011) :=
  EnergyTerminalBatchB13.PublicResidualCanonical.radius_certificate_of_canonical_producer h

theorem b13_remaining_of_1409_canonical_producer
    (hprod : EnergyTerminalBatchB13.CanonicalPacketProducer (1409 : Fin 5011)
      (fun _ p => FrozenCapPublicExcludedAggregate.PublicResidualData p))
    (hrest : ∀ k, k ∈ LaneBResidual373Incremental.residual373.erase (1409 : Fin 5011) →
      EnergyTerminalBatchB13.ResidualRadiusCertificate k) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  LaneBResidual373Incremental.b13_remaining_of_1409_certificate mem_1409
    (certificate_of_canonical_producer hprod) hrest

theorem b13_remaining_of_1409_and_erase_canonical_producers
    (hprod : EnergyTerminalBatchB13.CanonicalPacketProducer (1409 : Fin 5011)
      (fun _ p => FrozenCapPublicExcludedAggregate.PublicResidualData p))
    (hrest : ∀ k, k ∈ LaneBResidual373Incremental.residual373.erase (1409 : Fin 5011) →
      EnergyTerminalBatchB13.CanonicalPacketProducer k
        (fun _ p => FrozenCapPublicExcludedAggregate.PublicResidualData p)) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  b13_remaining_of_1409_canonical_producer hprod
    (fun k hk => EnergyTerminalBatchB13.PublicResidualCanonical.radius_certificate_of_canonical_producer
      (hrest k hk))

end
end N11Formalization.LaneBResidual373Seed1409
#check @N11Formalization.LaneBResidual373Seed1409.mem_1409
#check @N11Formalization.LaneBResidual373Seed1409.residual373_eq_insert_1409
#check @N11Formalization.LaneBResidual373Seed1409.certificate_of_canonical_producer
#check @N11Formalization.LaneBResidual373Seed1409.b13_remaining_of_1409_canonical_producer
#check @N11Formalization.LaneBResidual373Seed1409.b13_remaining_of_1409_and_erase_canonical_producers
#print axioms N11Formalization.LaneBResidual373Seed1409.mem_1409
#print axioms N11Formalization.LaneBResidual373Seed1409.b13_remaining_of_1409_canonical_producer
