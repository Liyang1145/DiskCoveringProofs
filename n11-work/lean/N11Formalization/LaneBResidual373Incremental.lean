import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCard

/-! Incremental assembly of the 373 residual radius certificates.

This module proves no radius certificate.  It turns the all-at-once premise
into a reusable split: one literal member of `residual373`, plus certificates
for the remaining 372 ids after erasing that member.  The split preserves the
exact cardinals and does not weaken the radius obligation. -/
set_option autoImplicit false
namespace N11Formalization.LaneBResidual373Incremental
open Finset
noncomputable section

abbrev residual373 : Finset (Fin 5011) :=
  EnergyTerminalBatchB13RefineSixteenResidual.residualIDs

theorem residual373_card : residual373.card = 373 :=
  EnergyTerminalBatchB13RefineSixteenResidual.residualIDs_card

theorem residual373_eq_insert_erase (n : Fin 5011)
    (hn : n ∈ residual373) :
    residual373 = insert n (residual373.erase n) :=
  (Finset.insert_erase hn).symm

theorem erase_card_of_mem (n : Fin 5011)
    (hn : n ∈ residual373) : (residual373.erase n).card = 372 := by
  rw [Finset.card_erase_of_mem hn, residual373_card]
  norm_num

theorem b13_remaining_of_erase_certificate (n : Fin 5011)
    (hn : n ∈ residual373)
    (hcert : EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hrest : ∀ k, k ∈ residual373.erase n →
        EnergyTerminalBatchB13.ResidualRadiusCertificate k) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalBatchB13RefineSixteenResidual.b13_remaining_of_residual_radius_certificates
  intro k hk
  by_cases hkn : k = n
  · simpa [hkn] using hcert
  · exact hrest k (Finset.mem_erase.mpr ⟨hkn, hk⟩)

theorem b13_remaining_of_1409_certificate
    (hn : (1409 : Fin 5011) ∈ residual373)
    (hcert : EnergyTerminalBatchB13.ResidualRadiusCertificate (1409 : Fin 5011))
    (hrest : ∀ k, k ∈ residual373.erase (1409 : Fin 5011) →
        EnergyTerminalBatchB13.ResidualRadiusCertificate k) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  b13_remaining_of_erase_certificate (1409 : Fin 5011) hn hcert hrest

end
end N11Formalization.LaneBResidual373Incremental
#check @N11Formalization.LaneBResidual373Incremental.residual373_card
#check @N11Formalization.LaneBResidual373Incremental.residual373_eq_insert_erase
#check @N11Formalization.LaneBResidual373Incremental.erase_card_of_mem
#check @N11Formalization.LaneBResidual373Incremental.b13_remaining_of_erase_certificate
#check @N11Formalization.LaneBResidual373Incremental.b13_remaining_of_1409_certificate
#print axioms N11Formalization.LaneBResidual373Incremental.erase_card_of_mem
#print axioms N11Formalization.LaneBResidual373Incremental.b13_remaining_of_erase_certificate
