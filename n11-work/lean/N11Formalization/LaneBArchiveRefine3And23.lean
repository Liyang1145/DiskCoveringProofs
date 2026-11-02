import N11Formalization.EnergyTerminalBatchB13ResidualCertificates
import N11Formalization.EnergyRefineN0003Restored
import N11Formalization.EnergyRefineN0023Restored
import N11Formalization.LaneBResidual346Bridge

/-! Discharge residual ids 3 and 23 using their restored archived split
refinements.  No other residual certificate is supplied. -/
set_option autoImplicit false
namespace N11Formalization.LaneBArchiveRefine3And23
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

theorem residualCertificate3 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN0003.new_radius 3
    (by simp [EnergyRefineN0003.newIDs]) y hy0 hy1 hc C Z r hf).le

theorem residualCertificate23 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 23 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN0023.new_radius 23
    (by simp [EnergyRefineN0023.newIDs]) y hy0 hy1 hc C Z r hf).le

theorem b13_remaining_of_residual346_omitting_3_23
    (h : ∀ n, n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
      n ≠ 3 → n ≠ 23 → EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  LaneBResidual346Bridge.b13_remaining_of_residual346_radius_certificates
    (fun n hn => by
      by_cases h3 : n = 3
      · subst n
        exact residualCertificate3
      · by_cases h23 : n = 23
        · subst n
          exact residualCertificate23
        · exact h n hn h3 h23)

end
end N11Formalization.LaneBArchiveRefine3And23
#check @N11Formalization.LaneBArchiveRefine3And23.residualCertificate3
#check @N11Formalization.LaneBArchiveRefine3And23.residualCertificate23
#check @N11Formalization.LaneBArchiveRefine3And23.b13_remaining_of_residual346_omitting_3_23
#print axioms N11Formalization.LaneBArchiveRefine3And23.b13_remaining_of_residual346_omitting_3_23
