import N11Formalization.EnergyTerminalBatchB13ResidualCertificates
import N11Formalization.LaneBResidual346Bridge
import N11Formalization.EnergyRefineN0003Restored
import N11Formalization.EnergyRefineN0023Restored
import N11Formalization.EnergyRefineN0038
import N11Formalization.EnergyRefineN3432
import N11Formalization.EnergyRefineN3490
import N11Formalization.EnergyRefineN3517
import N11Formalization.EnergyRefineN3550
import N11Formalization.EnergyRefineN3564
import N11Formalization.EnergyRefineN3569
import N11Formalization.EnergyRefineN3578
import N11Formalization.EnergyRefineN3738
import N11Formalization.EnergyRefineN3781
import N11Formalization.EnergyRefineN3825
import N11Formalization.EnergyRefineN3854

/-! Discharge the fourteen ids having structurally complete archive refinements.
The twelve canonical modules are byte-identical to their archived source except
for removal of one unbounded heartbeat directive; ids 3 and 23 use fresh
restored modules.  The remaining interface is exact at 332 ids.  No theorem here
proves a residual packet or the seven class exclusions. -/
set_option autoImplicit false
namespace N11Formalization.LaneBArchiveRefineAll14
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def archiveIDs : Finset (Fin 5011) := {3, 23, 38, 3432, 3490, 3517, 3550, 3564, 3569, 3578, 3738, 3781, 3825, 3854}

theorem certificate3 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN0003.new_radius 3 (by simp [EnergyRefineN0003.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate23 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 23 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN0023.new_radius 23 (by simp [EnergyRefineN0023.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate38 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 38 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN0038.new_radius 38 (by simp [EnergyRefineN0038.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3432 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3432 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3432.new_radius 3432 (by simp [EnergyRefineN3432.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3490 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3490 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3490.new_radius 3490 (by simp [EnergyRefineN3490.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3517 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3517 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3517.new_radius 3517 (by simp [EnergyRefineN3517.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3550 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3550 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3550.new_radius 3550 (by simp [EnergyRefineN3550.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3564 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3564 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3564.new_radius 3564 (by simp [EnergyRefineN3564.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3569 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3569 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3569.new_radius 3569 (by simp [EnergyRefineN3569.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3578 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3578 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3578.new_radius 3578 (by simp [EnergyRefineN3578.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3738 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3738 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3738.new_radius 3738 (by simp [EnergyRefineN3738.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3781 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3781 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3781.new_radius 3781 (by simp [EnergyRefineN3781.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3825 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3825 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3825.new_radius 3825 (by simp [EnergyRefineN3825.newIDs])
    y hy0 hy1 hc C Z r hf).le
theorem certificate3854 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3854 := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact (EnergyRefineN3854.new_radius 3854 (by simp [EnergyRefineN3854.newIDs])
    y hy0 hy1 hc C Z r hf).le

theorem certificateOf (n : Fin 5011) (hn : n ∈ archiveIDs) :
    EnergyTerminalBatchB13.ResidualRadiusCertificate n := by
  simp only [archiveIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact certificate3
  · exact certificate23
  · exact certificate38
  · exact certificate3432
  · exact certificate3490
  · exact certificate3517
  · exact certificate3550
  · exact certificate3564
  · exact certificate3569
  · exact certificate3578
  · exact certificate3738
  · exact certificate3781
  · exact certificate3825
  · exact certificate3854

theorem b13_remaining_of_residual332_radius_certificates
    (h : ∀ n, n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
      n ∉ archiveIDs → EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  LaneBResidual346Bridge.b13_remaining_of_residual346_radius_certificates
    (fun n hn => by
      by_cases hmem : n ∈ archiveIDs
      · exact certificateOf n hmem
      · exact h n hn hmem)

theorem main_of_residual332_radius_certificates_and_seven_classes
    (h : ∀ n, n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
      n ∉ archiveIDs → EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  LaneBResidual346Bridge.main_of_residual346_radius_certificates_and_seven_classes
    (fun n hn => by
      by_cases hmem : n ∈ archiveIDs
      · exact certificateOf n hmem
      · exact h n hn hmem) hclasses

theorem full_disk_bound_of_residual332_radius_certificates_and_seven_classes
    (h : ∀ n, n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
      n ∉ archiveIDs → EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  LaneBResidual346Bridge.full_disk_bound_of_residual346_radius_certificates_and_seven_classes
    (fun n hn => by
      by_cases hmem : n ∈ archiveIDs
      · exact certificateOf n hmem
      · exact h n hn hmem) hclasses

end
end N11Formalization.LaneBArchiveRefineAll14
#check @N11Formalization.LaneBArchiveRefineAll14.certificateOf
#check @N11Formalization.LaneBArchiveRefineAll14.b13_remaining_of_residual332_radius_certificates
#check @N11Formalization.LaneBArchiveRefineAll14.main_of_residual332_radius_certificates_and_seven_classes
#print axioms N11Formalization.LaneBArchiveRefineAll14.b13_remaining_of_residual332_radius_certificates
#print axioms N11Formalization.LaneBArchiveRefineAll14.full_disk_bound_of_residual332_radius_certificates_and_seven_classes
