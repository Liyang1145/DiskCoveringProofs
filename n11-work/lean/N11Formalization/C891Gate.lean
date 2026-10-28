import N11Formalization.BoxRstar
import N11Formalization.GridBridge

/-! C891 gate: 五条数据假设全部由 HsumPayloadB/GridBridge 供给（hK0_B,hK1_B,hK'0_B,hK'1_B,
hresCons_B,hsumB_grid,hsumRB_grid 经 NdBox.nd_box → GridBridge.nd_box_final）。无条件 RootSpecBall。 -/

noncomputable section
namespace N11Formalization.C891Gate
open N11Formalization

theorem c891_rootSpecBall : RootSpecBall := by
  obtain ⟨S, hsys, hlo, hhi, -, -, -⟩ := GridBridge.nd_box_final
  have hu := S.exists_unique
  rw [hlo, hhi, hsys] at hu
  obtain ⟨z, hz, hzu⟩ := hu
  exact ⟨z, ⟨mem_closedBall_cert_iff.mpr hz.1, hz.2⟩,
    fun w hw => hzu w ⟨mem_closedBall_cert_iff.mp hw.1, hw.2⟩⟩

theorem c891_readout :
    RootSpecBall ∧ ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ S.radiusIndex = 6 ∧
        Rstar S < 19 / 50 := by
  obtain ⟨S, h1, h2, h3, h4, -, h6⟩ := GridBridge.nd_box_final
  exact ⟨c891_rootSpecBall, S, h1, h2, h3, h4, h6⟩

end N11Formalization.C891Gate