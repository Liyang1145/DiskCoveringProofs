import N11Formalization.BoxRstar
import N11Formalization.FmAssembly

/-!
# `#print axioms` 读数：`BoxRstar.lean` 的每条承重定理

复现：
```
cd research-2026/n11-formalization/lean
$env:ELAN_HOME="E:\lean-lab\.elan"; $env:PATH="E:\lean-lab\.elan\bin;"+$env:PATH
lake env lean .\BoxRstarPrintAxioms.lean > ..\evidence\box-rstar\PRINT-AXIOMS.txt 2>&1
```
（`verify.ps1 -File` 在本机对中文路径有解析问题，故直接用 `lake env lean`。）

期望：零 `sorryAx`、零自定义 `axiom`、零 `Lean.ofReduceBool`/`native_decide` 桥；
传递依赖只应出现 `propext`、`Classical.choice`、`Quot.sound`。
-/

namespace N11Formalization

#print axioms rhoCert_pos
#print axioms rhoCertR_pos
#print axioms boxLo_boxHi_center_radius
#print axioms boxHiCert_sub_boxLoCert
#print axioms certC_six_eq
#print axioms boxHiCert_six_eq
#print axioms boxLoCert_six_eq
#print axioms certC_eight_eq
#print axioms certC_eight_transcription_gap
#print axioms pow_two_readings
#print axioms boxHiCert_six_real_eq
#print axioms boxLoCert_six_real_eq
#print axioms box_rstar_readings
#print axioms mem_closedBall_cert_iff
#print axioms certCR_mem_ball
#print axioms root_spec_certBox
#print axioms root_six_mem_cert_box
#print axioms Rstar_mem_of_krawczyk
#print axioms Rstar_le_boxHiCert_six_cast
#print axioms Rstar_le_boxHiCert_six
#print axioms boxLoCert_six_le_Rstar_cast
#print axioms boxLoCert_six_le_Rstar
#print axioms c891RootSpec_of_ball
#print axioms c891RootSpec_of_ball_with_idx
#print axioms c891RootSpec_of_krawczyk
#print axioms c891RootSpec_of_right_data
#print axioms boxHiCert_six_lt_R0
#print axioms boxHiCert_six_lt_R0_cross
#print axioms boxHiCert_six_lt_R0_real
#print axioms boxLoCert_six_pos
#print axioms Rstar_lt_R0_of_krawczyk
#print axioms Rstar_pos_of_krawczyk
#print axioms Rstar_readings_of_krawczyk
#print axioms Rstar_readings_of_ball
#print axioms Rstar_lt_R0_of_ball
-- FmAssembly.lean (Lead-approved item 1)
#print axioms tcSystem_adjointBlock_eq
#print axioms fmCert_mem_first
#print axioms fmCert_mem_adjoint
#print axioms mem_fmCert
#print axioms hLam_rfl
#print axioms mem_fmCert_cert
#print axioms mem_fmCert_of_point
#print axioms tcRootSpec_radiusIndex

end N11Formalization
