import N11Formalization.ResidualHfm
import N11Formalization.ResidualDerivPos

/-!
# `hFm` 的无条件形态（Lead 短装配，R287）

**对象**：`nd_end_to_end_right` 第 5 项 `hFm : ∀ k : Fin 12, (Fm k).Mem (TCSystem certCR k)`。

**依据**（Lead 亲验：两处 `hD` 绑元形状**逐字相同** ✓）：
* `hFm_of_hD (D : Fin 5 → Fin 7 → RatInterval)
     (hD : ∀ (k : Fin 5) (i : Fin 7), (D k i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k)) :
     ∀ k : Fin 12, (fmCert lamCert D k).Mem (TCSystem certCR k)`（**参数化** ✓）
* `hD : ∀ (k : Fin 5) (i : Fin 7), (D k i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k)`
  （`ResidualDerivPos.lean` L175–177，**零未消前提** ✓）
* `D := compIv 0..3 / compIv4`（`ResidualDerivD.lean` L619 ✓）

⚠ **命名口径（我自己的老坑，本轮复发一次）** ✗✓：`D` 的全名是 **`N11Formalization.D`**（**文件名不是 namespace** ✗）；
本文件已在 `namespace N11Formalization` 内 ⇒ 用**裸名** ✓。

**⇒ 本定理 = 一次应用**（不是新数学 ✗）。等级：kernel-proved，无 `sorry`／无自定义 `axiom`／无 `native_decide`。
-/

noncomputable section

namespace N11Formalization

/-- **`hFm` 无条件**：`hFm_of_hD` 在 `D`（= `compIv` 族）上的实例，`hD` 由 `ResidualDerivPos.hD` 供给。 -/
theorem hFm_uncond :
    ∀ k : Fin 12, (fmCert lamCert D k).Mem (TCSystem certCR k) :=
  hFm_of_hD D hD

/-- `Fm` 的显式取值（供消费点直接代入）✓。 -/
def FmUncond : Fin 12 → RatInterval := fmCert lamCert D

/-- 同一结论以 `FmUncond` 表述 ✓。 -/
theorem hFm_uncond' : ∀ k : Fin 12, (FmUncond k).Mem (TCSystem certCR k) :=
  hFm_uncond

end N11Formalization
