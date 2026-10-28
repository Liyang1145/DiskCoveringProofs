/-
n11-formalization —— **原 root 的真实消费者（`hs` 由盒推出，不再作前提）**。

写域：本文件（新件；evidence/ 先写，核通后原字节进 src）。
依赖：`N11Formalization.FlashAttainmentSpecifiedRoot`（指定 root 消费）
     + `N11Formalization.FlashTilingHubChordSigns`（我的 25 条 + `actualSigns : InCertBox u → ActualSigns u`）。

**关键**：`FlashAttainmentSpecifiedRoot.covers_of_specified_root` 原以 `hs : ActualSigns S.root` 为**前提**；
此处用 `actualSigns S.root (inCertBox_root S hlo hhi)` **把它推出** ⇒ 结论不再带 `hs` ✓
（`ActualSigns = hcv(63，slack 的 ringConvex) + hh0/hh1/chordA/chordB(25，本件依赖) = 88 符号全付）。
-/
import Mathlib
import N11Formalization.FlashAttainmentSpecifiedRoot
import N11Formalization.FlashTilingHubChordSigns
import N11Formalization.FlashSlackRoot
import N11Formalization.FlashAttainmentFinal

set_option linter.unusedVariables false

noncomputable section

namespace N11Formalization.FlashAttainmentRstarConsumer

open N11Formalization

/-- **指定 root（单实例，`hs` 已消）**：任一与证书一致的 `S` ⟹ `Covers (centersOfRoot S.root) (Rstar S)`。
半径即 `Rstar S` 本身（**未放大**）。 -/
theorem covers_of_specified_root_actual (S : C891RootSpec) (hsys : S.sys = TCSystem)
    (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    Covers (centersOfRoot S.root) (Rstar S) :=
  FlashAttainmentSpecifiedRoot.covers_of_specified_root S hsys hlo hhi hidx
    (FlashTilingHubChordSigns.actualSigns S.root
      (FlashAttainmentFinal.inCertBox_root S hlo hhi))

/-- **∀ 指定 root（`hs` 已消）** + 半径阈值。 -/
theorem covers_of_any_specified_root_actual :
    ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 → Covers (centersOfRoot S.root) (Rstar S) ∧ Rstar S < 19 / 50 :=
  fun S hsys hlo hhi hidx =>
    ⟨covers_of_specified_root_actual S hsys hlo hhi hidx,
      FlashAttainmentSpecifiedRoot.Rstar_lt_of_spec S hhi hidx⟩

/-- **存在形式（`hs` 已消）**：`nd_box_final` 的根被 11 个 `Rstar S` 盘覆盖。 -/
theorem exists_root_covers_actual :
    ∃ S : C891RootSpec, S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧
      S.radiusIndex = 6 ∧ Rstar S < 19 / 50 ∧ Covers (centersOfRoot S.root) (Rstar S) :=
  FlashSlackRoot.exists_root_covers (fun S hs hlo hhi hidx =>
    _root_.N11Formalization.FlashAttainmentFinal.hcover_of_signs S.root
      (FlashAttainmentFinal.inCertBox_root S hlo hhi)
      (FlashTilingHubChordSigns.actualSigns S.root
        (FlashAttainmentFinal.inCertBox_root S hlo hhi)))

end N11Formalization.FlashAttainmentRstarConsumer

#print axioms N11Formalization.FlashAttainmentRstarConsumer.covers_of_specified_root_actual
#print axioms N11Formalization.FlashAttainmentRstarConsumer.covers_of_any_specified_root_actual
#print axioms N11Formalization.FlashAttainmentRstarConsumer.exists_root_covers_actual
