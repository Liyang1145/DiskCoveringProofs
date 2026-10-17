/-
n11-formalization —— **指定原 root 的达到（∀ 指定 C891RootSpec）**。

写域：本文件（`evidence/flash-caps/`，验通后**原字节**进 src 为 `FlashAttainmentSpecifiedRoot.lean`）。

## 0. 目标（lead R-FBC-14 / R-FBC-16）

把 `FlashAttainmentFinal.exists_root_covers_of_signs` 的 **`∃S`** 提升为**对指定 `S`**：

```
∀ S, (S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert → S.radiusIndex = 6) →
     Covers (centersOfRoot S.root) (Rstar S) ∧ Rstar S < 19/50
```

**身份不能更换 root**：由 `C891RootSpec.root_unique`（源 `Conditional/RootSpec.lean`，实际 type 已读）
⇒ 满足同一 `sys`/盒 的任意两个 spec 的 `root` **相同**；故任一指定 spec 的结论与
`GridBridge.nd_box_final` 给出的那个 S 的结论**落在同一个根上**。

## 1. 口径（lead R-FBC-16）

* **不复制定义**：`ActualSigns` 等一律取自 `FlashAttainmentFinal`（避免同名不同 type 的两份）。
* `ActualSigns`（五组符号条件、**88 个未证符号**）**保持显式前提**、**非本件承诺**；由 flash-slack-faces 负责。
* 本件只做「指定 root 的达到 + 半径阈值 + 根身份」三件事，不加任何额外 Signs 承诺。
* 无浮点、无 `sorry`、无自定义 axiom。
-/

import Mathlib
import N11Formalization.Definitions
import N11Formalization.TCSystem
import N11Formalization.RootRangeBoxFull
import N11Formalization.GridBridge
import N11Formalization.FlashSlackRoot
import N11Formalization.FlashAttainmentFinal

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section

namespace N11Formalization.FlashAttainmentSpecifiedRoot

open N11Formalization
open N11Formalization.FlashAttainmentFinal (ActualSigns hcover_of_signs inCertBox_root)

/-! ## §1 指定 root 的达到（∀ S）与半径阈值 -/

/-- **指定 root 的达到**：`S` 与证书同一 `sys`/盒/半径坐标 + `ActualSigns S.root` ⟹
`Covers (centersOfRoot S.root) (Rstar S)`（委派 `FlashSlackRoot.covers_of_root`，**无 hF0**）。 -/
theorem covers_of_specified_root (S : C891RootSpec) (hsys : S.sys = TCSystem)
    (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6)
    (hs : ActualSigns S.root) :
    Covers (centersOfRoot S.root) (Rstar S) :=
  FlashSlackRoot.covers_of_root S hsys hlo hhi hidx
    (hcover_of_signs S.root (inCertBox_root S hlo hhi) hs)

/-- **指定 root 的半径阈值**：同一 sys/盒/半径坐标 ⟹ `Rstar S < 19/50`
（`Rstar_lt_R0_of_bound` + 盒上端精确值 `boxHiCert 6 = 1837489169128606637938325/2^82`）。 -/
theorem Rstar_lt_of_spec (S : C891RootSpec) (hhi : S.boxHi = boxHiCert)
    (hidx : S.radiusIndex = 6) : Rstar S < 19 / 50 := by
  refine Rstar_lt_R0_of_bound S ?_
  rw [hhi, hidx, boxHiCert_six_eq]
  norm_num

/-- **∀ 指定 root（把 `∃S` 提升为 `∀S`）**：`ActualSigns` 显式传入（不打包当进展）。 -/
theorem covers_of_any_specified_root
    (hs : ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 → ActualSigns S.root) :
    ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 → Covers (centersOfRoot S.root) (Rstar S) ∧ Rstar S < 19 / 50 :=
  fun S hsys hlo hhi hidx =>
    ⟨covers_of_specified_root S hsys hlo hhi hidx (hs S hsys hlo hhi hidx),
      Rstar_lt_of_spec S hhi hidx⟩

/-! ## §2 身份稳定性（根唯一性 ⇒ 不能换 root） -/

/-- **同一 `sys`/盒的两个 spec 有相同的根**（由 `C891RootSpec.root_unique`）。 -/
theorem root_eq_of_same_sys_box (S S' : C891RootSpec) (hsys : S.sys = S'.sys)
    (hlo : S.boxLo = S'.boxLo) (hhi : S.boxHi = S'.boxHi) : S'.root = S.root := by
  refine S.root_unique ?_
  refine ⟨fun i => ?_, ?_⟩
  · have h := S'.root_mem.1 i
    rw [hlo, hhi]
    exact h
  · rw [hsys]
    exact S'.root_mem.2

/-- **与 `nd_box_final` 的根同一**：任一满足证书 `sys`/盒 的 spec，其根 = `nd_box_final` 那个 S 的根。 -/
theorem root_eq_of_nd_box_final (S : C891RootSpec) (hsys : S.sys = TCSystem)
    (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) :
    ∃ S0 : C891RootSpec, S0.sys = TCSystem ∧ S0.boxLo = boxLoCert ∧ S0.boxHi = boxHiCert ∧
      S0.radiusIndex = 6 ∧ S.root = S0.root := by
  obtain ⟨S0, hs, hl, hh, hi, _, _⟩ := GridBridge.nd_box_final
  exact ⟨S0, hs, hl, hh, hi,
    root_eq_of_same_sys_box S0 S (hs.trans hsys.symm) (hl.trans hlo.symm) (hh.trans hhi.symm)⟩

/-- **结论在身份层面可搬运（不换 root 的显式形式）**：同一 `sys`/盒/半径坐标的两个 spec，
其达到命题 `Covers (centersOfRoot ·.root) (Rstar ·)` **等价**（因根相同、`Rstar` 相同）。 -/
theorem covers_transfer (S S' : C891RootSpec) (hsys : S.sys = S'.sys) (hlo : S.boxLo = S'.boxLo)
    (hhi : S.boxHi = S'.boxHi) (hidx : S.radiusIndex = S'.radiusIndex) :
    Covers (centersOfRoot S.root) (Rstar S) ↔ Covers (centersOfRoot S'.root) (Rstar S') := by
  have hroot : S'.root = S.root := root_eq_of_same_sys_box S S' hsys hlo hhi
  have hR : Rstar S' = Rstar S := by rw [Rstar, Rstar, hroot, hidx]
  rw [hroot, hR]

/-! ## §3 actual consumer：主口径阈值 `19/50` 形式 -/

/-- **主口径消费者（指定 root，单实例）**：指定 `S` 的覆盖成立且 `Rstar S < 19/50` ⇒
**盘半径直接用主口径阈值 `19/50`** 的覆盖（`Covers.mono`）。 -/
theorem covers_at_threshold (S : C891RootSpec) (hsys : S.sys = TCSystem)
    (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6)
    (hs : ActualSigns S.root) :
    Covers (centersOfRoot S.root) (19 / 50) :=
  (covers_of_specified_root S hsys hlo hhi hidx hs).mono (le_of_lt (Rstar_lt_of_spec S hhi hidx))

/-- **主口径消费者（∀ 指定 root）**。 -/
theorem covers_at_threshold_any
    (hs : ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 → ActualSigns S.root) :
    ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 → Covers (centersOfRoot S.root) (19 / 50) ∧ Rstar S < 19 / 50 :=
  fun S hsys hlo hhi hidx =>
    ⟨covers_at_threshold S hsys hlo hhi hidx (hs S hsys hlo hhi hidx),
      Rstar_lt_of_spec S hhi hidx⟩

end N11Formalization.FlashAttainmentSpecifiedRoot

#print axioms N11Formalization.FlashAttainmentSpecifiedRoot.covers_of_specified_root
#print axioms N11Formalization.FlashAttainmentSpecifiedRoot.Rstar_lt_of_spec
#print axioms N11Formalization.FlashAttainmentSpecifiedRoot.covers_of_any_specified_root
#print axioms N11Formalization.FlashAttainmentSpecifiedRoot.root_eq_of_same_sys_box
#print axioms N11Formalization.FlashAttainmentSpecifiedRoot.root_eq_of_nd_box_final
#print axioms N11Formalization.FlashAttainmentSpecifiedRoot.covers_transfer
#print axioms N11Formalization.FlashAttainmentSpecifiedRoot.covers_at_threshold
#print axioms N11Formalization.FlashAttainmentSpecifiedRoot.covers_at_threshold_any
