import Mathlib
import N11Formalization.FlashLocalMixedPinned

/-!
# FlashLocal — 120 局部叶承重链 · 第十环（基座）：Taylor 拆分的**定义**与**范数证书**

按 Lead 2026-09-30 指定：位移与余项必须**定义**（不是任意未绑定参数），且
`frob Wrem ≤ q²/2` **必须来自 `FlashLocalChart` 的实际第二余项 lemma**（不可由三阶界推）。

本件只含定义 + 三条证书（**不依赖** Lead 的 `ResumeFlux*` 件），供合成件
`FlashLocalDirectional` 直接 `import`，以便在 Lead 的 olean 就位前先把这一半核掉。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset

/-- 位移族 `disp_i = circleMap (θ_i + x_i) − circleMap (θ_i)`。 -/
def disp (θ x : Fin 9 → ℝ) : Fin 9 → Point := fun i => circleMap (θ i + x i) - circleMap (θ i)

/-- **二阶余项** `Wrem_i = disp_i − x_i • tangent_i`（= 源 L5 的 `w`）。 -/
def Wrem (θ x : Fin 9 → ℝ) : Fin 9 → Point := fun i => disp θ x i - x i • circleTangent (θ i)

/-- **三阶余项**（**定义**，源 L5）：`R_i = disp_i − x_i • tangent_i + (x_i²/2) • circle_i`。 -/
def thirdRemFamily (θ x : Fin 9 → ℝ) : Fin 9 → Point :=
  fun i => Wrem θ x i + (x i ^ 2 / 2) • circleMap (θ i)

/-- Taylor 拆分的加法形：`Jx + Wrem = disp`。 -/
theorem Jx_add_Wrem (θ x : Fin 9 → ℝ) :
    (fun i => Jx θ x i + Wrem θ x i) = disp θ x := by
  funext i
  simp [Jx, Wrem, disp]

/-- 我的 `h0_quadratic_mixed_lower` 的槽型 ↔ 这里的 `Wrem`：`(−x²/2)•circle + R = Wrem`。 -/
theorem neg_rad_add_third (θ x : Fin 9 → ℝ) :
    (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + thirdRemFamily θ x i) = Wrem θ x := by
  funext i
  simp [thirdRemFamily, Wrem]

/-- **范数证书 1**：`frob Wrem ≤ q²/2`，**来自 `FlashLocalChart` 的实际第二余项 lemma**
（`anchorRemainder_frob_norm_le`），不是从三阶界推的。 -/
theorem frob_Wrem_le (θ x : Fin 9 → ℝ) : frob (Wrem θ x) ≤ (∑ i, x i ^ 2) / 2 :=
  anchorRemainder_frob_norm_le θ x

/-- **范数证书 2**：`frob R ≤ q³/6`，来自 `FlashLocalThirdFrob` 的族级三阶聚合。 -/
theorem frob_thirdRem_le (θ x : Fin 9 → ℝ) :
    frob (thirdRemFamily θ x) ≤ (∑ i, x i ^ 2) * Real.sqrt (∑ i, x i ^ 2) / 6 :=
  anchorThird_frob_norm_le θ x

/-- **范数证书 3**：`∑ ‖disp‖² ≤ ∑ x²`（弦长，`FlashLocalChart`）。 -/
theorem disp_frob_le (θ x : Fin 9 → ℝ) :
    ∑ i, ‖disp θ x i‖ ^ 2 ≤ ∑ i, x i ^ 2 :=
  anchorDelta_frob_le θ x

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.Jx_add_Wrem
#print axioms N11Formalization.FlashLocal.neg_rad_add_third
#print axioms N11Formalization.FlashLocal.frob_Wrem_le
#print axioms N11Formalization.FlashLocal.frob_thirdRem_le
#print axioms N11Formalization.FlashLocal.disp_frob_le
