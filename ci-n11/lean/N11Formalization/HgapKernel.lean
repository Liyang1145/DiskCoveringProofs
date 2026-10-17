import N11Formalization.DeltaAny
import N11Formalization.HessBoxMem
import N11Formalization.HessSeamBall
import N11Formalization.F1.BallD35C7

/-!
# `HgapKernel.lean` — 成员 `hgap-kernel`：R257 简报 §3 接口 **I-1**（+ cone §9 未付的 B2 桥）

**义务**：把 `evidence/lead/scratch/FinalBridgeB.lean` 里 `theorem core` 的末步前提 `hgap`
换成**证成的定理**，产出 `coreClosed`（`hgap` 不再是参数）。`core` 的另外 7 条前提
（`hadj/hd/hWa/hWb/hW6/hWp/hpos`）**保持为参数**（由 `premise-bundle` 供给，本件不碰）。

**写域**：只写 `evidence/hgap-kernel/`。**未改** `lean/**`、未碰根表、未写 STATUS/DEAD、未登记 claim。
**判据**：**禁**占位证 / 自定义公理 / 内核外判定（简报 §5.3，本件行锚定扫描 0 命中）。
`lake env lean <本件>` exit 0 且输出 **0 字节**（⇒ 也不许有 warning）；
公理画像另一次跑（`#print axioms` 在末尾临时追加）。

## ★ 实测发现：`hgap` 内含一条 cone 明文「未付」的桥（Lead 已采纳，见 team-message-70bc2ad0 / 0a357599）

`hgap` **不是**纯书写形态差。闭合它**必需**一般点的一阶系数桥

```
(fderiv ℝ (DeltaX k) u) (Pi.single i 1) = dUxReal k i (pad12 u)      （Δy 同）      （= B2）
```

理由：`DeltaAny.SRad2_any` 给 `∂²S = 2(X·∂²X + ∂ᵢX·∂ⱼX) + 2(Y·∂²Y + ∂ᵢY·∂ⱼY)`，
而盒靶 `distHessRealBox` 的第一/三项原子是 `dUxReal` 的积 ⇒ 需要
`∂ᵢX·∂ⱼX + ∂ᵢY·∂ⱼY = ux_i·ux_j + uy_i·uy_j`；这**不能**由「组合式」恒等式
`X·a_i + Y·b_i = 0`（`a_i := ux_i − ∂ᵢX`）推出（取 `a_i = −t·Y, b_i = t·X` 即破坏）。
即 `DeltaAny.lean` **§9 L734–753** 自己登记「本轮未走通」的那一条。

**本件把 B2 补上，且 §9 L750–752 担心的「新显式前提」在本文路线上不存在**：
§9 计划走 `fderiv_comp` 在 `pad12 x`（12 维点）处求值 ⇒ 需要 12 维口径的正性；
本文改走**逐支 `HasFDerivAt` + CLM 取值**（cone 已有的一般点料），
前提只有 `core` 已有的 `hWa/hWb/hW6/hWp`（**全在 7 维点 `u` 上**）⇒ **零新增前提**。

## 结构

| 节 | 内容 | 依赖 |
|---|---|---|
| §1 | `scalar_hgap` 纯标量核（`0 < S` ＋ 6 条形状等式） | `Real.mul_self_sqrt` + `field_simp` + `ring` |
| §2 | **B2** 一阶系数桥 `dDeltaX_single` / `dDeltaY_single`（`k=0..4` 分派） | `hasFDerivAt_Uvec*_any`(C4)、`dUvec*CLM_single_eq_dUvec*Real`(C7)、`hasFDerivAt_hub*_any`/`hasFDerivAt_wPoint*_any`(C5)、`hasFDerivAt_ringCenter*_any`(C2)、`ringCLM*_single_eq_ring*Real`/`WpAt_eq_WpReal`(C7)、`pad12_{four,five,six}`、DeltaAny `PtCF*/HubCF*/Delta*_eq/Delta*12_sub` |
| §3 | **B1** `dSRad_any`（`HessSeamHL7.dSRad_single` 的 `u0 → x` 升格；cone 无 `_any` 版） | `DeltaAny.hasFDerivAt_Delta{X,Y}_any` |
| §4 | **B3** `hgapProved` = `hgap` 的语句但右端直接写 `distHessRealBox (pad12 u) k i j` | §1＋§2＋§3＋`DeltaAny.SRad2_any`＋`first7_pad12` |
| §5 | `coreClosed`（I-1 签名；件 B 机械链的三条引理按 Lead 裁定 **由本件独占重述**） | §4 ＋ scratch 链 |
-/

noncomputable section

set_option maxHeartbeats 4000000

namespace N11Formalization

namespace HgapKernel

/-! ## 1. 纯标量核 -/

/-- **纯标量核**（I-1 的代数内核；无字面量依赖、可复用）。

口径：`S` 是 `HessSeam.SRad k u`（只须 `0 < S`）；`X = Δx`、`Y = Δy`；`p = ∂²Δx`、`q = ∂²Δy`；
`ai = ∂ᵢΔx, aj = ∂ⱼΔx, bi = ∂ᵢΔy, bj = ∂ⱼΔy` 是一阶系数；
`U = ∂²S`、`Pi = ∂ᵢS`、`Pj = ∂ⱼS`；`A/B/C` 是盒靶的三个中间体。
右端**逐字照 `Lead.HessBoxMem.distHessRealBox`（`HessBoxMem.lean` L27–37）的结合形**书写
（`2 * ((1 / (2 * √S)) * A)` 而不是 `2 * (1 / (2 * √S)) * A`）⇒ §4 回填不需要任何重组。 -/
theorem scalar_hgap {S X Y p q ai aj bi bj A B C U Pi Pj : ℝ}
    (hS : 0 < S)
    (hA : A = ai * aj + bi * bj)
    (hB : B = X * p + Y * q)
    (hC : C = (X * ai + Y * bi) * (X * aj + Y * bj))
    (hU : U = 2 * (X * p + ai * aj) + 2 * (Y * q + bi * bj))
    (hPi : Pi = 2 * (X * ai + Y * bi))
    (hPj : Pj = 2 * (X * aj + Y * bj)) :
    1 / (2 * Real.sqrt S) * U
        + (-2) * (1 / (2 * Real.sqrt S))
            * ((2 * Real.sqrt S) * (2 * Real.sqrt S))⁻¹ * Pj * Pi
      = 2 * ((1 / (2 * Real.sqrt S)) * A) + 2 * ((1 / (2 * Real.sqrt S)) * B)
        - 2 * ((1 / (S * (2 * Real.sqrt S))) * C) := by
  rw [hA, hB, hC, hU, hPi, hPj]
  have hs : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt (le_of_lt hS)
  have h2 : (2 * Real.sqrt S) * (2 * Real.sqrt S) = 4 * S := by
    rw [show (2 * Real.sqrt S) * (2 * Real.sqrt S) = (2 * 2) * (Real.sqrt S * Real.sqrt S) by ring]
    rw [hs]
    norm_num
  have hzero2 : (0 : ℝ) < 2 := by norm_num
  have hposw : 0 < 2 * Real.sqrt S := mul_pos hzero2 (Real.sqrt_pos.mpr hS)
  have hne : (2 : ℝ) * Real.sqrt S ≠ 0 := ne_of_gt hposw
  have hne4 : (4 : ℝ) * S ≠ 0 := mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hS)
  have hneS : S * (2 * Real.sqrt S) ≠ 0 := mul_ne_zero (ne_of_gt hS) hne
  field_simp [hne, hne4, hneS, h2, hs]
  rw [Real.sq_sqrt (le_of_lt hS)]   -- run1 实测：field_simp 输出 √S ^ 2，hs 匹配不上
  ring

/-! ## 2. B2：一阶系数桥（`DeltaAny.lean` §9 登记为「未付」的那一条） -/

/-- **B2（Δx 支）**：一般点 `x : Fin 7 → ℝ` 上 `∂ᵢ(Δx_k) = dUxReal k i (pad12 x)`。
按 `k = 0..4` 分派；`k = 0..3` 用 `hasFDerivAt_Uvec0_any` + `dUvec0CLM_single_eq_dUvec0Real`
+ `hasFDerivAt_hub{0,1}_0_any`；`k = 4` 用 `hasFDerivAt_wPoint_0_any` + `hasFDerivAt_ringCenter0_any`
+ `ringCLM0_single_eq_ring0Real`。**零新增前提**（四条正性就是 `core` 的 `hWa/hWb/hW6/hWp`）。 -/
theorem dDeltaX_single (k : Fin 5) (i : Fin 7) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (_hWp : 0 < Wpf x) :
    (fderiv ℝ (DeltaX k) x) (Pi.single i 1) = dUxReal k i (pad12 x) := by
  fin_cases k
  · -- k = 0：`Uvec 1` − `hub1`（`coord 5`）
    show (fderiv ℝ (DeltaX (0 : Fin 5)) x) (Pi.single i 1) = dUxReal (0 : Fin 5) i (pad12 x)
    have hP : HasFDerivAt (DeltaAny.PtCF (0 : Fin 5)) (dUvec0CLM 1 x) x :=
      hasFDerivAt_Uvec0_any 1 x (ne_of_gt hWa) (ne_of_gt hWb)
    have hH : HasFDerivAt (DeltaAny.HubCF (0 : Fin 5)) (coord 5) x := hasFDerivAt_hub1_0_any x
    have hd : HasFDerivAt (DeltaX (0 : Fin 5)) (dUvec0CLM 1 x - coord 5) x := hP.sub hH
    rw [hd.fderiv, sub_apply, dUvec0CLM_single_eq_dUvec0Real 1 i x]
    simp only [dUxReal]
  · -- k = 1：`Uvec 2` − `hub0`（`coord 4`）
    show (fderiv ℝ (DeltaX (1 : Fin 5)) x) (Pi.single i 1) = dUxReal (1 : Fin 5) i (pad12 x)
    have hP : HasFDerivAt (DeltaAny.PtCF (1 : Fin 5)) (dUvec0CLM 2 x) x :=
      hasFDerivAt_Uvec0_any 2 x (ne_of_gt hWa) (ne_of_gt hWb)
    have hH : HasFDerivAt (DeltaAny.HubCF (1 : Fin 5)) (coord 4) x := hasFDerivAt_hub0_0_any x
    have hd : HasFDerivAt (DeltaX (1 : Fin 5)) (dUvec0CLM 2 x - coord 4) x := hP.sub hH
    rw [hd.fderiv, sub_apply, dUvec0CLM_single_eq_dUvec0Real 2 i x]
    simp only [dUxReal]
  · -- k = 2：`Uvec 3` − `hub0`（`coord 4`）
    show (fderiv ℝ (DeltaX (2 : Fin 5)) x) (Pi.single i 1) = dUxReal (2 : Fin 5) i (pad12 x)
    have hP : HasFDerivAt (DeltaAny.PtCF (2 : Fin 5)) (dUvec0CLM 3 x) x :=
      hasFDerivAt_Uvec0_any 3 x (ne_of_gt hWa) (ne_of_gt hWb)
    have hH : HasFDerivAt (DeltaAny.HubCF (2 : Fin 5)) (coord 4) x := hasFDerivAt_hub0_0_any x
    have hd : HasFDerivAt (DeltaX (2 : Fin 5)) (dUvec0CLM 3 x - coord 4) x := hP.sub hH
    rw [hd.fderiv, sub_apply, dUvec0CLM_single_eq_dUvec0Real 3 i x]
    simp only [dUxReal]
  · -- k = 3：`Uvec 8` − `hub1`（`coord 5`）
    show (fderiv ℝ (DeltaX (3 : Fin 5)) x) (Pi.single i 1) = dUxReal (3 : Fin 5) i (pad12 x)
    have hP : HasFDerivAt (DeltaAny.PtCF (3 : Fin 5)) (dUvec0CLM 8 x) x :=
      hasFDerivAt_Uvec0_any 8 x (ne_of_gt hWa) (ne_of_gt hWb)
    have hH : HasFDerivAt (DeltaAny.HubCF (3 : Fin 5)) (coord 5) x := hasFDerivAt_hub1_0_any x
    have hd : HasFDerivAt (DeltaX (3 : Fin 5)) (dUvec0CLM 8 x - coord 5) x := hP.sub hH
    rw [hd.fderiv, sub_apply, dUvec0CLM_single_eq_dUvec0Real 8 i x]
    simp only [dUxReal]
  · -- k = 4：`wPoint` − `ringCenter 6`
    show (fderiv ℝ (DeltaX (4 : Fin 5)) x) (Pi.single i 1) = dUxReal (4 : Fin 5) i (pad12 x)
    have hP : HasFDerivAt (DeltaAny.PtCF (4 : Fin 5)) ((1 / 2 : ℝ) • (coord 4 + coord 5)) x :=
      hasFDerivAt_wPoint_0_any x
    have hH : HasFDerivAt (DeltaAny.HubCF (4 : Fin 5)) (ringCLM0 6 x) x :=
      hasFDerivAt_ringCenter0_any 6 x (ne_of_gt hW6)
    have hd : HasFDerivAt (DeltaX (4 : Fin 5))
        ((1 / 2 : ℝ) • (coord 4 + coord 5) - ringCLM0 6 x) x := hP.sub hH
    rw [hd.fderiv, sub_apply, ringCLM0_single_eq_ring0Real i x (ne_of_gt hW6)]
    simp only [dUxReal]

/-- **B2（Δy 支）**：`∂ᵢ(Δy_k) = dUyReal k i (pad12 x)`。
`k = 0..3` 的驻点叶 y 坐标恒 `0` ⇒ CLM 取 `(0 : (Fin 7 → ℝ) →L[ℝ] ℝ)`（与 `dUyReal` 的写法同形）。
`k = 4` 需要 `WpAt x ≠ 0`：由 `hWp : 0 < Wpf x` 供给，等式 `WpAt x = Wpf x` 用 `rfl` **显式钉住**
（Lead 裁定：不许只靠 `simp` 顺走）。 -/
theorem dDeltaY_single (k : Fin 5) (i : Fin 7) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    (fderiv ℝ (DeltaY k) x) (Pi.single i 1) = dUyReal k i (pad12 x) := by
  fin_cases k
  · show (fderiv ℝ (DeltaY (0 : Fin 5)) x) (Pi.single i 1) = dUyReal (0 : Fin 5) i (pad12 x)
    have hP : HasFDerivAt (DeltaAny.PtCF1 (0 : Fin 5)) (dUvec1CLM 1 x) x :=
      hasFDerivAt_Uvec1_any 1 x (ne_of_gt hWa) (ne_of_gt hWb)
    have hH : HasFDerivAt (DeltaAny.HubCF1 (0 : Fin 5)) (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) x :=
      hasFDerivAt_hub1_1_any x
    have hd : HasFDerivAt (DeltaY (0 : Fin 5)) (dUvec1CLM 1 x - 0) x := hP.sub hH
    rw [hd.fderiv, sub_apply, dUvec1CLM_single_eq_dUvec1Real 1 i x]
    simp only [dUyReal]
  · show (fderiv ℝ (DeltaY (1 : Fin 5)) x) (Pi.single i 1) = dUyReal (1 : Fin 5) i (pad12 x)
    have hP : HasFDerivAt (DeltaAny.PtCF1 (1 : Fin 5)) (dUvec1CLM 2 x) x :=
      hasFDerivAt_Uvec1_any 2 x (ne_of_gt hWa) (ne_of_gt hWb)
    have hH : HasFDerivAt (DeltaAny.HubCF1 (1 : Fin 5)) (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) x :=
      hasFDerivAt_hub0_1_any x
    have hd : HasFDerivAt (DeltaY (1 : Fin 5)) (dUvec1CLM 2 x - 0) x := hP.sub hH
    rw [hd.fderiv, sub_apply, dUvec1CLM_single_eq_dUvec1Real 2 i x]
    simp only [dUyReal]
  · show (fderiv ℝ (DeltaY (2 : Fin 5)) x) (Pi.single i 1) = dUyReal (2 : Fin 5) i (pad12 x)
    have hP : HasFDerivAt (DeltaAny.PtCF1 (2 : Fin 5)) (dUvec1CLM 3 x) x :=
      hasFDerivAt_Uvec1_any 3 x (ne_of_gt hWa) (ne_of_gt hWb)
    have hH : HasFDerivAt (DeltaAny.HubCF1 (2 : Fin 5)) (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) x :=
      hasFDerivAt_hub0_1_any x
    have hd : HasFDerivAt (DeltaY (2 : Fin 5)) (dUvec1CLM 3 x - 0) x := hP.sub hH
    rw [hd.fderiv, sub_apply, dUvec1CLM_single_eq_dUvec1Real 3 i x]
    simp only [dUyReal]
  · show (fderiv ℝ (DeltaY (3 : Fin 5)) x) (Pi.single i 1) = dUyReal (3 : Fin 5) i (pad12 x)
    have hP : HasFDerivAt (DeltaAny.PtCF1 (3 : Fin 5)) (dUvec1CLM 8 x) x :=
      hasFDerivAt_Uvec1_any 8 x (ne_of_gt hWa) (ne_of_gt hWb)
    have hH : HasFDerivAt (DeltaAny.HubCF1 (3 : Fin 5)) (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) x :=
      hasFDerivAt_hub1_1_any x
    have hd : HasFDerivAt (DeltaY (3 : Fin 5)) (dUvec1CLM 8 x - 0) x := hP.sub hH
    rw [hd.fderiv, sub_apply, dUvec1CLM_single_eq_dUvec1Real 8 i x]
    simp only [dUyReal]
  · -- `WpAt x = Wpf x` 显式钉住（Lead 裁定 3），再取 `≠ 0`
    have hw : WpAt x = Wpf x := rfl
    have hWp' : WpAt x ≠ 0 := by
      rw [hw]
      exact ne_of_gt hWp
    show (fderiv ℝ (DeltaY (4 : Fin 5)) x) (Pi.single i 1) = dUyReal (4 : Fin 5) i (pad12 x)
    have hP : HasFDerivAt (DeltaAny.PtCF1 (4 : Fin 5))
        ((1 / (2 * Real.sqrt (WpAt x))) • ((2 * x 6) • coord 6
          - (2 * ((x 5 - x 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))) x :=
      hasFDerivAt_wPoint_1_any x hWp'
    have hH : HasFDerivAt (DeltaAny.HubCF1 (4 : Fin 5)) (ringCLM1 6 x) x :=
      hasFDerivAt_ringCenter1_any 6 x (ne_of_gt hW6)
    have hd : HasFDerivAt (DeltaY (4 : Fin 5))
        ((1 / (2 * Real.sqrt (WpAt x))) • ((2 * x 6) • coord 6
          - (2 * ((x 5 - x 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))
          - ringCLM1 6 x) x := hP.sub hH
    rw [hd.fderiv, sub_apply, ringCLM1_single_eq_ring1Real i x (ne_of_gt hW6)]
    simp only [dUyReal, WpAt_eq_WpReal, pad12_four, pad12_five, pad12_six]

/-! ## 3. B1：一般点的 `∂S` 读数（cone 只有 `u0` 版 `HessSeamHL7.dSRad_single` ⇒ 本件升格） -/

/-- `S_k = Δx_k² + Δy_k²` 的一阶取值（一般点）。逐字重放 `HessSeamHL7.dSRad_single` 的 `u0 → x`。 -/
theorem dSRad_any (k : Fin 5) (i : Fin 7) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    (fderiv ℝ (HessSeam.SRad k) x) (Pi.single i 1)
      = 2 * (DeltaX k x) * ((fderiv ℝ (DeltaX k) x) (Pi.single i 1))
        + 2 * (DeltaY k x) * ((fderiv ℝ (DeltaY k) x) (Pi.single i 1)) := by
  have hX := DeltaAny.hasFDerivAt_DeltaX_any k x hWa hWb hW6 hWp
  have hY := DeltaAny.hasFDerivAt_DeltaY_any k x hWa hWb hW6 hWp
  have hsum := (hX.mul hX).add (hY.mul hY)
  have hval : (fderiv ℝ (DeltaX k * DeltaX k + DeltaY k * DeltaY k) x) (Pi.single i 1)
      = 2 * (DeltaX k x) * ((fderiv ℝ (DeltaX k) x) (Pi.single i 1))
        + 2 * (DeltaY k x) * ((fderiv ℝ (DeltaY k) x) (Pi.single i 1)) := by
    rw [hsum.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  exact hval

/-! ## 4. B3：`hgap` 由「前提」变「定理」 -/

/-- **`hgapProved`**：`FinalBridgeB.core` 末步前提 `hgap` 的**证成版**，
右端**不写裸展开式**、直接写盒靶 `Lead.HessBoxMem.distHessRealBox (pad12 u) k i j`
（Lead 裁定 1：一并消掉 `_out.txt` 那条类型失配）。
只吃 `core` 已有的 `hWa/hWb/hW6/hWp/hpos` ⇒ **无新增承重假设**。 -/
theorem hgapProved (k : Fin 5) (i j : Fin 7) (u : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) u) (hWb : 0 < Wfun ((resSlot k) + 1) u)
    (hW6 : 0 < Wfun 6 u) (hWp : 0 < Wpf u) (hpos : 0 < HessSeam.SRad k u) :
    1 / (2 * Real.sqrt (HessSeam.SRad k u)) * secondPartial (HessSeam.SRad k) u i j
        + (-2) * (1 / (2 * Real.sqrt (HessSeam.SRad k u)))
            * ((2 * Real.sqrt (HessSeam.SRad k u)) * (2 * Real.sqrt (HessSeam.SRad k u)))⁻¹
            * (fderiv ℝ (HessSeam.SRad k) u) (Pi.single j 1)
            * (fderiv ℝ (HessSeam.SRad k) u) (Pi.single i 1)
      = Lead.HessBoxMem.distHessRealBox (pad12 u) k i j := by
  -- 一阶读数（B1 + B2）
  have hPi : (fderiv ℝ (HessSeam.SRad k) u) (Pi.single i 1)
      = 2 * (DeltaX k u * dUxReal k i (pad12 u) + DeltaY k u * dUyReal k i (pad12 u)) := by
    rw [dSRad_any k i u hWa hWb hW6 hWp, dDeltaX_single k i u hWa hWb hW6 hWp,
      dDeltaY_single k i u hWa hWb hW6 hWp]
    try ring
  have hPj : (fderiv ℝ (HessSeam.SRad k) u) (Pi.single j 1)
      = 2 * (DeltaX k u * dUxReal k j (pad12 u) + DeltaY k u * dUyReal k j (pad12 u)) := by
    rw [dSRad_any k j u hWa hWb hW6 hWp, dDeltaX_single k j u hWa hWb hW6 hWp,
      dDeltaY_single k j u hWa hWb hW6 hWp]
    try ring
  -- 二阶读数（cone `SRad2_any` + B2 逐支替换）
  have hU : secondPartial (HessSeam.SRad k) u i j
      = 2 * (DeltaX k u * secondPartial (DeltaX k) u i j
            + dUxReal k i (pad12 u) * dUxReal k j (pad12 u))
        + 2 * (DeltaY k u * secondPartial (DeltaY k) u i j
            + dUyReal k i (pad12 u) * dUyReal k j (pad12 u)) := by
    rw [DeltaAny.SRad2_any k u hWa hWb hW6 hWp i j,
      dDeltaX_single k i u hWa hWb hW6 hWp, dDeltaX_single k j u hWa hWb hW6 hWp,
      dDeltaY_single k i u hWa hWb hW6 hWp, dDeltaY_single k j u hWa hWb hW6 hWp]
    try ring
  -- `S_k u = Δx² + Δy²`（换成盒靶的 `Apt/Bpt` 写法）
  have hr : HessSeam.SRad k u
      = ((Apt k (pad12 u)).ofLp 0 - (Bpt k (pad12 u)).ofLp 0) ^ 2
        + ((Apt k (pad12 u)).ofLp 1 - (Bpt k (pad12 u)).ofLp 1) ^ 2 := by
    simp only [HessSeam.SRad, DeltaX, DeltaY, pow_two]
  have hgap := scalar_hgap (S := HessSeam.SRad k u) (X := DeltaX k u) (Y := DeltaY k u)
    (p := secondPartial (DeltaX k) u i j) (q := secondPartial (DeltaY k) u i j)
    (ai := dUxReal k i (pad12 u)) (aj := dUxReal k j (pad12 u))
    (bi := dUyReal k i (pad12 u)) (bj := dUyReal k j (pad12 u))
    (U := secondPartial (HessSeam.SRad k) u i j)
    (Pi := (fderiv ℝ (HessSeam.SRad k) u) (Pi.single i 1))
    (Pj := (fderiv ℝ (HessSeam.SRad k) u) (Pi.single j 1))
    hpos rfl rfl rfl hU hPi hPj
  rw [hgap]
  simp only [Lead.HessBoxMem.distHessRealBox, first7_pad12, hr, DeltaX, DeltaY, pow_two]

/-! ## 5. `coreClosed`（I-1）+ 件 B 机械链的重述（Lead 裁定 2：本件独占这三条） -/

/-- 点一般化的投影交换（`HessSeam.hessEntry_eq_secondPartial_residualFun` 的 `u0 → z` 版）。
**重述**自 `evidence/lead/scratch/FinalBridgeB.lean`（scratch 不可 import ⇒ 必须有唯一权威份；
Lead 已裁定本件为权威份，另两名成员不得重述）。 -/
theorem vec_secondPartial_eq_any (z : Fin 7 → ℝ)
    (hd : ∀ᶠ v in nhds z, DifferentiableAt ℝ residualFun v)
    (hadjz : DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) z)
    (mm : Fin 5) :
    (fderiv ℝ (fun v : Fin 7 → ℝ => fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w mm) v) z)
      = ((ContinuousLinearMap.compL ℝ (Fin 7 → ℝ) (Fin 5 → ℝ) ℝ)
            (ContinuousLinearMap.proj mm))
          ∘SL (fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) z) := by
  let P : (Fin 5 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj mm
  let Φ : ((Fin 7 → ℝ) →L[ℝ] (Fin 5 → ℝ)) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin 7 → ℝ) (Fin 5 → ℝ) ℝ) P
  have hfun : (P ∘ residualFun) = fun w : Fin 7 → ℝ => residualFun w mm := by
    funext w
    rw [Function.comp_apply, ContinuousLinearMap.proj_apply]
  have hpt' : (fun v : Fin 7 → ℝ => fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w mm) v)
      =ᶠ[nhds z] fun v : Fin 7 → ℝ => Φ (fderiv ℝ residualFun v) := by
    filter_upwards [hd] with v hv
    have hcv : HasFDerivAt (P ∘ residualFun) (P ∘SL fderiv ℝ residualFun v) v :=
      (ContinuousLinearMap.hasFDerivAt P).comp v hv.hasFDerivAt
    rw [hfun] at hcv
    rw [hcv.fderiv, ContinuousLinearMap.compL_apply]
  have hM : fderiv ℝ (fun v : Fin 7 → ℝ => fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w mm) v) z
      = Φ ∘SL (fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) z) := by
    rw [hpt'.fderiv_eq]
    exact ((ContinuousLinearMap.hasFDerivAt Φ).comp z hadjz.hasFDerivAt).fderiv
  show fderiv ℝ (fun v : Fin 7 → ℝ => fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w mm) v) z
      = Φ ∘SL (fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) z)
  exact hM

/-- `coord 6` 的二阶 = 0（一般点）。**重述**自 scratch（同上一条理由）。 -/
theorem secondPartial_clm_any (L : (Fin 7 → ℝ) →L[ℝ] ℝ) (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => L z) x i j = 0 := by
  rw [secondPartial_eq_of_hasFDerivAt (TowerBC.hasFDerivAt_fderiv_clm_any L x) i j]
  exact zero_apply _

/-- `√(SRad k)` 在一般点邻域可微。 **重述**自 scratch（同上一条理由）。 -/
theorem eventually_diff_sqrtSRad_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) (hpos : 0 < HessSeam.SRad k x) :
    ∀ᶠ z in nhds x, DifferentiableAt ℝ (fun z : Fin 7 → ℝ => Real.sqrt (HessSeam.SRad k z)) z := by
  have hcont : ContinuousAt (HessSeam.SRad k) x :=
    ((DeltaAny.eventually_diff_SRad_any k x hWa hWb hW6 hWp).self_of_nhds).continuousAt
  filter_upwards [DeltaAny.eventually_diff_SRad_any k x hWa hWb hW6 hWp,
    hcont.eventually (IsOpen.mem_nhds isOpen_ne (ne_of_gt hpos))] with z hzS hz
  exact ((Real.hasDerivAt_sqrt hz).differentiableAt).comp z hzS

/-- **接口 I-1 的交付件 `coreClosed`**：`FinalBridgeB.core` 去掉 `hgap` 参数后的闭合版。
其余 7 条前提（`hadj/hd/hWa/hWb/hW6/hWp/hpos`）**保持为参数**（`premise-bundle` 供给）。
链 (i)–(vi) 逐字重放 Lead 的机械链；**末步 `exact hgapProved …`（§4）——不再是前提。** -/
theorem coreClosed (k : Fin 5) (i j : Fin 7) (u : Fin 7 → ℝ)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u)
    (hd : ∀ᶠ z in nhds u, DifferentiableAt ℝ residualFun z)
    (hWa : 0 < Wfun (resSlot k) u) (hWb : 0 < Wfun ((resSlot k) + 1) u)
    (hW6 : 0 < Wfun 6 u) (hWp : 0 < Wpf u) (hpos : 0 < HessSeam.SRad k u) :
    HessSeam.hessEntryAt u i j k = Lead.HessBoxMem.distHessRealBox (pad12 u) k i j := by
  -- (i) 投影交换
  have hcomp := vec_secondPartial_eq_any u hd hadj k
  have hleft : HessSeam.hessEntryAt u i j k
      = ((fderiv ℝ (fun v : Fin 7 → ℝ => fderiv ℝ residualFun v) u)
          (Pi.single j 1)) (Pi.single i 1) k := rfl
  have hclm : ((fderiv ℝ (fun v : Fin 7 → ℝ => fderiv ℝ residualFun v) u)
          (Pi.single j 1)) (Pi.single i 1) k
      = secondPartial (fun w : Fin 7 → ℝ => residualFun w k) u i j := by
    rw [show secondPartial (fun w : Fin 7 → ℝ => residualFun w k) u i j
        = (((fderiv ℝ (fun v : Fin 7 → ℝ => fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w k) v) u)
            (Pi.single j 1)) (Pi.single i 1)) from rfl, hcomp]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.proj_apply]
  -- (ii) 逐点：`residualFun · k = √SRad − coord 6`
  have hfun : (fun w : Fin 7 → ℝ => residualFun w k)
      = fun w : Fin 7 → ℝ => Real.sqrt (HessSeam.SRad k w) - w 6 := by
    funext w
    have hd1 : residualFun w k
        = dist ((Apt k) (pad12 w)) ((Bpt k) (pad12 w)) - w 6 :=
      congrFun (HessSeam.residualFun_eq_dist_sub k) w
    have hd2 : dist ((Apt k) (pad12 w)) ((Bpt k) (pad12 w)) = Real.sqrt (HessSeam.SRad k w) :=
      congrFun (HessSeam.dist_Apt_Bpt_eq_sqrt_SRad k) w
    rw [hd1, hd2]
  have hdef : (fun w : Fin 7 → ℝ => Real.sqrt (HessSeam.SRad k w) - w 6)
      = fun w : Fin 7 → ℝ => Real.sqrt (HessSeam.SRad k w) - coord 6 w := rfl
  -- (iii) `coord 6` 的二阶 = 0
  have hsq : secondPartial (fun w : Fin 7 → ℝ =>
        Real.sqrt (HessSeam.SRad k w) - coord 6 w) u i j
      = secondPartial (fun w : Fin 7 → ℝ => Real.sqrt (HessSeam.SRad k w)) u i j := by
    rw [HessSeam.secondPartial_sub_any u
      (DeltaAny.hasFDerivAt_fderiv_sqrtSRad_any k u hWa hWb hW6 hWp hpos)
      (TowerBC.hasFDerivAt_fderiv_clm_any (coord 6) u)
      (eventually_diff_sqrtSRad_any k u hWa hWb hW6 hWp hpos)
      (Filter.Eventually.of_forall fun z =>
        (ContinuousLinearMap.hasFDerivAt (coord 6) (x := z)).differentiableAt) i j,
      secondPartial_clm_any (coord 6) u i j, sub_zero]
  -- (iv) 链式闭式
  have hU : secondPartial (fun w : Fin 7 → ℝ => Real.sqrt (HessSeam.SRad k w)) u i j
      = 1 / (2 * Real.sqrt (HessSeam.SRad k u)) * secondPartial (HessSeam.SRad k) u i j
        + (-2) * (1 / (2 * Real.sqrt (HessSeam.SRad k u)))
            * ((2 * Real.sqrt (HessSeam.SRad k u)) * (2 * Real.sqrt (HessSeam.SRad k u)))⁻¹
            * (fderiv ℝ (HessSeam.SRad k) u) (Pi.single j 1)
            * (fderiv ℝ (HessSeam.SRad k) u) (Pi.single i 1) :=
    DeltaAny.secondPartial_sqrtSRad_any k u hWa hWb hW6 hWp hpos i j
  -- (vi) 末步：**证成的定理**（不再是前提）
  rw [hleft, hclm, hfun, hdef, hsq, hU]
  exact hgapProved k i j u hWa hWb hW6 hWp hpos

end HgapKernel

end N11Formalization
