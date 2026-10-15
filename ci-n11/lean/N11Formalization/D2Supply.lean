/-
  d2-supply (R266 · T4) —— **球形式 `hd2x` / `hd2y` 供给件**（`lean/**` 只读；本件为落根候选）

## 目标

把 `TowerBC.d2xIvBox_mem`（**15 前提**）/ `TowerBC.d2yIvBox_mem`（**17 前提**）在
`Q := HessSeam.Q7`、`z := first7 x`、`x ∈ closedBall certCR rhoCertR` 处**喂满**，产出
`N11Formalization.HJAssembly.hJ_of_hcore_and_d2` 两个显式洞的形状：

```
-- ✅ 已证（本件）：上游件 d2xIvBox_mem / d2yIvBox_mem 的 15 / 17 条前提**全部喂满**
d2xIvBox_mem_ball : (TowerBC.d2xIvBox Q7C k i j).Mem (secondPartial (DeltaX k) (first7 x) i j)
d2yIvBox_mem_ball : 同形（DeltaY / d2yIvBox）
-- ⚠ **桥（未付，显式假设）**：d2xIvBox Q7C 与 d2xIv **不是** defeq（见下）
hBridgeX : ∀ k i j, TowerBC.d2xIvBox Q7C k i j = d2xIv k i j        （hBridgeY 同）
-- ✅ 已证（给定桥）：消费者形
d2xIv_mem_ball_of_bridge hBridgeX : (d2xIv k i j).Mem (secondPartial (DeltaX k) (first7 x) i j)
d2yIv_mem_ball_of_bridge hBridgeY : 同形
```

⚠ **卡上"`d2xIvBox Q7C` 与 `d2xIv` 逐支同形 ⇒ defeq"为假（实测）**：两者**定义树不同** ——
盒侧走 `TowerBC.ring2Box Q7C`（`rho2IvBox Q` / `cosTotLag (thetaInterval (ndAngleBox (pad12Box Q)))` …），
数值表侧走 `D2Leaves.ring2`（`rho2Iv` / `cosTIv = cosTotLag (thetaInterval (angleVecInterval cCert))` …）。
桥需要 **L1** `pad12Box Q7C = cCert` ＋ **L2** 逐叶「区间算术值 = 数值表字面量」；
L2 与 T2 报告 §⑤.4 判死的是同一堵墙（`ring2`/`arc2` 全库无 `_lo/_hi` 叶件）。
`#reduce` 在**两侧**都报 `maxRecDepth`（`P3_eval.out.txt`）⇒ 选格器也读不出值。
**口径方向**：盒侧的 `_mem` 只给**包含** ⇒ 反推更窄的 `d2xIv` **不可能**免费拿到。
详见同目录 `T4-REPORT.md` §⑤.2。**本件不声称桥为真，也不声称为假。**

## 前提逐条喂料（**每条都 `#check` 过真名**，读数另存 `log-P1_check.out.txt` / `log-P2*`）

| 前提 | 喂料件（真名，本件 `#check` 过） |
|---|---|
| `hz` | `Q7Transfer.hz_of_mem_closedBall hx` |
| `hW6` | `Q7Transfer.Q7_wkBoxQ_pos 6` |
| `hWa` / `hWb` | `Q7Transfer.Q7_wkBoxQ_pos (resSlot k)` / `(… + 1)` |
| `hWp` / `hVp` | `Q7Transfer.Q7_WpIvBoxQ_pos` / `Q7Transfer.Q7_WpIvBoxQ_valid` |
| `hUh`(x) | `DeltaAny.hasFDerivAt_fderiv_UvecC0_any (resSlot k) (first7 x) (pb_hWa k hx) (pb_hWb k hx)` |
| `hUh`(y) | `DeltaAny.hasFDerivAt_fderiv_UvecC1_any …`（同参） |
| `hH0`/`hH1` | 本件 `hub0xF_any` / `hub1xF_any`（y 支 `hub0yF_any` / `hub1yF_any`） |
| `hUd` | 本件 `uvecDiff0_any`（`TowerBC.uvec_evdiff` ＋ 邻域正性升格） |
| `hHd0`/`hHd1` | `TowerBC.eventually_diff_hub0xF` / `_hub1xF`（y 支 `_hub0yF` / `_hub1yF`） |
| `hU2` | 本件 `uvecSec0_any`（`TowerBC.secondPartial_Uvec_coord_any` 的逐字实例） |
| `hWx` / `hWxd` | 本件 `wPointxF_any` / `wPointxFd_any` |
| `hC6` | `TowerBC.hasFDerivAt_fderiv_ringC0_any 6 (first7 x) (pb_Wfun_pos 6 hx)`（y 支 `_ringC1_any`） |
| `hWy` | `TowerBC.hasFDerivAt_fderiv_wyF_any (first7 x) (pb_hWp hx)` |
| `hWyd` | 本件 `wPointyFd_any`（`wpF_eq_sqrt` ＋ `Real.hasDerivAt_sqrt` ＋ `hasFDerivAt_Wpf_any`） |
| `hC6d` | 本件 `ringC0d_any` / `ringC1d_any`（`hasFDerivAt_ringCenter{0,1}_any` ＋ 邻域正性） |

**每条都用上**：`k = 4` 走 `_wF` 支（只用 `hz/hW6/hWx/hC6/hWxd/hC6d`），`k ≠ 4` 走
`Uvec` 支（用 `hz/hWa/hWb/hUh/hH/hUd/hU2`）；两条路的前提**全部**给出（不被用的也给）。

## 三条实现要点（都是**实测**出来的，不是猜的）

1. **`Q7C` 必须是 `def`**：`abbrev` 在 `d2xIvBox Q7C` 与 `d2xIv` 的 defeq 上**不 unfold** ⇒
   两条 `simpa only [d2xIv, d2xIvBox]` 会红。改 `def` 后绿（读数链见 `log-d2_supply.out.txt` 历史）。
2. **`hub` 四族的常值桥**：`hasFDerivAt_fderiv_of_eq_const_any` 的 `h` 位是**完整函数等式**，
   直接喂 `fun z => congrFun hub0xF_eq z` 会红（elab 侧不把 `∀` 当 `=`）；
   正解 = `funext fun z => congrFun … z`（或用 `hasFDerivAt_fderiv_of_eq_clm_any x hub0xF_eq`）。
3. **`hUd`/`hC6d` 的邻域正性**：`hasFDerivAt_ringCenter{0,1}_any` 要**变点处**的 `Wfun ≠ 0`，
   不是只有 `z` 处 ⇒ 先 `Wfun_pos_eventually`（`hasFDerivAt_Wfun` 连续）升成邻域，再用 `.mono` 逐点降。

## 口径

无 `sorry`/`admit`/自定义 `axiom`/`native_decide`/`Lean.ofReduceBool`；本件**不打印**
（判据 = stdout/stderr **0 字节**）；公理画像用另置副本 `d2_supply_axioms.lean`。
**本件不引入任何新假设**：全部材料来自 `hx` 或锥内无条件件。
-/
import N11Formalization.TowerBC_N_anyx_layer1
import N11Formalization.DeltaAny
import N11Formalization.PremiseBundle
import N11Formalization.Q7WkBoxTransfer
import N11Formalization.HessSeamBall
import N11Formalization.D2Leaves
import N11Formalization.BoxRstar
import N11Formalization.ResidualDerivJT
import N11Formalization.ResidualDerivJTHess
import N11Formalization.TCSystem
import N11Formalization.Definitions
set_option maxHeartbeats 1600000

noncomputable section

namespace N11Formalization.D2Supply

open N11Formalization
open N11Formalization.TowerBC
open N11Formalization.HessSeam

/-- `Q7`（真全名 `N11Formalization.HessSeam.Q7`）的别名。
⚠ **`Q7` 不在 `Q7Transfer` namespace 内**（那只是模块里开的 `namespace N11Formalization.Q7Transfer`）
—— 本工程「模块名 ≠ 命名空间」的老坑，读数见 `log-P1_check.out.txt`。
⚠ **必须 `def` 不是 `abbrev`**：`d2xIvBox Q7C` 与 `d2xIv` 的 defeq 要靠它 unfold。 -/
def Q7C : Fin 7 → RatInterval := HessSeam.Q7

/-! ## 0. `hub` 四族横/纵坐标（`hH0`/`hH1`；y 支备用）与 `wPoint` 横坐标（`hWx`/`hWxd`） -/

/-- `hub0` 横坐标：点恒等式 `hub0xF_eq`（**裸顶层名**）＋ `hasFDerivAt_fderiv_of_eq_clm_any`。 -/
theorem hub0xF_any (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ (fun y : Fin 7 → ℝ =>
        (hub0 (pad12 y)).ofLp 0) y) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) x := by
  have h : (fun y : Fin 7 → ℝ => (hub0 (pad12 y)).ofLp 0)
      = fun z : Fin 7 → ℝ => coord 4 z := hub0xF_eq
  simpa using hasFDerivAt_fderiv_of_eq_clm_any x h

/-- `hub1` 横坐标。 -/
theorem hub1xF_any (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ (fun y : Fin 7 → ℝ =>
        (hub1 (pad12 y)).ofLp 0) y) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) x := by
  have h : (fun y : Fin 7 → ℝ => (hub1 (pad12 y)).ofLp 0)
      = fun z : Fin 7 → ℝ => coord 5 z := hub1xF_eq
  simpa using hasFDerivAt_fderiv_of_eq_clm_any x h

/-- `hub0` 纵坐标（恒 `0`）。 -/
theorem hub0yF_any (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ (fun y : Fin 7 → ℝ =>
        (hub0 (pad12 y)).ofLp 1) y) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) x :=
  hasFDerivAt_fderiv_of_eq_const_any (funext fun z => congrFun hub0yF_eq z) x

/-- `hub1` 纵坐标（恒 `0`）。 -/
theorem hub1yF_any (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ (fun y : Fin 7 → ℝ =>
        (hub1 (pad12 y)).ofLp 1) y) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) x :=
  hasFDerivAt_fderiv_of_eq_const_any (funext fun z => congrFun hub1yF_eq z) x

/-- `wPoint.x = (1/2)(z₄+z₅)`（仿射；CLM 形 `(1/2) • (coord 4 + coord 5)`）。 -/
theorem wPointxF_eq_any :
    (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0)
      = fun z => ((1 / 2 : ℝ) • (coord 4 + coord 5)) z := by
  funext z
  rw [wPoint_coord0, pad12_four, pad12_five]
  simp only [smul_apply, add_apply, smul_eq_mul]
  ring_nf
  simp [coord]

/-- `hWx`：`wPoint.x` 仿射 ⇒ 二阶 CLM `0`。 -/
theorem wPointxF_any (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ (fun y : Fin 7 → ℝ =>
        (wPoint (pad12 y)).ofLp 0) y) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) x :=
  hasFDerivAt_fderiv_of_eq_clm_any x wPointxF_eq_any

/-- `hWxd`。 -/
theorem wPointxFd_any (x : Fin 7 → ℝ) :
    ∀ᶠ w in nhds x, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 0) w := by
  rw [wPointxF_eq_any]
  exact Filter.Eventually.of_forall fun w =>
    (ContinuousLinearMap.hasFDerivAt
      (f := (1 / 2 : ℝ) • (coord 4 + coord 5)) (x := w)).differentiableAt

/-! ## 1. 邻域正性升格 + `Uvec` 支（`hUd` / `hU2`） -/

/-- `0 < Wfun s z` ⇒ 邻域内正（`hasFDerivAt_Wfun` 连续）。 -/
theorem Wfun_pos_eventually {s : Fin 9} {z : Fin 7 → ℝ} (h : 0 < Wfun s z) :
    ∀ᶠ w in nhds z, 0 < Wfun s w :=
  (hasFDerivAt_Wfun s z).continuousAt.eventually (eventually_gt_nhds h)

/-- `hUd`（x 支）：`TowerBC.uvec_evdiff`（三块 `_any` 微分）。 -/
theorem uvecDiff0_any {z : Fin 7 → ℝ} (s : Fin 9) (hWs : 0 < Wfun s z)
    (hWs1 : 0 < Wfun (s + 1) z) :
    ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp 0) w := by
  have hd1 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ =>
      rhoK (pad12 w) s * Real.cos (thetaOf (angleVec (pad12 w)) s)) w :=
    (Wfun_pos_eventually hWs).mono fun w hw =>
      (hasFDerivAt_ringCenter0_any s w (ne_of_gt hw)).differentiableAt
  have hd2 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ =>
      rhoK (pad12 w) (s + 1) * Real.cos (thetaOf (angleVec (pad12 w)) (s + 1))) w :=
    (Wfun_pos_eventually hWs1).mono fun w hw =>
      (hasFDerivAt_ringCenter0_any (s + 1) w (ne_of_gt hw)).differentiableAt
  have h1 : (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp 0)
      = fun w : Fin 7 → ℝ =>
        rhoK (pad12 w) s * Real.cos (thetaOf (angleVec (pad12 w)) s) := by
    funext w
    exact ringCenter_coord0 (pad12 w) s
  have h2 : (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp 0)
      = fun w : Fin 7 → ℝ =>
        rhoK (pad12 w) (s + 1) * Real.cos (thetaOf (angleVec (pad12 w)) (s + 1)) := by
    funext w
    exact ringCenter_coord0 (pad12 w) (s + 1)
  simpa only [h1, h2] using uvec_evdiff (s := s) (c := 0) (z := z) hd1 hd2
    (Filter.Eventually.of_forall fun w => (hasFDerivAt_arcC0_any s w).differentiableAt)

/-- `hUd`（y 支）。 -/
theorem uvecDiff1_any {z : Fin 7 → ℝ} (s : Fin 9) (hWs : 0 < Wfun s z)
    (hWs1 : 0 < Wfun (s + 1) z) :
    ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp 1) w := by
  have hd1 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ =>
      rhoK (pad12 w) s * Real.sin (thetaOf (angleVec (pad12 w)) s)) w :=
    (Wfun_pos_eventually hWs).mono fun w hw =>
      (hasFDerivAt_ringCenter1_any s w (ne_of_gt hw)).differentiableAt
  have hd2 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ =>
      rhoK (pad12 w) (s + 1) * Real.sin (thetaOf (angleVec (pad12 w)) (s + 1))) w :=
    (Wfun_pos_eventually hWs1).mono fun w hw =>
      (hasFDerivAt_ringCenter1_any (s + 1) w (ne_of_gt hw)).differentiableAt
  have h1 : (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp 1)
      = fun w : Fin 7 → ℝ =>
        rhoK (pad12 w) s * Real.sin (thetaOf (angleVec (pad12 w)) s) := by
    funext w
    exact ringCenter_coord1 (pad12 w) s
  have h2 : (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp 1)
      = fun w : Fin 7 → ℝ =>
        rhoK (pad12 w) (s + 1) * Real.sin (thetaOf (angleVec (pad12 w)) (s + 1)) := by
    funext w
    exact ringCenter_coord1 (pad12 w) (s + 1)
  simpa only [h1, h2] using uvec_evdiff (s := s) (c := 1) (z := z) hd1 hd2
    (Filter.Eventually.of_forall fun w => (hasFDerivAt_arcC1_any s w).differentiableAt)

/-- `hU2`（x 支）：`TowerBC.secondPartial_Uvec_coord_any` 的**逐字实例**（9 前提全供）。 -/
theorem uvecSec0_any {z : Fin 7 → ℝ} (s : Fin 9) (hWs : 0 < Wfun s z)
    (hWs1 : 0 < Wfun (s + 1) z) :
    ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp 0) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp 0) z i j
        + secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp 0) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp 0) z i j := fun i j =>
  secondPartial_Uvec_coord_any s 0 z i j
    (hasFDerivAt_fderiv_ringC0_any s z hWs)
    (hasFDerivAt_fderiv_ringC0_any (s + 1) z hWs1)
    (hasFDerivAt_fderiv_ArcC_any s 0 z)
    (by
      have hd1 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ =>
          rhoK (pad12 w) s * Real.cos (thetaOf (angleVec (pad12 w)) s)) w :=
        (Wfun_pos_eventually hWs).mono fun w hw =>
          (hasFDerivAt_ringCenter0_any s w (ne_of_gt hw)).differentiableAt
      have h1 : (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp 0)
          = fun w : Fin 7 → ℝ =>
            rhoK (pad12 w) s * Real.cos (thetaOf (angleVec (pad12 w)) s) := by
        funext w
        exact ringCenter_coord0 (pad12 w) s
      simpa only [h1] using hd1)
    (by
      have hd2 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ =>
          rhoK (pad12 w) (s + 1) * Real.cos (thetaOf (angleVec (pad12 w)) (s + 1))) w :=
        (Wfun_pos_eventually hWs1).mono fun w hw =>
          (hasFDerivAt_ringCenter0_any (s + 1) w (ne_of_gt hw)).differentiableAt
      have h2 : (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp 0)
          = fun w : Fin 7 → ℝ =>
            rhoK (pad12 w) (s + 1) * Real.cos (thetaOf (angleVec (pad12 w)) (s + 1)) := by
        funext w
        exact ringCenter_coord0 (pad12 w) (s + 1)
      simpa only [h2] using hd2)
    (Filter.Eventually.of_forall fun w => (hasFDerivAt_arcC0_any s w).differentiableAt)

/-- `hU2`（y 支）。 -/
theorem uvecSec1_any {z : Fin 7 → ℝ} (s : Fin 9) (hWs : 0 < Wfun s z)
    (hWs1 : 0 < Wfun (s + 1) z) :
    ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp 1) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp 1) z i j
        + secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp 1) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp 1) z i j := fun i j =>
  secondPartial_Uvec_coord_any s 1 z i j
    (hasFDerivAt_fderiv_ringC1_any s z hWs)
    (hasFDerivAt_fderiv_ringC1_any (s + 1) z hWs1)
    (hasFDerivAt_fderiv_ArcC_any s 1 z)
    (by
      have hd1 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ =>
          rhoK (pad12 w) s * Real.sin (thetaOf (angleVec (pad12 w)) s)) w :=
        (Wfun_pos_eventually hWs).mono fun w hw =>
          (hasFDerivAt_ringCenter1_any s w (ne_of_gt hw)).differentiableAt
      have h1 : (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp 1)
          = fun w : Fin 7 → ℝ =>
            rhoK (pad12 w) s * Real.sin (thetaOf (angleVec (pad12 w)) s) := by
        funext w
        exact ringCenter_coord1 (pad12 w) s
      simpa only [h1] using hd1)
    (by
      have hd2 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ =>
          rhoK (pad12 w) (s + 1) * Real.sin (thetaOf (angleVec (pad12 w)) (s + 1))) w :=
        (Wfun_pos_eventually hWs1).mono fun w hw =>
          (hasFDerivAt_ringCenter1_any (s + 1) w (ne_of_gt hw)).differentiableAt
      have h2 : (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp 1)
          = fun w : Fin 7 → ℝ =>
            rhoK (pad12 w) (s + 1) * Real.sin (thetaOf (angleVec (pad12 w)) (s + 1)) := by
        funext w
        exact ringCenter_coord1 (pad12 w) (s + 1)
      simpa only [h2] using hd2)
    (Filter.Eventually.of_forall fun w => (hasFDerivAt_arcC1_any s w).differentiableAt)

/-! ## 2. `hC6d`（`ringCenter` 两支）与 `hWyd`（`√Wpf`） -/

/-- `hC6d`（x 支）。 -/
theorem ringC0d_any {z : Fin 7 → ℝ} {k : Fin 9} (hW : 0 < Wfun k z) :
    ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) k).ofLp 0) w := by
  have hd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ =>
      rhoK (pad12 w) k * Real.cos (thetaOf (angleVec (pad12 w)) k)) w :=
    (Wfun_pos_eventually hW).mono fun w hw =>
      (hasFDerivAt_ringCenter0_any k w (ne_of_gt hw)).differentiableAt
  have h1 : (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) k).ofLp 0)
      = fun w : Fin 7 → ℝ =>
        rhoK (pad12 w) k * Real.cos (thetaOf (angleVec (pad12 w)) k) := by
    funext w
    exact ringCenter_coord0 (pad12 w) k
  simpa only [h1] using hd

/-- `hC6d`（y 支）。 -/
theorem ringC1d_any {z : Fin 7 → ℝ} {k : Fin 9} (hW : 0 < Wfun k z) :
    ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) k).ofLp 1) w := by
  have hd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ =>
      rhoK (pad12 w) k * Real.sin (thetaOf (angleVec (pad12 w)) k)) w :=
    (Wfun_pos_eventually hW).mono fun w hw =>
      (hasFDerivAt_ringCenter1_any k w (ne_of_gt hw)).differentiableAt
  have h1 : (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) k).ofLp 1)
      = fun w : Fin 7 → ℝ =>
        rhoK (pad12 w) k * Real.sin (thetaOf (angleVec (pad12 w)) k) := by
    funext w
    exact ringCenter_coord1 (pad12 w) k
  simpa only [h1] using hd

/-- `0 < Wpf z` ⇒ 邻域内正（`hasFDerivAt_Wpf_any` 连续）。 -/
theorem Wpf_pos_eventually {z : Fin 7 → ℝ} (h : 0 < Wpf z) :
    ∀ᶠ w in nhds z, 0 < Wpf w :=
  (hasFDerivAt_Wpf_any z).continuousAt.eventually (eventually_gt_nhds h)

/-- `hWyd`：`wPoint.y = √Wpf`（`wpF_eq_sqrt`）＋ `√` 的链式（`Real.hasDerivAt_sqrt` ×
`hasFDerivAt_Wpf_any`；**要 `Wpf` 自身的导数**，不是 `hasFDerivAt_fderiv_Wpf_any`）。 -/
theorem wPointyFd_any {z : Fin 7 → ℝ} (hWp : 0 < Wpf z) :
    ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 1) w := by
  rw [wpF_eq_sqrt]
  exact (Wpf_pos_eventually hWp).mono fun w hw =>
    ((Real.hasDerivAt_sqrt (ne_of_gt hw)).differentiableAt.comp w
      (hasFDerivAt_Wpf_any w).differentiableAt)

/-! ## 3. **两条球形式主定理**（15 / 17 前提全喂） -/

/-- **`hd2x`（上游件逐字结论形）**：`TowerBC.d2xIvBox_mem` 的 **15** 条前提全喂。 -/
theorem d2xIvBox_mem_ball (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (TowerBC.d2xIvBox Q7C k i j).Mem (secondPartial (DeltaX k) (first7 x) i j) := by
  have hW6 : (0 : ℚ) < (TowerBC.wkBoxQ Q7C (6 : Fin 9)).lo := Q7Transfer.Q7_wkBoxQ_pos (6 : Fin 9)
  have hWa : (0 : ℚ) < (TowerBC.wkBoxQ Q7C (resSlot k)).lo :=
    Q7Transfer.Q7_wkBoxQ_pos (resSlot k)
  have hWb : (0 : ℚ) < (TowerBC.wkBoxQ Q7C ((resSlot k) + 1)).lo :=
    Q7Transfer.Q7_wkBoxQ_pos ((resSlot k) + 1)
  exact @TowerBC.d2xIvBox_mem Q7C k i j (first7 x)
    (Q7Transfer.hz_of_mem_closedBall hx) hW6 hWa hWb
    (DeltaAny.L2UvecC0At (first7 x) (resSlot k))
    (DeltaAny.hasFDerivAt_fderiv_UvecC0_any (resSlot k) (first7 x)
      (PremiseBundle.pb_hWa k hx) (PremiseBundle.pb_hWb k hx))
    (hub0xF_any (first7 x)) (hub1xF_any (first7 x))
    (uvecDiff0_any (resSlot k) (PremiseBundle.pb_hWa k hx) (PremiseBundle.pb_hWb k hx))
    (TowerBC.eventually_diff_hub0xF (first7 x))
    (TowerBC.eventually_diff_hub1xF (first7 x))
    (uvecSec0_any (resSlot k) (PremiseBundle.pb_hWa k hx) (PremiseBundle.pb_hWb k hx))
    (wPointxF_any (first7 x))
    (TowerBC.hasFDerivAt_fderiv_ringC0_any (6 : Fin 9) (first7 x)
      (PremiseBundle.pb_Wfun_pos hx (6 : Fin 9)))
    (wPointxFd_any (first7 x))
    (ringC0d_any (PremiseBundle.pb_Wfun_pos hx (6 : Fin 9)))

/-! ### ⚠ 桥（`d2xIvBox Q7C` → `d2xIv`）：**未付**（如实登记，见 `T4-REPORT.md` §⑤）

`d2xIvBox Q7C` 与 `d2xIv` **不是** defeq：前者走 `ring2Box Q7C`（区间树 `rho2IvBox Q` /
`cosTotLag (thetaInterval (ndAngleBox (pad12Box Q)))` …），后者走 `ring2`（数值表 `rho2Iv` /
`cosTIv = cosTotLag (thetaInterval (angleVecInterval cCert))` …）。
逐项要的是 `pad12Box Q7C = cCert`（L1）＋ 逐叶「区间算术值 = 数值表字面量」（L2，
`ring2`/`arc2` **没有** `_lo/_hi` 叶件，同 T2 §⑤.4 的实测）。
故本件**不写** `d2xIvBox Q7C = d2xIv` 的 `theorem`，改把它写成**显式假设**（下游 Lead 用）：

```
-- 供给（本件已证）
d2xIvBox_mem_ball : … (TowerBC.d2xIvBox Q7C k i j).Mem (secondPartial (DeltaX k) (first7 x) i j)
-- 桥（**假设**，未付）
hBridgeX : ∀ k i j, TowerBC.d2xIvBox Q7C k i j = d2xIv k i j
-- ⇒ 消费者形
d2xIv_mem_ball_of_bridge hBridgeX : (d2xIv k i j).Mem (secondPartial (DeltaX k) (first7 x) i j)
```

**注意口径方向**（这决定了桥能不能免费拿）：区间算术 `ring2Box Q7C` 对**同一**函数做的是
**包含**（`_mem` 定理给出 `Mem`），它**不可能**证成 `Mem` 的**反方向**（更窄盒 ⇒ 更强的 `Mem` 不成立）；
故 `d2xIv` 侧只能由「表的**值**相等」（L1＋L2）或「`d2xIv` 是更宽的盒」拿到，两者都需要数值叶。 -/

/-- **消费者形（`d2xIv` 侧）＝ 本件已证的盒形 ＋ 一条显式桥假设**（不藏着）。 -/
theorem d2xIv_mem_ball_of_bridge
    (hBridgeX : ∀ (k : Fin 5) (i j : Fin 7), TowerBC.d2xIvBox Q7C k i j = d2xIv k i j)
    (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (d2xIv k i j).Mem (secondPartial (DeltaX k) (first7 x) i j) := by
  rw [← hBridgeX k i j]
  exact d2xIvBox_mem_ball k i j hx

/-- **`hd2y`（上游件逐字结论形）**：`TowerBC.d2yIvBox_mem` 的 **17** 条前提全喂。 -/
theorem d2yIvBox_mem_ball (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (TowerBC.d2yIvBox Q7C k i j).Mem (secondPartial (DeltaY k) (first7 x) i j) := by
  have hW6 : (0 : ℚ) < (TowerBC.wkBoxQ Q7C (6 : Fin 9)).lo := Q7Transfer.Q7_wkBoxQ_pos (6 : Fin 9)
  have hWp : (0 : ℚ) < (TowerBC.WpIvBoxQ Q7C).lo := Q7Transfer.Q7_WpIvBoxQ_pos
  have hVp : (TowerBC.WpIvBoxQ Q7C).Valid := Q7Transfer.Q7_WpIvBoxQ_valid
  have hWa : (0 : ℚ) < (TowerBC.wkBoxQ Q7C (resSlot k)).lo :=
    Q7Transfer.Q7_wkBoxQ_pos (resSlot k)
  have hWb : (0 : ℚ) < (TowerBC.wkBoxQ Q7C ((resSlot k) + 1)).lo :=
    Q7Transfer.Q7_wkBoxQ_pos ((resSlot k) + 1)
  exact @TowerBC.d2yIvBox_mem Q7C k i j (first7 x)
    (Q7Transfer.hz_of_mem_closedBall hx) hW6 hWp hVp hWa hWb
    (DeltaAny.L2UvecC1At (first7 x) (resSlot k))
    (DeltaAny.hasFDerivAt_fderiv_UvecC1_any (resSlot k) (first7 x)
      (PremiseBundle.pb_hWa k hx) (PremiseBundle.pb_hWb k hx))
    (hub0yF_any (first7 x)) (hub1yF_any (first7 x))
    (uvecDiff1_any (resSlot k) (PremiseBundle.pb_hWa k hx) (PremiseBundle.pb_hWb k hx))
    (TowerBC.eventually_diff_hub0yF (first7 x))
    (TowerBC.eventually_diff_hub1yF (first7 x))
    (uvecSec1_any (resSlot k) (PremiseBundle.pb_hWa k hx) (PremiseBundle.pb_hWb k hx))
    (TowerBC.hasFDerivAt_fderiv_wyF_any (first7 x) (PremiseBundle.pb_hWp hx))
    (TowerBC.hasFDerivAt_fderiv_ringC1_any (6 : Fin 9) (first7 x)
      (PremiseBundle.pb_Wfun_pos hx (6 : Fin 9)))
    (wPointyFd_any (PremiseBundle.pb_hWp hx))
    (ringC1d_any (PremiseBundle.pb_Wfun_pos hx (6 : Fin 9)))

/-- **消费者形（`d2yIv` 侧）＝ 盒形 ＋ 一条显式桥假设**（同 x 支，桥**未付**）。 -/
theorem d2yIv_mem_ball_of_bridge
    (hBridgeY : ∀ (k : Fin 5) (i j : Fin 7), TowerBC.d2yIvBox Q7C k i j = d2yIv k i j)
    (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (d2yIv k i j).Mem (secondPartial (DeltaY k) (first7 x) i j) := by
  rw [← hBridgeY k i j]
  exact d2yIvBox_mem_ball k i j hx

end N11Formalization.D2Supply
