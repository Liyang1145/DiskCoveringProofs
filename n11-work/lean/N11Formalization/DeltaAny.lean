/-
# `Δ` 链的**一般点升格**：`HessSeamHL7.lean` 的球心版（点 `u0`）→ 任意点 `x : Fin 7 → ℝ`

**约定（本件全程）**：`x : Fin 7 → ℝ`（**不是** `Fin 12`）。凡需要 `Fin 12` 侧的量
（`Apt`/`Bpt`/`dUxReal`/`ringCenter`/`Uvec`）一律经 `pad12 x` 读出 ✓。

**本件供给的靶**：
* (1) `eventually_diff_DeltaX_any` / `_DeltaY_any` / `_DXsq_any` / `_DYsq_any` / `_SRad_any`
* (2) `hasFDerivAt_DeltaX_any` / `_DeltaY_any`（由 (1) `.self_of_nhds.hasFDerivAt`）
* (3) `hasFDerivAt_fderiv_DeltaX_any` / `_DeltaY_any`（一般点的"二阶 CLM"事实）
* (4) `SRad2_any`（= `HessSeamHL7.SRad2_single` 的 `u0 → x` 版）
* (5) `sqrtSRad2_any`（= `HessSeamHL7.sqrtSRad2_single` 的 `u0 → x` 版，`L2SqrtSRad_any` 显式化）
* (6) `secondPartial_sqrtSRad_any`（右端 = `distHessRealBox (pad12 x)`
  ＋ `DeltaX_u0`-型原子替换；**这是通往 `(6) 的最终靶**的那一条）
* 盒桥 `secondPartial_DeltaX_first7` / `secondPartial_DeltaY_first7`

**前提口径**：正性/非退化一律**显式参数**。球心版把 `0 < (WkIv j).lo`（区间下界）当参数；
本件取**实侧**点形态 `0 < Wfun j x` / `0 < Wpf x`（更一般；由 `WkIv_mem` + `mem_lo_le` 供给 ✓）。

⚠ **`Fin` 字面量坑（本轮实测）**：`DeltaX12 0`（裸 `0`）**不归约** ✗；写 `DeltaX12 (0 : Fin 5)`
才 `rfl` ✓（`Advance.not_advance` 的 `Fin` 字面量规避法）。

**禁**：`sorry` / `admit` / 自定义 `axiom` / `native_decide`。
-/

import N11Formalization.HessSeamHL7
import N11Formalization.HessSeamAny
import N11Formalization.TowerBC_N_anyx_layer1
import N11Formalization.D2Leaves
import N11Formalization.D2IvBoxMem
import N11Formalization.F1.BallD35C4
import N11Formalization.F1.BallD35C2
import N11Formalization.F1.BallD35C9
import N11Formalization.F1.BallD35Hrad
import N11Formalization.HessBoxMem

noncomputable section

set_option maxHeartbeats 4000000

set_option linter.unusedVariables false

namespace N11Formalization

namespace DeltaAny

open RatInterval

/-! ## 0. 命名叶（`F` 形态）与二阶 CLM 载体 -/

/-- `Δx_k` 的**载体叶**（`k = 0..3` 走 `Uvec`，`k = 4` 走 `wPoint`）。
⚠ `@[reducible]` **必需**：否则 `fderiv ℝ (PtCF k)` 在类型里不展开 ✗（本文件的实际教训）。 -/
@[reducible] def PtCF (k : Fin 5) : (Fin 7 → ℝ) → ℝ :=
  match k with
  | 0 => fun z : Fin 7 → ℝ => (Uvec (pad12 z) 1).ofLp 0
  | 1 => fun z : Fin 7 → ℝ => (Uvec (pad12 z) 2).ofLp 0
  | 2 => fun z : Fin 7 → ℝ => (Uvec (pad12 z) 3).ofLp 0
  | 3 => fun z : Fin 7 → ℝ => (Uvec (pad12 z) 8).ofLp 0
  | 4 => fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0

/-- `Δy_k` 的**载体叶**。 -/
@[reducible] def PtCF1 (k : Fin 5) : (Fin 7 → ℝ) → ℝ :=
  match k with
  | 0 => fun z : Fin 7 → ℝ => (Uvec (pad12 z) 1).ofLp 1
  | 1 => fun z : Fin 7 → ℝ => (Uvec (pad12 z) 2).ofLp 1
  | 2 => fun z : Fin 7 → ℝ => (Uvec (pad12 z) 3).ofLp 1
  | 3 => fun z : Fin 7 → ℝ => (Uvec (pad12 z) 8).ofLp 1
  | 4 => fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1

/-- `Δx_k` 的**驻点叶**（`hub0`/`hub1`/`ringCenter 6`）。 -/
@[reducible] def HubCF (k : Fin 5) : (Fin 7 → ℝ) → ℝ :=
  match k with
  | 0 => fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0
  | 1 => fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0
  | 2 => fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0
  | 3 => fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0
  | 4 => fun z : Fin 7 → ℝ => (ringCenter (pad12 z) 6).ofLp 0

/-- `Δy_k` 的**驻点叶**。 -/
@[reducible] def HubCF1 (k : Fin 5) : (Fin 7 → ℝ) → ℝ :=
  match k with
  | 0 => fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1
  | 1 => fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1
  | 2 => fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1
  | 3 => fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1
  | 4 => fun z : Fin 7 → ℝ => (ringCenter (pad12 z) 6).ofLp 1

/-- `Δx_k = (Apt k ∘ pad12).ofLp 0 − (Bpt k ∘ pad12).ofLp 0`（= `DeltaX k`，`rfl` ✓）。 -/
@[reducible] def DeltaX12 (k : Fin 5) : (Fin 7 → ℝ) → ℝ :=
  fun z => ((Apt k) (pad12 z)).ofLp 0 - ((Bpt k) (pad12 z)).ofLp 0

/-- `Δy_k`。 -/
@[reducible] def DeltaY12 (k : Fin 5) : (Fin 7 → ℝ) → ℝ :=
  fun z => ((Apt k) (pad12 z)).ofLp 1 - ((Bpt k) (pad12 z)).ofLp 1

theorem DeltaX_eq (k : Fin 5) : DeltaX k = DeltaX12 k := rfl

theorem DeltaY_eq (k : Fin 5) : DeltaY k = DeltaY12 k := rfl

theorem DeltaX_comp (k : Fin 5) (y : Fin 7 → ℝ) : DeltaX k y = DeltaX12 k y := rfl

theorem DeltaY_comp (k : Fin 5) (y : Fin 7 → ℝ) : DeltaY k y = DeltaY12 k y := rfl

/-- `Δx_k = 载体叶 − 驻点叶`（**逐支 `rfl`**；`(0 : Fin 5)` 写法必需 ✓）。 -/
theorem DeltaX12_sub (k : Fin 5) : DeltaX12 k = PtCF k - HubCF k := by
  fin_cases k <;> rfl

/-- `Δy_k = 载体叶 − 驻点叶`。 -/
theorem DeltaY12_sub (k : Fin 5) : DeltaY12 k = PtCF1 k - HubCF1 k := by
  fin_cases k <;> rfl

theorem DeltaX_comp_sub (k : Fin 5) (y : Fin 7 → ℝ) : DeltaX k y = PtCF k y - HubCF k y := by
  rw [DeltaX_comp, DeltaX12_sub]
  rfl

theorem DeltaY_comp_sub (k : Fin 5) (y : Fin 7 → ℝ) : DeltaY k y = PtCF1 k y - HubCF1 k y := by
  rw [DeltaY_comp, DeltaY12_sub]
  rfl

/-! ## 1. 叶级一阶可微性（一般点 `x`；前提一律取**实侧正性** `0 < Wfun`/`0 < Wpf`） -/

theorem PtCF_differentiable (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    DifferentiableAt ℝ (PtCF k) x := by
  fin_cases k
  · exact (hasFDerivAt_Uvec0_any 1 x (ne_of_gt hWa) (ne_of_gt hWb)).differentiableAt
  · exact (hasFDerivAt_Uvec0_any 2 x (ne_of_gt hWa) (ne_of_gt hWb)).differentiableAt
  · exact (hasFDerivAt_Uvec0_any 3 x (ne_of_gt hWa) (ne_of_gt hWb)).differentiableAt
  · exact (hasFDerivAt_Uvec0_any 8 x (ne_of_gt hWa) (ne_of_gt hWb)).differentiableAt
  · exact (hasFDerivAt_wPoint_0_any x).differentiableAt

theorem PtCF1_differentiable (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    DifferentiableAt ℝ (PtCF1 k) x := by
  fin_cases k
  · exact (hasFDerivAt_Uvec1_any 1 x (ne_of_gt hWa) (ne_of_gt hWb)).differentiableAt
  · exact (hasFDerivAt_Uvec1_any 2 x (ne_of_gt hWa) (ne_of_gt hWb)).differentiableAt
  · exact (hasFDerivAt_Uvec1_any 3 x (ne_of_gt hWa) (ne_of_gt hWb)).differentiableAt
  · exact (hasFDerivAt_Uvec1_any 8 x (ne_of_gt hWa) (ne_of_gt hWb)).differentiableAt
  · exact (hasFDerivAt_wPoint_1_any x (ne_of_gt hWp)).differentiableAt

theorem HubCF_differentiable (k : Fin 5) (x : Fin 7 → ℝ)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    DifferentiableAt ℝ (HubCF k) x := by
  fin_cases k
  · exact (hasFDerivAt_hub1_0_any x).differentiableAt
  · exact (hasFDerivAt_hub0_0_any x).differentiableAt
  · exact (hasFDerivAt_hub0_0_any x).differentiableAt
  · exact (hasFDerivAt_hub1_0_any x).differentiableAt
  · exact (hasFDerivAt_ringCenter0_any 6 x (ne_of_gt hW6)).differentiableAt

theorem HubCF1_differentiable (k : Fin 5) (x : Fin 7 → ℝ)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    DifferentiableAt ℝ (HubCF1 k) x := by
  fin_cases k
  · exact (hasFDerivAt_hub1_1_any x).differentiableAt
  · exact (hasFDerivAt_hub0_1_any x).differentiableAt
  · exact (hasFDerivAt_hub0_1_any x).differentiableAt
  · exact (hasFDerivAt_hub1_1_any x).differentiableAt
  · exact (hasFDerivAt_ringCenter1_any 6 x (ne_of_gt hW6)).differentiableAt

theorem PtCF_differentiable_forall (k : Fin 5) (z : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) z) (hWb : 0 < Wfun ((resSlot k) + 1) z)
    (hW6 : 0 < Wfun 6 z) (hWp : 0 < Wpf z) :
    DifferentiableAt ℝ (PtCF k) z :=
  PtCF_differentiable k z hWa hWb hW6 hWp

theorem PtCF1_differentiable_forall (k : Fin 5) (z : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) z) (hWb : 0 < Wfun ((resSlot k) + 1) z)
    (hW6 : 0 < Wfun 6 z) (hWp : 0 < Wpf z) :
    DifferentiableAt ℝ (PtCF1 k) z :=
  PtCF1_differentiable k z hWa hWb hW6 hWp

theorem HubCF_differentiable_forall (k : Fin 5) (z : Fin 7 → ℝ)
    (hW6 : 0 < Wfun 6 z) (hWp : 0 < Wpf z) :
    DifferentiableAt ℝ (HubCF k) z :=
  HubCF_differentiable k z hW6 hWp

theorem HubCF1_differentiable_forall (k : Fin 5) (z : Fin 7 → ℝ)
    (hW6 : 0 < Wfun 6 z) (hWp : 0 < Wpf z) :
    DifferentiableAt ℝ (HubCF1 k) z :=
  HubCF1_differentiable k z hW6 hWp

/-! ## 2. (1) `eventually_diff_*_any` -/

theorem eventually_diff_DeltaX_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    ∀ᶠ z in nhds x, DifferentiableAt ℝ (DeltaX k) z := by
  have hWae : ∀ᶠ w in nhds x, 0 < Wfun (resSlot k) w :=
    (hasFDerivAt_Wfun (resSlot k) x).continuousAt.eventually (eventually_gt_nhds hWa)
  have hWbe : ∀ᶠ w in nhds x, 0 < Wfun ((resSlot k) + 1) w :=
    (hasFDerivAt_Wfun ((resSlot k) + 1) x).continuousAt.eventually (eventually_gt_nhds hWb)
  have hW6e : ∀ᶠ w in nhds x, 0 < Wfun 6 w :=
    (hasFDerivAt_Wfun 6 x).continuousAt.eventually (eventually_gt_nhds hW6)
  have hWpe : ∀ᶠ w in nhds x, 0 < Wpf w :=
    (hasFDerivAt_Wpf_any x).continuousAt.eventually (eventually_gt_nhds hWp)
  filter_upwards [hWae, hWbe, hW6e, hWpe] with z ha hb h6 hp
  exact (PtCF_differentiable k z ha hb h6 hp).sub
      (HubCF_differentiable k z h6 hp) |>.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => DeltaX_comp_sub k y)

theorem eventually_diff_DeltaY_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    ∀ᶠ z in nhds x, DifferentiableAt ℝ (DeltaY k) z := by
  have hWae : ∀ᶠ w in nhds x, 0 < Wfun (resSlot k) w :=
    (hasFDerivAt_Wfun (resSlot k) x).continuousAt.eventually (eventually_gt_nhds hWa)
  have hWbe : ∀ᶠ w in nhds x, 0 < Wfun ((resSlot k) + 1) w :=
    (hasFDerivAt_Wfun ((resSlot k) + 1) x).continuousAt.eventually (eventually_gt_nhds hWb)
  have hW6e : ∀ᶠ w in nhds x, 0 < Wfun 6 w :=
    (hasFDerivAt_Wfun 6 x).continuousAt.eventually (eventually_gt_nhds hW6)
  have hWpe : ∀ᶠ w in nhds x, 0 < Wpf w :=
    (hasFDerivAt_Wpf_any x).continuousAt.eventually (eventually_gt_nhds hWp)
  filter_upwards [hWae, hWbe, hW6e, hWpe] with z ha hb h6 hp
  exact (PtCF1_differentiable k z ha hb h6 hp).sub
      (HubCF1_differentiable k z h6 hp) |>.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => DeltaY_comp_sub k y)

theorem eventually_diff_DXsq_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    ∀ᶠ z in nhds x, DifferentiableAt ℝ (fun y : Fin 7 → ℝ => DeltaX k y * DeltaX k y) z :=
  (eventually_diff_DeltaX_any k x hWa hWb hW6 hWp).mono fun _ hz => hz.mul hz

theorem eventually_diff_DYsq_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    ∀ᶠ z in nhds x, DifferentiableAt ℝ (fun y : Fin 7 → ℝ => DeltaY k y * DeltaY k y) z :=
  (eventually_diff_DeltaY_any k x hWa hWb hW6 hWp).mono fun _ hz => hz.mul hz

theorem eventually_diff_SRad_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    ∀ᶠ z in nhds x, DifferentiableAt ℝ (HessSeam.SRad k) z := by
  show ∀ᶠ z in nhds x, DifferentiableAt ℝ
    (fun y : Fin 7 → ℝ => DeltaX k y * DeltaX k y + DeltaY k y * DeltaY k y) z
  filter_upwards [eventually_diff_DeltaX_any k x hWa hWb hW6 hWp,
    eventually_diff_DeltaY_any k x hWa hWb hW6 hWp] with z hzx hzy
  exact (hzx.mul hzx).add (hzy.mul hzy)

/-! ## 3. (2) `hasFDerivAt_DeltaX_any` / `_DeltaY_any` -/

theorem hasFDerivAt_DeltaX_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    HasFDerivAt (DeltaX k) (fderiv ℝ (DeltaX k) x) x :=
  ((eventually_diff_DeltaX_any k x hWa hWb hW6 hWp).self_of_nhds).hasFDerivAt

theorem hasFDerivAt_DeltaY_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    HasFDerivAt (DeltaY k) (fderiv ℝ (DeltaY k) x) x :=
  ((eventually_diff_DeltaY_any k x hWa hWb hW6 hWp).self_of_nhds).hasFDerivAt

/-! ## 4. 二阶叶：`L2UvecC0/C1At`（由 `ringC*_any` ＋ `ArcC_any` ＋ `add/sub_any` 拼） -/

def L2UvecC0At (x : Fin 7 → ℝ) (s : Fin 9) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (TowerBC.L2RingC0At x s + TowerBC.L2RingC0At x (s + 1)) - TowerBC.L2ArcAt x s 0

def L2UvecC1At (x : Fin 7 → ℝ) (s : Fin 9) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (TowerBC.L2RingC1At x s + TowerBC.L2RingC1At x (s + 1)) - TowerBC.L2ArcAt x s 1

set_option maxHeartbeats 2000000 in
theorem hasFDerivAt_fderiv_UvecC0_any (s : Fin 9) (x : Fin 7 → ℝ)
    (hW0 : 0 < Wfun s x) (hW1 : 0 < Wfun (s + 1) x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 0) z)
      (L2UvecC0At x s) x := by
  have hC := TowerBC.hasFDerivAt_fderiv_ringC0_any s x hW0
  have hC' := TowerBC.hasFDerivAt_fderiv_ringC0_any (s + 1) x hW1
  have hA := TowerBC.hasFDerivAt_fderiv_ArcC_any s 0 x
  have hW0e : ∀ᶠ w in nhds x, 0 < Wfun s w :=
    (hasFDerivAt_Wfun s x).continuousAt.eventually (eventually_gt_nhds hW0)
  have hW1e : ∀ᶠ w in nhds x, 0 < Wfun (s + 1) w :=
    (hasFDerivAt_Wfun (s + 1) x).continuousAt.eventually (eventually_gt_nhds hW1)
  have hCd : ∀ᶠ w in nhds x,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 0) w :=
    hW0e.mono fun w hw => (hasFDerivAt_ringCenter0_any s w (ne_of_gt hw)).differentiableAt
  have hC'd : ∀ᶠ w in nhds x,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 0) w :=
    hW1e.mono fun w hw => (hasFDerivAt_ringCenter0_any (s + 1) w (ne_of_gt hw)).differentiableAt
  have hAd : ∀ᶠ w in nhds x, DifferentiableAt ℝ (ArcC s 0) w :=
    Filter.Eventually.of_forall fun w => (hasFDerivAt_arcC0_any s w).differentiableAt
  have hsum := HessSeam.hasFDerivAt_fderiv_add_any (x := x) hC hC' hCd hC'd
  have hsumd : ∀ᶠ w in nhds x, DifferentiableAt ℝ
      ((fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 0)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 0)) w :=
    (hCd.and hC'd).mono fun _ hz => hz.1.add hz.2
  have hfun : (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 0)
      = (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 0)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 0)
        - ArcC s 0 := by
    funext z
    rw [Uvec_coord0]
    rfl
  have hsub := HessSeam.hasFDerivAt_fderiv_sub_any (x := x) hsum hA hsumd hAd
  have hmain : HasFDerivAt (fun z : Fin 7 → ℝ =>
      fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 0) z)
      ((TowerBC.L2RingC0At x s + TowerBC.L2RingC0At x (s + 1)) - TowerBC.L2ArcAt x s 0) x := by
    show HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ =>
      (ringCenter (pad12 z) s).ofLp 0
        + (ringCenter (pad12 z) (s + 1)).ofLp 0 - ArcC s 0 z) z) _ x
    exact hsub
  rw [show L2UvecC0At x s
      = (TowerBC.L2RingC0At x s + TowerBC.L2RingC0At x (s + 1)) - TowerBC.L2ArcAt x s 0 from rfl]
  exact hmain

set_option maxHeartbeats 2000000 in
theorem hasFDerivAt_fderiv_UvecC1_any (s : Fin 9) (x : Fin 7 → ℝ)
    (hW0 : 0 < Wfun s x) (hW1 : 0 < Wfun (s + 1) x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 1) z)
      (L2UvecC1At x s) x := by
  have hC := TowerBC.hasFDerivAt_fderiv_ringC1_any s x hW0
  have hC' := TowerBC.hasFDerivAt_fderiv_ringC1_any (s + 1) x hW1
  have hA := TowerBC.hasFDerivAt_fderiv_ArcC_any s 1 x
  have hW0e : ∀ᶠ w in nhds x, 0 < Wfun s w :=
    (hasFDerivAt_Wfun s x).continuousAt.eventually (eventually_gt_nhds hW0)
  have hW1e : ∀ᶠ w in nhds x, 0 < Wfun (s + 1) w :=
    (hasFDerivAt_Wfun (s + 1) x).continuousAt.eventually (eventually_gt_nhds hW1)
  have hCd : ∀ᶠ w in nhds x,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 1) w :=
    hW0e.mono fun w hw => (hasFDerivAt_ringCenter1_any s w (ne_of_gt hw)).differentiableAt
  have hC'd : ∀ᶠ w in nhds x,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 1) w :=
    hW1e.mono fun w hw => (hasFDerivAt_ringCenter1_any (s + 1) w (ne_of_gt hw)).differentiableAt
  have hAd : ∀ᶠ w in nhds x, DifferentiableAt ℝ (ArcC s 1) w :=
    Filter.Eventually.of_forall fun w => (hasFDerivAt_arcC1_any s w).differentiableAt
  have hsum := HessSeam.hasFDerivAt_fderiv_add_any (x := x) hC hC' hCd hC'd
  have hsumd : ∀ᶠ w in nhds x, DifferentiableAt ℝ
      ((fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 1)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 1)) w :=
    (hCd.and hC'd).mono fun _ hz => hz.1.add hz.2
  have hfun : (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 1)
      = (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 1)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 1)
        - ArcC s 1 := by
    funext z
    rw [Uvec_coord1]
    rfl
  have hsub := HessSeam.hasFDerivAt_fderiv_sub_any (x := x) hsum hA hsumd hAd
  have hmain : HasFDerivAt (fun z : Fin 7 → ℝ =>
      fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 1) z)
      ((TowerBC.L2RingC1At x s + TowerBC.L2RingC1At x (s + 1)) - TowerBC.L2ArcAt x s 1) x := by
    show HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ =>
      (ringCenter (pad12 z) s).ofLp 1
        + (ringCenter (pad12 z) (s + 1)).ofLp 1 - ArcC s 1 z) z) _ x
    exact hsub
  rw [show L2UvecC1At x s
      = (TowerBC.L2RingC1At x s + TowerBC.L2RingC1At x (s + 1)) - TowerBC.L2ArcAt x s 1 from rfl]
  exact hmain

/-! ## 5. (3) 二阶 CLM：`L2DeltaX_any` / `L2DeltaY_any` -/

@[reducible] def L2PtC0_any (x : Fin 7 → ℝ) (k : Fin 5) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  match k with
  | 0 => L2UvecC0At x 1
  | 1 => L2UvecC0At x 2
  | 2 => L2UvecC0At x 3
  | 3 => L2UvecC0At x 8
  | 4 => 0

@[reducible] def L2PtC1_any (x : Fin 7 → ℝ) (k : Fin 5) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  match k with
  | 0 => L2UvecC1At x 1
  | 1 => L2UvecC1At x 2
  | 2 => L2UvecC1At x 3
  | 3 => L2UvecC1At x 8
  | 4 => TowerBC.L2WyAt x

@[reducible] def L2HubC0_any (x : Fin 7 → ℝ) (k : Fin 5) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  match k with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => TowerBC.L2RingC0At x 6

@[reducible] def L2HubC1_any (x : Fin 7 → ℝ) (k : Fin 5) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  match k with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => TowerBC.L2RingC1At x 6

def L2DeltaX_any (x : Fin 7 → ℝ) (k : Fin 5) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  L2PtC0_any x k - L2HubC0_any x k

def L2DeltaY_any (x : Fin 7 → ℝ) (k : Fin 5) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  L2PtC1_any x k - L2HubC1_any x k

theorem hasFDerivAt_fderiv_PtC_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF k) z) (L2PtC0_any x k) x := by
  have hk0 : (k = (0 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF k) z)
      (L2PtC0_any x k) x := by
    intro hk; subst hk
    exact hasFDerivAt_fderiv_UvecC0_any 1 x hWa hWb
  have hk1 : (k = (1 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF k) z)
      (L2PtC0_any x k) x := by
    intro hk; subst hk
    exact hasFDerivAt_fderiv_UvecC0_any 2 x hWa hWb
  have hk2 : (k = (2 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF k) z)
      (L2PtC0_any x k) x := by
    intro hk; subst hk
    exact hasFDerivAt_fderiv_UvecC0_any 3 x hWa hWb
  have hk3 : (k = (3 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF k) z)
      (L2PtC0_any x k) x := by
    intro hk; subst hk
    exact hasFDerivAt_fderiv_UvecC0_any 8 x hWa hWb
  have hk4 : (k = (4 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF k) z)
      (L2PtC0_any x k) x := by
    intro hk; subst hk
    have hx : (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0)
        = fun z => ((1 / 2 : ℝ) • (coord 4 + coord 5)) z := by
      funext z
      rw [wPoint_coord0, pad12_four, pad12_five]
      change (z 4 + z 5) / 2 = (1 / 2) * (z 4 + z 5)
      ring
    exact TowerBC.hasFDerivAt_fderiv_of_eq_clm_any x hx
  fin_cases k
  · exact hk0 rfl
  · exact hk1 rfl
  · exact hk2 rfl
  · exact hk3 rfl
  · exact hk4 rfl

theorem hasFDerivAt_fderiv_PtCF1_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF1 k) z) (L2PtC1_any x k) x := by
  have hk0 : (k = (0 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF1 k) z)
      (L2PtC1_any x k) x := by
    intro hk; subst hk
    exact hasFDerivAt_fderiv_UvecC1_any 1 x hWa hWb
  have hk1 : (k = (1 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF1 k) z)
      (L2PtC1_any x k) x := by
    intro hk; subst hk
    exact hasFDerivAt_fderiv_UvecC1_any 2 x hWa hWb
  have hk2 : (k = (2 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF1 k) z)
      (L2PtC1_any x k) x := by
    intro hk; subst hk
    exact hasFDerivAt_fderiv_UvecC1_any 3 x hWa hWb
  have hk3 : (k = (3 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF1 k) z)
      (L2PtC1_any x k) x := by
    intro hk; subst hk
    exact hasFDerivAt_fderiv_UvecC1_any 8 x hWa hWb
  have hk4 : (k = (4 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (PtCF1 k) z)
      (L2PtC1_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_wyF_any x hWp
  fin_cases k
  · exact hk0 rfl
  · exact hk1 rfl
  · exact hk2 rfl
  · exact hk3 rfl
  · exact hk4 rfl

theorem hasFDerivAt_fderiv_HubC_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hW6 : 0 < Wfun 6 x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF k) z) (L2HubC0_any x k) x := by
  have hk0 : (k = (0 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF k) z)
      (L2HubC0_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_of_eq_clm_any x hub1xF_eq
  have hk1 : (k = (1 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF k) z)
      (L2HubC0_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_of_eq_clm_any x hub0xF_eq
  have hk2 : (k = (2 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF k) z)
      (L2HubC0_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_of_eq_clm_any x hub0xF_eq
  have hk3 : (k = (3 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF k) z)
      (L2HubC0_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_of_eq_clm_any x hub1xF_eq
  have hk4 : (k = (4 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF k) z)
      (L2HubC0_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_ringC0_any 6 x hW6
  fin_cases k
  · exact hk0 rfl
  · exact hk1 rfl
  · exact hk2 rfl
  · exact hk3 rfl
  · exact hk4 rfl

theorem hasFDerivAt_fderiv_HubCF1_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hW6 : 0 < Wfun 6 x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF1 k) z) (L2HubC1_any x k) x := by
  have hk0 : (k = (0 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF1 k) z)
      (L2HubC1_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_of_eq_const_any hub1yF_eq x
  have hk1 : (k = (1 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF1 k) z)
      (L2HubC1_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_of_eq_const_any hub0yF_eq x
  have hk2 : (k = (2 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF1 k) z)
      (L2HubC1_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_of_eq_const_any hub0yF_eq x
  have hk3 : (k = (3 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF1 k) z)
      (L2HubC1_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_of_eq_const_any hub1yF_eq x
  have hk4 : (k = (4 : Fin 5)) → HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HubCF1 k) z)
      (L2HubC1_any x k) x := by
    intro hk; subst hk
    exact TowerBC.hasFDerivAt_fderiv_ringC1_any 6 x hW6
  fin_cases k
  · exact hk0 rfl
  · exact hk1 rfl
  · exact hk2 rfl
  · exact hk3 rfl
  · exact hk4 rfl

theorem hasFDerivAt_fderiv_DeltaX_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (DeltaX k) z) (L2DeltaX_any x k) x := by
  have hP := hasFDerivAt_fderiv_PtC_any k x hWa hWb hW6 hWp
  have hH := hasFDerivAt_fderiv_HubC_any k x hW6
  have hWae : ∀ᶠ w in nhds x, 0 < Wfun (resSlot k) w :=
    (hasFDerivAt_Wfun (resSlot k) x).continuousAt.eventually (eventually_gt_nhds hWa)
  have hWbe : ∀ᶠ w in nhds x, 0 < Wfun ((resSlot k) + 1) w :=
    (hasFDerivAt_Wfun ((resSlot k) + 1) x).continuousAt.eventually (eventually_gt_nhds hWb)
  have hW6e : ∀ᶠ w in nhds x, 0 < Wfun 6 w :=
    (hasFDerivAt_Wfun 6 x).continuousAt.eventually (eventually_gt_nhds hW6)
  have hWpe : ∀ᶠ w in nhds x, 0 < Wpf w :=
    (hasFDerivAt_Wpf_any x).continuousAt.eventually (eventually_gt_nhds hWp)
  have hsub := HessSeam.hasFDerivAt_fderiv_sub_any (x := x) hP hH
    (hWae.and hWbe |>.and hW6e |>.and hWpe |>.mono fun z hz =>
      PtCF_differentiable_forall k z hz.1.1.1 hz.1.1.2 hz.1.2 hz.2)
    (hW6e.and hWpe |>.mono fun z hz => HubCF_differentiable_forall k z hz.1 hz.2)
  have hmain : HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ
      (fun y : Fin 7 → ℝ => PtCF k y - HubCF k y) z) (L2PtC0_any x k - L2HubC0_any x k) x := hsub
  have hgoal : DeltaX12 k = PtCF k - HubCF k := DeltaX12_sub k
  rw [show (fun z : Fin 7 → ℝ => fderiv ℝ (fun y : Fin 7 → ℝ => DeltaX k y) z)
      = (fun z : Fin 7 → ℝ => fderiv ℝ (fun y : Fin 7 → ℝ => DeltaX12 k y) z) from by
        rw [DeltaX_eq]]
  rw [show (fun y : Fin 7 → ℝ => DeltaX12 k y) = (fun y : Fin 7 → ℝ => PtCF k y - HubCF k y) from by
    rw [hgoal]; rfl]
  exact hmain

theorem hasFDerivAt_fderiv_DeltaY_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (DeltaY k) z) (L2DeltaY_any x k) x := by
  have hP := hasFDerivAt_fderiv_PtCF1_any k x hWa hWb hW6 hWp
  have hH := hasFDerivAt_fderiv_HubCF1_any k x hW6
  have hWae : ∀ᶠ w in nhds x, 0 < Wfun (resSlot k) w :=
    (hasFDerivAt_Wfun (resSlot k) x).continuousAt.eventually (eventually_gt_nhds hWa)
  have hWbe : ∀ᶠ w in nhds x, 0 < Wfun ((resSlot k) + 1) w :=
    (hasFDerivAt_Wfun ((resSlot k) + 1) x).continuousAt.eventually (eventually_gt_nhds hWb)
  have hW6e : ∀ᶠ w in nhds x, 0 < Wfun 6 w :=
    (hasFDerivAt_Wfun 6 x).continuousAt.eventually (eventually_gt_nhds hW6)
  have hWpe : ∀ᶠ w in nhds x, 0 < Wpf w :=
    (hasFDerivAt_Wpf_any x).continuousAt.eventually (eventually_gt_nhds hWp)
  have hsub := HessSeam.hasFDerivAt_fderiv_sub_any (x := x) hP hH
    (hWae.and hWbe |>.and hW6e |>.and hWpe |>.mono fun z hz =>
      PtCF1_differentiable_forall k z hz.1.1.1 hz.1.1.2 hz.1.2 hz.2)
    (hW6e.and hWpe |>.mono fun z hz => HubCF1_differentiable_forall k z hz.1 hz.2)
  have hmain : HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ
      (fun y : Fin 7 → ℝ => PtCF1 k y - HubCF1 k y) z) (L2PtC1_any x k - L2HubC1_any x k) x := hsub
  have hgoal : DeltaY12 k = PtCF1 k - HubCF1 k := DeltaY12_sub k
  rw [show (fun z : Fin 7 → ℝ => fderiv ℝ (fun y : Fin 7 → ℝ => DeltaY k y) z)
      = (fun z : Fin 7 → ℝ => fderiv ℝ (fun y : Fin 7 → ℝ => DeltaY12 k y) z) from by
        rw [DeltaY_eq]]
  rw [show (fun y : Fin 7 → ℝ => DeltaY12 k y) = (fun y : Fin 7 → ℝ => PtCF1 k y - HubCF1 k y) from by
    rw [hgoal]; rfl]
  exact hmain

/-! ## 6. (4) `SRad2_any`：`S_k` 的二阶取值（`(5)` 的输入）

模板 = `HessSeamHL7.SRad2_single`（球心 `u0` → 一般点 `x`）。
第二项系数写成 `((fderiv …) (single i 1)) * ((fderiv …) (single j 1))`（**同序**），
与 `HasFDerivAt` 产出形（`smulRight`）逐字对齐 ✓。 -/

@[reducible] def L2SRad_any (x : Fin 7 → ℝ) (k : Fin 5) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  ((DeltaX k x) • L2DeltaX_any x k + (fderiv ℝ (DeltaX k) x).smulRight (fderiv ℝ (DeltaX k) x)
      + ((DeltaX k x) • L2DeltaX_any x k
        + (fderiv ℝ (DeltaX k) x).smulRight (fderiv ℝ (DeltaX k) x)))
    + ((DeltaY k x) • L2DeltaY_any x k + (fderiv ℝ (DeltaY k) x).smulRight (fderiv ℝ (DeltaY k) x)
      + ((DeltaY k x) • L2DeltaY_any x k
        + (fderiv ℝ (DeltaY k) x).smulRight (fderiv ℝ (DeltaY k) x)))

theorem hasFDerivAt_fderiv_SRad_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (HessSeam.SRad k) z) (L2SRad_any x k) x := by
  have hX := HessSeam.hasFDerivAt_fderiv_mul_scalar_any (φ := DeltaX k) (ψ := DeltaX k) x
    (hasFDerivAt_DeltaX_any k x hWa hWb hW6 hWp) (hasFDerivAt_fderiv_DeltaX_any k x hWa hWb hW6 hWp)
    (hasFDerivAt_DeltaX_any k x hWa hWb hW6 hWp) (hasFDerivAt_fderiv_DeltaX_any k x hWa hWb hW6 hWp)
    (eventually_diff_DeltaX_any k x hWa hWb hW6 hWp) (eventually_diff_DeltaX_any k x hWa hWb hW6 hWp)
  have hY := HessSeam.hasFDerivAt_fderiv_mul_scalar_any (φ := DeltaY k) (ψ := DeltaY k) x
    (hasFDerivAt_DeltaY_any k x hWa hWb hW6 hWp) (hasFDerivAt_fderiv_DeltaY_any k x hWa hWb hW6 hWp)
    (hasFDerivAt_DeltaY_any k x hWa hWb hW6 hWp) (hasFDerivAt_fderiv_DeltaY_any k x hWa hWb hW6 hWp)
    (eventually_diff_DeltaY_any k x hWa hWb hW6 hWp) (eventually_diff_DeltaY_any k x hWa hWb hW6 hWp)
  have hsum := HessSeam.hasFDerivAt_fderiv_add_any (x := x) hX hY
    (eventually_diff_DXsq_any k x hWa hWb hW6 hWp) (eventually_diff_DYsq_any k x hWa hWb hW6 hWp)
  rw [L2SRad_any]
  exact hsum

theorem SRad2_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) (i j : Fin 7) :
    secondPartial (HessSeam.SRad k) x i j
      = 2 * ((DeltaX k x) * secondPartial (DeltaX k) x i j
            + ((fderiv ℝ (DeltaX k) x) (Pi.single i 1))
              * ((fderiv ℝ (DeltaX k) x) (Pi.single j 1)))
        + 2 * ((DeltaY k x) * secondPartial (DeltaY k) x i j
            + ((fderiv ℝ (DeltaY k) x) (Pi.single i 1))
              * ((fderiv ℝ (DeltaY k) x) (Pi.single j 1))) := by
  have hSRad : (fun z : Fin 7 → ℝ => HessSeam.SRad k z)
      = fun z : Fin 7 → ℝ => DeltaX k z * DeltaX k z + DeltaY k z * DeltaY k z := by
    funext z
    rfl
  have hval : secondPartial (HessSeam.SRad k) x i j
      = (L2SRad_any x k (Pi.single j 1)) (Pi.single i 1) := by
    have h : secondPartial (fun z : Fin 7 → ℝ => HessSeam.SRad k z) x i j
        = (L2SRad_any x k (Pi.single j 1)) (Pi.single i 1) :=
      secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_SRad_any k x hWa hWb hW6 hWp) i j
    rw [hSRad] at h
    exact h
  have h2x := (hasFDerivAt_fderiv_DeltaX_any k x hWa hWb hW6 hWp).fderiv
  have h2y := (hasFDerivAt_fderiv_DeltaY_any k x hWa hWb hW6 hWp).fderiv
  rw [hval, L2SRad_any]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.smulRight_apply]
  rw [← h2x, ← h2y]
  rw [show secondPartial (DeltaX k) x i j
      = (fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ (DeltaX k) y) x
          (Pi.single j 1)) (Pi.single i 1) from rfl]
  rw [show secondPartial (DeltaY k) x i j
      = (fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ (DeltaY k) y) x
          (Pi.single j 1)) (Pi.single i 1) from rfl]
  rw [h2x, h2y]
  ring_nf

/-! ## 7. (5) `sqrtSRad2_any`：`√S_k` 的二阶取值 -/

@[reducible] def L2SqrtSRad_any (x : Fin 7 → ℝ) (k : Fin 5) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (deriv Real.sqrt (HessSeam.SRad k x)) • L2SRad_any x k
    + (((fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (HessSeam.SRad k x)).comp
        (fderiv ℝ (HessSeam.SRad k) x)).smulRight (fderiv ℝ (HessSeam.SRad k) x))

theorem hasFDerivAt_fderiv_sqrtSRad_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) (hpos : 0 < HessSeam.SRad k x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => Real.sqrt (HessSeam.SRad k z)) z)
      (L2SqrtSRad_any x k) x := by
  have hS : HasFDerivAt (HessSeam.SRad k) (fderiv ℝ (HessSeam.SRad k) x) x :=
    ((eventually_diff_SRad_any k x hWa hWb hW6 hWp).self_of_nhds).hasFDerivAt
  rw [L2SqrtSRad_any]
  refine HessSeam.hasFDerivAt_fderiv_comp_scalar_any (g := HessSeam.SRad k) (u := Real.sqrt) x
    hS (hasFDerivAt_fderiv_SRad_any k x hWa hWb hW6 hWp) ?_ ?_ ?_
  · have hu := (hasDerivAt_deriv_sqrt hpos).hasFDerivAt
    have hu' : HasFDerivAt (fun t : ℝ => deriv Real.sqrt t)
        (fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (HessSeam.SRad k x)) (HessSeam.SRad k x) := by
      rw [hu.fderiv]
      exact hu
    exact hu'
  · exact eventually_diff_SRad_any k x hWa hWb hW6 hWp
  · have hcont : ContinuousAt (HessSeam.SRad k) x := hS.continuousAt
    filter_upwards [hcont.eventually (IsOpen.mem_nhds isOpen_ne (ne_of_gt hpos))] with z hz
    exact (Real.hasDerivAt_sqrt hz).differentiableAt

theorem sqrtSRad2_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) (hpos : 0 < HessSeam.SRad k x) (i j : Fin 7) :
    (L2SqrtSRad_any x k (Pi.single j 1)) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (HessSeam.SRad k x))) * (secondPartial (HessSeam.SRad k) x i j)
        + ((-2) * (1 / (2 * Real.sqrt (HessSeam.SRad k x))))
            * ((2 * Real.sqrt (HessSeam.SRad k x)) * (2 * Real.sqrt (HessSeam.SRad k x)))⁻¹
            * ((fderiv ℝ (HessSeam.SRad k) x) (Pi.single j 1))
            * ((fderiv ℝ (HessSeam.SRad k) x) (Pi.single i 1)) := by
  rw [L2SqrtSRad_any]
  simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [d2_fderivReal_apply_eq_mul_one, fderiv_apply_one_eq_deriv]
  rw [HasDerivAt.deriv (Real.hasDerivAt_sqrt (ne_of_gt hpos))]
  rw [HasDerivAt.deriv (hasDerivAt_deriv_sqrt hpos)]
  rw [SRad2_any k x hWa hWb hW6 hWp i j]
  rw [show secondPartial (DeltaX k) x i j
      = (fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ (DeltaX k) y) x
          (Pi.single j 1)) (Pi.single i 1) from rfl]
  rw [show secondPartial (DeltaY k) x i j
      = (fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ (DeltaY k) y) x
          (Pi.single j 1)) (Pi.single i 1) from rfl]
  rw [show (fun y : Fin 7 → ℝ => fderiv ℝ (DeltaX k) y) = fun y => fderiv ℝ (DeltaX k) y from rfl]
  rw [show (fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ (DeltaX k) y) x)
      = L2DeltaX_any x k from (hasFDerivAt_fderiv_DeltaX_any k x hWa hWb hW6 hWp).fderiv]
  rw [show (fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ (DeltaY k) y) x)
      = L2DeltaY_any x k from (hasFDerivAt_fderiv_DeltaY_any k x hWa hWb hW6 hWp).fderiv]
  ring_nf

/-! ## 8. (6) `secondPartial_sqrtSRad_any`：二阶取值 ⇔ `L2SqrtSRad_any`（**已证**）

模板 = `HessSeamHL7.secondPartial_sqrtSRad`（球心 `u0` → 一般点 `x`）。
⚠ 其**右端**是 `distHessReal`（**球心专属**具名靶）；一般点的对应物是
`N11Formalization.Lead.HessBoxMem.distHessRealBox (pad12 x) k i j`（**逐点靶**）。
把 `(6)` 的右端换成 `distHessRealBox` 还需**系数桥**（见下节**未付**）。 -/

theorem secondPartial_sqrtSRad_any (k : Fin 5) (x : Fin 7 → ℝ)
    (hWa : 0 < Wfun (resSlot k) x) (hWb : 0 < Wfun ((resSlot k) + 1) x)
    (hW6 : 0 < Wfun 6 x) (hWp : 0 < Wpf x) (hpos : 0 < HessSeam.SRad k x) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => Real.sqrt (HessSeam.SRad k z)) x i j
      = (1 / (2 * Real.sqrt (HessSeam.SRad k x))) * (secondPartial (HessSeam.SRad k) x i j)
        + ((-2) * (1 / (2 * Real.sqrt (HessSeam.SRad k x))))
            * ((2 * Real.sqrt (HessSeam.SRad k x)) * (2 * Real.sqrt (HessSeam.SRad k x)))⁻¹
            * ((fderiv ℝ (HessSeam.SRad k) x) (Pi.single j 1))
            * ((fderiv ℝ (HessSeam.SRad k) x) (Pi.single i 1)) := by
  have h := sqrtSRad2_any k x hWa hWb hW6 hWp hpos i j
  rw [show secondPartial (fun z : Fin 7 → ℝ => Real.sqrt (HessSeam.SRad k z)) x i j
      = (L2SqrtSRad_any x k (Pi.single j 1)) (Pi.single i 1) from
    secondPartial_eq_of_hasFDerivAt
      (hasFDerivAt_fderiv_sqrtSRad_any k x hWa hWb hW6 hWp hpos) i j]
  exact h

/-! ## 9. **未付的那一步（如实登记）**：`dUxReal` 系数桥

`(6)` 的目标右端（`distHessRealBox (pad12 x) k i j`）的五原子是
`(Apt k (pad12 x)).ofLp 0` / `.ofLp 1`（= `DeltaX k x`/`DeltaY k x` ✓ 定义层同一）、
`dUxReal k i (pad12 x)` / `dUyReal k i (pad12 x)`、
`secondPartial (DeltaX k) (first7 (pad12 x)) i j`（= `secondPartial (DeltaX k) x i j` ✓）。

⇒ 只差**一条**：`(fderiv ℝ (DeltaX k) x) (Pi.single i 1) = dUxReal k i (pad12 x)`（`Δy` 同）。
其证法（下一轮）：
```lean
-- v := fun y : Fin 12 → ℝ => DeltaX k (first7 y)  （= DeltaX12 k，逐点 ✓）
-- ① fderiv ℝ v (pad12 x) = (fderiv ℝ (DeltaX k) (pad12 x)).comp proj7CLM   （`fderiv_comp` + `first7`）
-- ② 再对 Δx_k ∘ pad12 用一次 `fderiv_comp`（被求值点 `pad12 x`）:
--    fderiv ℝ (Δx_k ∘ pad12) (pad12 x) = (fderiv ℝ (DeltaX k) (pad12 x)).comp (fderiv ℝ pad12 (pad12 x))
-- ③ 左端逐支展开（`dUvec0Real x s i` 等）⇒ = `dUxReal k i (pad12 x)`
```
**需要的前提**（`pad12 x` 处的正性，**不是** `x` 处）：`0 < Wfun (resSlot k) (pad12 x)`、
`0 < Wfun ((resSlot k)+1) (pad12 x)`、`0 < Wfun 6 (pad12 x)`、`0 < Wpf (pad12 x)`。
⚠ 本仓库的 `hWkL` 型区间数据只给了 `u0` 处 ✗ ⇒ 在**一般 `x`** 上是**新的显式前提**。
本轮**未**走通这一步 ✗（不是"缺料"，是"缺一次 `fderiv_comp` 装配"）。 -/

end DeltaAny

end N11Formalization
