import N11Formalization.F1.BallD35C13
import N11Formalization.F1.BallD35C10
import N11Formalization.F1.BallD35Hrad
import N11Formalization.HessSeamBall
import N11Formalization.HessSeamHL7
import N11Formalization.DeltaAny
import N11Formalization.NondegProof
import N11Formalization.Transport

/-!
# I-2：件 B（`FinalBridgeB.core`）的**七条前提**由 `hx` 供给 —— `PremiseBundle`

**义务**（简报 §3 I-2）：对**任意合法盒内点** `x ∈ Metric.closedBall certCR rhoCertR`，把
`u := first7 x` 代入 `theorem core` 所需的七条前提**逐条具名**成立：
`pb_hd / pb_hadj / pb_hWa / pb_hWb / pb_hW6 / pb_hWp / pb_hpos`。
**不合成合取**、**不新增任何未证前提**、**不放宽结论形状**。

## 普查结论（`#check @全名` 实测读数见 `_readout.out.txt`；时刻 2026-09-28 19:34 探针）

1. **正性五条走「12 维证书盒」，不走 `Q7` + `TowerBC.Wfun_pos_of_wkBoxQ`**。
   实测：`@TowerBC.Wfun_pos_of_wkBoxQ` 的第二条前提是 `0 < (TowerBC.wkBoxQ Q s).lo`，
   而 `wkBoxQ` 是**泛型盒**函数 —— `TowerBC_N_anyx_layer1.lean` L798 自己写明
   「泛型 `Q` **无全局正性** ✗ ⇒ 当假设」，`D2IvBoxMem.lean` L434/L480 同样把它**当假设**吃。
   ⇒ `Q7` 路线的这条前提 **cone 里没有**（不是形状不合，是真的没付）。
   正解 = 无条件 ℚ 级正性三件 + `hx` 版 `Mem`（`*_mem` 的参数**就是 12 维 `x`**）：
   `wkBox_pos (j : Fin 9)` / `wkBox_mem hx j`、`WpIvBox_pos` / `WpIvBox_mem hx`、
   `radIvBox_pos k` / `radIvBox_mem k hx`，配 `RatInterval.mem_lo_le` ⇒ **`0 <` 值**（不是 `≠ 0`）。
   ⇒ 简报 §3 ⚠「`radIvBox_ne_zero_of_ball` 只给 `≠ 0`」的困境由 `radIvBox_mem + radIvBox_pos` 解除。
2. **换形只用四件**（全部 `#check` 核过）：`first7_six`（rfl 级）、`angleVec_transport`、
   `Apt_transport`/`Bpt_transport`（顶层名，`F1/BallD35C12` L82/L91；`HessSeam.*` 是同名第二份），
   加 `Wpf (first7 x) = WpReal x := rfl`（**探针实测 defeq ✓**）、`pow_two` 换 `^2` ↔ `*`。
3. **`pb_hd`**：cone **没有**任何 `∀ᶠ z in nhds u, DifferentiableAt ℝ residualFun z`
   （`HessSeamHL7.lean` L17 明写 `hd` 是前提、「不可由 `hadj` 推出」）⇒ 本件**新供给**：
   `contDiffAt_residualFun_first7 (n := (2 : WithTop ℕ∞))`（前提写在 **12 维 `x`** 上）
   → `contDiffAt_pi` → mathlib `ContDiffAt.eventually (_ : n ≠ ∞)`（`ContDiff/Defs.lean` L1036）
   → `filter_upwards` → `ContDiffAt.differentiableAt`。
4. **`pb_hadj`**：cone 的 `differentiableAt_fderiv_residualFun_of_ball` 要 `pad12 z ∈ closedBall certCR rhoCertR`
   —— 喂 `z = first7 x` 需 `pad12 (first7 x) ∈ ball`，**假命题**（NOTE 否定 2；真提升是 `HessSeam.lift12`，
   `lift12 z ≠ pad12 z`）。⇒ 本件**不换命题、不放宽**：照 `BallD35C13.differentiableAt_residualFun_first7_ball`
   （L74–83，前提已是 `x ∈ ball`）的骨架，末行换成 `contDiffAt_fderiv_residualFun (m := ⊤)`。
   ⇒ **结论形状与 C10 逐字同**（`DifferentiableAt ℝ (fun z => fderiv ℝ residualFun z) (first7 x)`），
   **前提形状**换成 `hx`。这是**新件**，不是重述根内定理。
5. `rho_of_ball` / `radW_of_ball`（`F1/BallD35C13` L56/L62，件在 `N11Formalization` **顶层**）
   已是「`hx` ⇒ `≠ 0`」的现成件 ⇒ 本件直接复用，不手搓 `simpa [pow_two]`。

**口径**：无 `sorry` / 无 `admit` / 无自定义 `axiom` / 无 `native_decide`；
`decide`/`omega` 不新增；公理画像见 `_readout.out.txt`（只在 0 error 时读）。
-/

noncomputable section

namespace N11Formalization

namespace PremiseBundle

/-! ## 1. 可微性两条 -/

/-- **`hd` 的球上供给**（简报 §3 I-2 第 1 条）：任意合法盒内点 `x` ⇒ `residualFun` 在
`first7 x` 的**邻域**逐点可微。cone 内此前**不存在**任何 `_any` 版邻域可微性件
（`HessSeamHL7` L17 把 `hd` 列为前提）⇒ 本条是**新供给**，不是重述。 -/
theorem pb_hd {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    ∀ᶠ z in nhds (first7 x), DifferentiableAt ℝ residualFun z := by
  obtain ⟨hU1, hU2, hU3, hU8, hWpne⟩ := nd_all_via_dist
  have hC : ContDiffAt ℝ (2 : WithTop ℕ∞) residualFun (first7 x) := by
    rw [contDiffAt_pi]
    intro i
    exact contDiffAt_residualFun_first7 (n := (2 : WithTop ℕ∞)) x (rho_of_ball hx) (radW_of_ball hx)
      (hU1 x hx) (hU2 x hx) (hU3 x hx) (hU8 x hx) (hWpne x hx) i
  have he : ∀ᶠ z in nhds (first7 x), ContDiffAt ℝ (2 : WithTop ℕ∞) residualFun z :=
    hC.eventually (by simp)
  filter_upwards [he] with z hz
  exact hz.differentiableAt (by simp)

/-- **`hadj` 的球上供给**（简报 §3 I-2 第 2 条）：`z ↦ fderiv ℝ residualFun z` 在 `first7 x` 可微。
**不**经 `BallD35C10.differentiableAt_fderiv_residualFun_of_ball`（它要 `pad12 z ∈ ball`，
喂 `first7 x` 是**假**）；走 `contDiffAt_residualFun_first7 (n := ⊤ + 1)` +
`contDiffAt_fderiv_residualFun (m := ⊤)` —— 与 C13 的 `differentiableAt_residualFun_first7_ball`
同骨架、同前提形状（只 `hx`）。 -/
theorem pb_hadj {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) (first7 x) := by
  obtain ⟨hU1, hU2, hU3, hU8, hWpne⟩ := nd_all_via_dist
  have hC : ContDiffAt ℝ (⊤ + 1) (fun w : Fin 7 → ℝ => residualFun w) (first7 x) := by
    rw [contDiffAt_pi]
    intro i
    exact contDiffAt_residualFun_first7 (n := ⊤ + 1) x (rho_of_ball hx) (radW_of_ball hx)
      (hU1 x hx) (hU2 x hx) (hU3 x hx) (hU8 x hx) (hWpne x hx) i
  exact (contDiffAt_fderiv_residualFun (m := ⊤) hC).differentiableAt (by simp)

/-! ## 2. 正性五条（`Wfun` 泛型一条 + 三条实例 + `Wpf` + `SRad`） -/

/-- **`Wfun` 的球上正性（泛型槽 `s : Fin 9`）**：
`(wkBox s).lo > 0`（ℚ 级、无条件，`BallD35Hrad` L37）＋ `(wkBox s).Mem (值在 12 维 x 上)`
（L40）⇒ 值 `> 0`；再用 `first7_six` + `angleVec_transport` + `pow_two` 将「值在 `x`」换成
「`Wfun s (first7 x)`」（逐字换形，`simp only` 四件）。 -/
theorem pb_Wfun_pos {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) (s : Fin 9) :
    0 < Wfun s (first7 x) := by
  have h1 : ((wkBox s).lo : ℝ) ≤ x 6 * x 6 - Real.sin (angleVec x s) * Real.sin (angleVec x s) :=
    RatInterval.mem_lo_le (wkBox_mem hx s)
  have h2 : (0 : ℝ) < (((wkBox s).lo : ℚ) : ℝ) := by exact_mod_cast wkBox_pos s
  have h3 : 0 < x 6 * x 6 - Real.sin (angleVec x s) * Real.sin (angleVec x s) :=
    lt_of_lt_of_le h2 h1
  have h4 : Wfun s (first7 x)
      = x 6 * x 6 - Real.sin (angleVec x s) * Real.sin (angleVec x s) := by
    simp only [Wfun, first7_six, angleVec_transport, pow_two]
  rw [h4]
  exact h3

/-- **`hWa`**（简报 §3 I-2 第 3 条）：`0 < Wfun (resSlot k) (first7 x)`。 -/
theorem pb_hWa (k : Fin 5) {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    0 < Wfun (resSlot k) (first7 x) :=
  pb_Wfun_pos hx (resSlot k)

/-- **`hWb`**（简报 §3 I-2 第 4 条）：`0 < Wfun ((resSlot k) + 1) (first7 x)`。 -/
theorem pb_hWb (k : Fin 5) {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    0 < Wfun ((resSlot k) + 1) (first7 x) :=
  pb_Wfun_pos hx (resSlot k + 1)

/-- **`hW6`**（简报 §3 I-2 第 5 条）：`0 < Wfun 6 (first7 x)`（`6 : Fin 9` 字面量）。 -/
theorem pb_hW6 {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    0 < Wfun 6 (first7 x) :=
  pb_Wfun_pos hx 6

/-- **`hWp`**（简报 §3 I-2 第 6 条）：`0 < Wpf (first7 x)`。
`Wpf (first7 x) = WpReal x` 是 **defeq**（探针实测 `rfl` ✓）⇒ 直接吃
`WpIvBox_pos`（`BallD35Hrad` L158，无条件 ℚ 级）+ `WpIvBox_mem hx`（L161）。 -/
theorem pb_hWp {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    0 < Wpf (first7 x) := by
  have h1 : (WpIvBox.lo : ℝ) ≤ WpReal x := RatInterval.mem_lo_le (WpIvBox_mem hx)
  have h2 : (0 : ℝ) < ((WpIvBox.lo : ℚ) : ℝ) := by exact_mod_cast WpIvBox_pos
  have h3 : 0 < WpReal x := lt_of_lt_of_le h2 h1
  rw [show Wpf (first7 x) = WpReal x from rfl]
  exact h3

/-- **`hpos`**（简报 §3 I-2 第 7 条）：`0 < HessSeam.SRad k (first7 x)`。
**不用** `radIvBox_ne_zero_of_ball`（只给 `≠ 0` ⇒ 还需另取非负性）；改吃
`radIvBox_pos k`（L524，无条件 ℚ 级）+ `radIvBox_mem k hx`（L127，**`^2` 形**），
再 `simp only [SRad, DeltaX, DeltaY, Apt_transport, Bpt_transport, pow_two]`
把 `Δx·Δx + Δy·Δy`（在 `pad12 (first7 x)`）换成 `Δx^2 + Δy^2`（在 `x`）。 -/
theorem pb_hpos (k : Fin 5) {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    0 < HessSeam.SRad k (first7 x) := by
  have h1 : ((radIvBox k).lo : ℝ) ≤ ((Apt k x).ofLp 0 - (Bpt k x).ofLp 0) ^ 2
      + ((Apt k x).ofLp 1 - (Bpt k x).ofLp 1) ^ 2 := RatInterval.mem_lo_le (radIvBox_mem k hx)
  have h2 : (0 : ℝ) < (((radIvBox k).lo : ℚ) : ℝ) := by exact_mod_cast radIvBox_pos k
  have h3 : 0 < ((Apt k x).ofLp 0 - (Bpt k x).ofLp 0) ^ 2
      + ((Apt k x).ofLp 1 - (Bpt k x).ofLp 1) ^ 2 := lt_of_lt_of_le h2 h1
  have h4 : HessSeam.SRad k (first7 x)
      = ((Apt k x).ofLp 0 - (Bpt k x).ofLp 0) ^ 2 + ((Apt k x).ofLp 1 - (Bpt k x).ofLp 1) ^ 2 := by
    simp only [HessSeam.SRad, DeltaX, DeltaY, Apt_transport, Bpt_transport, pow_two]
  rw [h4]
  exact h3

end PremiseBundle

end N11Formalization
