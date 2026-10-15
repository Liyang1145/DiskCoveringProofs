import N11Formalization.HessSeamMain

/-!
# hess-seam 附（**去重版 v2**）：`hL7` 的**一阶桥**（`fderiv (DeltaX/DeltaY)` = `d1xR`/`d1yR`）

**去重改动（Lead R-去重，逐条）**：
1. `import N11Formalization.D2Leaves` → **`import N11Formalization.HessSeamMain`**（= `HessSeam_Cell000.lean`
   在 `srcDir` 的模块名；其 sha16 = `6E44199D4FD72448`，与我的绿件**逐字节相同**）；
2. **删除**本件原先自带的两条 def `d1xR`／`d1yR` —— 它们与 `HessSeamMain` 内的同名声明在**共享
   `namespace N11Formalization.HessSeam`** 下**逐字相同**（Lead 实测交集 = `{d1xR, d1yR}`，我复核定义体逐字一致 ✓）
   ⇒ 同时入根会报 `environment already contains`。去重后本件**不新增**任何与 Main 同名的声明。
3. 本件其余 **16 条**声明名（`d1xR_else`/`d1xR_four`/`d1yR_else`/`d1yR_four` 4 条读出 ＋
   `fderiv_DeltaX_{zero,one,two,three,four}`/`fderiv_DeltaY_{zero,one,two,three,four}` 10 条字面量子引理 ＋
   `fderiv_DeltaX`/`fderiv_DeltaY` 2 条 `fin_cases` 分派）与 Main **无交集**（已由"两件同时 import"
   探针 `scratch/HessSeamBOTH_probe.lean` = exit=0 / 0 行 验证 ✓）。
   ⚠ **口径**：本件**被 Main 反向依赖**（Main 不 import 本件）⇒ 单向依赖，无环 ✓。

**数学内容与 v1 逐字相同**（未改任何陈述/证明）：`hL7 : hessEntry i j mm = distHessReal mm i j` 的右端含
`d1xR`/`d1yR`（CLM 求值形态 = `d1xIv`/`d1yIv` 的 `Mem` 靶），把它接到**真正的 Fréchet 导数**
`fderiv ℝ (DeltaX k) u0 (Pi.single i 1)` 是 L7 实数恒等式**必经**一步。一阶 L7 本身根内已付
（`ResidualDerivDist.fderiv_residual_0..4`，CLM 形态与本件引用的 `d1xR` 内层逐字相同）。

**形状纪律**（照 `D2Leaves.d2xIv_mem` 先例）：`fin_cases` 会把 `k` 换成 `((fun i => i) ⟨0, ⋯⟩)` 形态，`rw` 匹配不上
⇒ 每个 `k` 字面量单独一条子引理，主引理只做 `fin_cases` + `exact`（defeq 容错）✓；
收尾不能用裸 `rfl`（`resSlot`/`resHub` 的 pattern-match 不在 `reducible` 透明度下展开）⇒ 用
`simp only [resSlot, resHub]`（显式列名 = 在 `reducible` 下也展开）✓。

**口径**：盒心 `u0 = first7 cCertR`；`ΔX k`/`ΔY k` = `D2Leaves` 的真值形态；
无 `sorry`/公理/`native_decide`；`decide` 只用在 `Fin` 索引上。
-/

noncomputable section

namespace N11Formalization

namespace HessSeam

open RatInterval

/-! ## 1. `d1xR`/`d1yR` 的两支读出（`d1xR`/`d1yR` 本体由 `HessSeamMain` 提供，本件不重定义） -/

theorem d1xR_else (k : Fin 5) (i : Fin 7) (hk : ¬ k = 4) :
    d1xR k i
      = ((dring0CLM (resSlot k) + dring0CLM ((resSlot k) + 1) - darc0CLM (resSlot k)) (Pi.single i 1)
        - (coord (resHub k)) (Pi.single i 1)) := by
  rw [d1xR, if_neg hk]

theorem d1xR_four (i : Fin 7) :
    d1xR 4 i
      = (((1 / 2 : ℝ) • (coord 4 + coord 5)) (Pi.single i 1) - (dring0CLM 6) (Pi.single i 1)) := by
  rw [d1xR, if_pos rfl]

theorem d1yR_else (k : Fin 5) (i : Fin 7) (hk : ¬ k = 4) :
    d1yR k i
      = ((dring1CLM (resSlot k) + dring1CLM ((resSlot k) + 1) - darc1CLM (resSlot k)) (Pi.single i 1)
        - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)) := by
  rw [d1yR, if_neg hk]

theorem d1yR_four (i : Fin 7) :
    d1yR 4 i
      = ((((1 / (2 * Real.sqrt Wp)) • ((2 * u0 6) • coord 6
            - (2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))) (Pi.single i 1))
        - (dring1CLM 6) (Pi.single i 1)) := by
  rw [d1yR, if_pos rfl]

/-! ## 2. 一阶桥：`k = 0..3`（`Apt = Uvec (resSlot k)`、`Bpt = hub`）与 `k = 4`（`wPoint`/`ringCenter 6`） -/

/-! ### 2.1 x 分量 -/

theorem fderiv_DeltaX_zero (i : Fin 7)
    (h0 : Wk 1 ≠ 0) (h1 : Wk ((1 : Fin 9) + 1) ≠ 0) :
    (fderiv ℝ (DeltaX 0) u0) (Pi.single i 1) = d1xR 0 i := by
  have hf : HasFDerivAt (DeltaX 0)
      ((dring0CLM 1 + dring0CLM (1 + 1) - darc0CLM 1) - coord 5) u0 :=
    (hasFDerivAt_Uvec0 1 h0 h1).sub hasFDerivAt_hub1_0
  rw [hf.fderiv, d1xR_else 0 i (by decide), sub_apply]
  simp only [resSlot, resHub]

theorem fderiv_DeltaX_one (i : Fin 7)
    (h0 : Wk 2 ≠ 0) (h1 : Wk ((2 : Fin 9) + 1) ≠ 0) :
    (fderiv ℝ (DeltaX 1) u0) (Pi.single i 1) = d1xR 1 i := by
  have hf : HasFDerivAt (DeltaX 1)
      ((dring0CLM 2 + dring0CLM (2 + 1) - darc0CLM 2) - coord 4) u0 :=
    (hasFDerivAt_Uvec0 2 h0 h1).sub hasFDerivAt_hub0_0
  rw [hf.fderiv, d1xR_else 1 i (by decide), sub_apply]
  simp only [resSlot, resHub]

theorem fderiv_DeltaX_two (i : Fin 7)
    (h0 : Wk 3 ≠ 0) (h1 : Wk ((3 : Fin 9) + 1) ≠ 0) :
    (fderiv ℝ (DeltaX 2) u0) (Pi.single i 1) = d1xR 2 i := by
  have hf : HasFDerivAt (DeltaX 2)
      ((dring0CLM 3 + dring0CLM (3 + 1) - darc0CLM 3) - coord 4) u0 :=
    (hasFDerivAt_Uvec0 3 h0 h1).sub hasFDerivAt_hub0_0
  rw [hf.fderiv, d1xR_else 2 i (by decide), sub_apply]
  simp only [resSlot, resHub]

theorem fderiv_DeltaX_three (i : Fin 7)
    (h0 : Wk 8 ≠ 0) (h1 : Wk ((8 : Fin 9) + 1) ≠ 0) :
    (fderiv ℝ (DeltaX 3) u0) (Pi.single i 1) = d1xR 3 i := by
  have hf : HasFDerivAt (DeltaX 3)
      ((dring0CLM 8 + dring0CLM (8 + 1) - darc0CLM 8) - coord 5) u0 :=
    (hasFDerivAt_Uvec0 8 h0 h1).sub hasFDerivAt_hub1_0
  rw [hf.fderiv, d1xR_else 3 i (by decide), sub_apply]
  simp only [resSlot, resHub]

theorem fderiv_DeltaX_four (i : Fin 7) (hW6 : Wk 6 ≠ 0) :
    (fderiv ℝ (DeltaX 4) u0) (Pi.single i 1) = d1xR 4 i := by
  have hf : HasFDerivAt (DeltaX 4)
      (((1 / 2 : ℝ) • (coord 4 + coord 5)) - dring0CLM 6) u0 :=
    hasFDerivAt_wPoint_0.sub (hasFDerivAt_ringCenter0 6 hW6)
  rw [hf.fderiv, d1xR_four i, sub_apply]

/-! ### 2.2 y 分量 -/

theorem fderiv_DeltaY_zero (i : Fin 7)
    (h0 : Wk 1 ≠ 0) (h1 : Wk ((1 : Fin 9) + 1) ≠ 0) :
    (fderiv ℝ (DeltaY 0) u0) (Pi.single i 1) = d1yR 0 i := by
  have hf : HasFDerivAt (DeltaY 0)
      ((dring1CLM 1 + dring1CLM (1 + 1) - darc1CLM 1) - 0) u0 :=
    (hasFDerivAt_Uvec1 1 h0 h1).sub hasFDerivAt_hub1_1
  rw [hf.fderiv, d1yR_else 0 i (by decide), sub_apply]
  simp only [resSlot, zero_apply]

theorem fderiv_DeltaY_one (i : Fin 7)
    (h0 : Wk 2 ≠ 0) (h1 : Wk ((2 : Fin 9) + 1) ≠ 0) :
    (fderiv ℝ (DeltaY 1) u0) (Pi.single i 1) = d1yR 1 i := by
  have hf : HasFDerivAt (DeltaY 1)
      ((dring1CLM 2 + dring1CLM (2 + 1) - darc1CLM 2) - 0) u0 :=
    (hasFDerivAt_Uvec1 2 h0 h1).sub hasFDerivAt_hub0_1
  rw [hf.fderiv, d1yR_else 1 i (by decide), sub_apply]
  simp only [resSlot, zero_apply]

theorem fderiv_DeltaY_two (i : Fin 7)
    (h0 : Wk 3 ≠ 0) (h1 : Wk ((3 : Fin 9) + 1) ≠ 0) :
    (fderiv ℝ (DeltaY 2) u0) (Pi.single i 1) = d1yR 2 i := by
  have hf : HasFDerivAt (DeltaY 2)
      ((dring1CLM 3 + dring1CLM (3 + 1) - darc1CLM 3) - 0) u0 :=
    (hasFDerivAt_Uvec1 3 h0 h1).sub hasFDerivAt_hub0_1
  rw [hf.fderiv, d1yR_else 2 i (by decide), sub_apply]
  simp only [resSlot, zero_apply]

theorem fderiv_DeltaY_three (i : Fin 7)
    (h0 : Wk 8 ≠ 0) (h1 : Wk ((8 : Fin 9) + 1) ≠ 0) :
    (fderiv ℝ (DeltaY 3) u0) (Pi.single i 1) = d1yR 3 i := by
  have hf : HasFDerivAt (DeltaY 3)
      ((dring1CLM 8 + dring1CLM (8 + 1) - darc1CLM 8) - 0) u0 :=
    (hasFDerivAt_Uvec1 8 h0 h1).sub hasFDerivAt_hub1_1
  rw [hf.fderiv, d1yR_else 3 i (by decide), sub_apply]
  simp only [resSlot, zero_apply]

theorem fderiv_DeltaY_four (i : Fin 7) (hW6 : Wk 6 ≠ 0) (hWp : Wp ≠ 0) :
    (fderiv ℝ (DeltaY 4) u0) (Pi.single i 1) = d1yR 4 i := by
  have hf : HasFDerivAt (DeltaY 4)
      (((1 / (2 * Real.sqrt Wp)) • ((2 * u0 6) • coord 6
          - (2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))) - dring1CLM 6) u0 :=
    (hasFDerivAt_wPoint_1 hWp).sub (hasFDerivAt_ringCenter1 6 hW6)
  rw [hf.fderiv, d1yR_four i, sub_apply]

/-! ### 2.3 分派（`fin_cases` + `exact`，defeq 容错） -/

theorem fderiv_DeltaX (k : Fin 5) (i : Fin 7)
    (h0 : Wk (resSlot k) ≠ 0) (h1 : Wk ((resSlot k) + 1) ≠ 0) (hW6 : Wk 6 ≠ 0) :
    (fderiv ℝ (DeltaX k) u0) (Pi.single i 1) = d1xR k i := by
  fin_cases k
  · exact fderiv_DeltaX_zero i h0 h1
  · exact fderiv_DeltaX_one i h0 h1
  · exact fderiv_DeltaX_two i h0 h1
  · exact fderiv_DeltaX_three i h0 h1
  · exact fderiv_DeltaX_four i hW6

theorem fderiv_DeltaY (k : Fin 5) (i : Fin 7)
    (h0 : Wk (resSlot k) ≠ 0) (h1 : Wk ((resSlot k) + 1) ≠ 0) (hW6 : Wk 6 ≠ 0)
    (hWp : Wp ≠ 0) :
    (fderiv ℝ (DeltaY k) u0) (Pi.single i 1) = d1yR k i := by
  fin_cases k
  · exact fderiv_DeltaY_zero i h0 h1
  · exact fderiv_DeltaY_one i h0 h1
  · exact fderiv_DeltaY_two i h0 h1
  · exact fderiv_DeltaY_three i h0 h1
  · exact fderiv_DeltaY_four i hW6 hWp

end HessSeam

end N11Formalization
