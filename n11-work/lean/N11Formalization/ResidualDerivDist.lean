/-
# `D` 阶段 3 —— **`dist` 节点**：残差分量 `dist (A_k z) (B_k z) − z₆` 的导数（第 1 层：表示层）

## ⚠ 文件头警语（防后来者再漏 —— 本工程已为此浪费过多轮）
**`B_k` 也是 `z` 的函数**，不是"给定点"：
* `hub0 u = !₂[u 4, 0]`、`hub1 u = !₂[u 5, 0]` ⇒ `∂(hub0ₓ)/∂z₄ = 1` / `∂(hub1ₓ)/∂z₅ = 1`，
  **坐标 1 的导数为 0**（具名：`hasFDerivAt_hub0_0/1`、`hasFDerivAt_hub1_0/1`）；
* `wPoint u = !₂[(u4+u5)/2, √((u6)² − ((u5−u4)/2)²)]` ⇒ **两个坐标都依赖 `z`**，
  且坐标 1 又是 `sqrt`（其 radicand `Wp` 的正性是**独立的**第二批正性，见 `hasFDerivAt_wPoint_1`）。
⇒ `Δx = A_x − B_x` 的导数里**必须显式出现** `−δ_{i,4}` / `−δ_{i,5}`（以及 `wPoint` 那一列的
`∓1/2` 与 `∂√…`）。**漏这项会让 `D` 整列偏 5 个数量级以上，且包含性检查仍可能通过** —— 故在此具名固定。

## 本层内容（**无大数算术**，纯表示层）
* `pad12_four/five/six`、`single_four/five/six`：具体下标上的取值；
* `hasFDerivAt_dist` / `fderiv_dist_single`：**通用** `dist (P z) (Q z)` 链式（四个坐标函数版）；
* `hasFDerivAt_hub0_0/1`、`hasFDerivAt_hub1_0/1`、`hasFDerivAt_wPoint_0/1`：`B_k` 随 `z` 变的具名导数；
* `fderiv_residualComp`：**通用残差分量节点**（`hfun : residualFun · k = dist(A,B) − z₆`）；
* **`fderiv_residual_0..4`**：5 个分量的完整标量导数读数（末项 `− (if i = 6 then 1 else 0)`
  就是残差里的 **`−R` 项**）。

**条件**（**显式前提，不假装无条件**）：`hg`（盒心两点分离，`0 ∉ [Δx²+Δy²]`）、
`Wk` 非零（`sqrt` 侧）、`Wp` 非零（`wPoint` 坐标 1 的 `sqrt` 侧）。
-/
import N11Formalization.ResidualDerivNode2

noncomputable section

namespace N11Formalization

open RatInterval

/-! ## 0. `pad12` / `Pi.single` 的具体下标取值 -/

theorem pad12_four (z : Fin 7 → ℝ) : pad12 z 4 = z 4 := by simp [pad12]

theorem pad12_five (z : Fin 7 → ℝ) : pad12 z 5 = z 5 := by simp [pad12]

theorem pad12_six (z : Fin 7 → ℝ) : pad12 z 6 = z 6 := by simp [pad12]

theorem single_four (i : Fin 7) :
    (Pi.single i 1 : Fin 7 → ℝ) 4 = (if i = 4 then 1 else 0 : ℝ) := by
  by_cases h : i = 4
  · subst h
    rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne (Ne.symm h), if_neg h]

theorem single_five (i : Fin 7) :
    (Pi.single i 1 : Fin 7 → ℝ) 5 = (if i = 5 then 1 else 0 : ℝ) := by
  by_cases h : i = 5
  · subst h
    rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne (Ne.symm h), if_neg h]

/-! ## 1. 通用 `dist (P z) (Q z)` 链式（四个坐标函数版） -/

/-- **通用 `dist` 链式**：`P₀,P₁,Q₀,Q₁` 在 `u0` 处可微、盒心两点分离 ⇒
`z ↦ √((P₀−Q₀)² + (P₁−Q₁)²)` 可微，导数为 `(1/(2√g)) • dg`，
`dg = (2Δx) • (P₀'−Q₀') + (2Δy) • (P₁'−Q₁')`。 -/
theorem hasFDerivAt_dist
    (Px Py Qx Qy : (Fin 7 → ℝ) → ℝ)
    (Px' Py' Qx' Qy' : (Fin 7 → ℝ) →L[ℝ] ℝ)
    (hPx : HasFDerivAt Px Px' u0) (hPy : HasFDerivAt Py Py' u0)
    (hQx : HasFDerivAt Qx Qx' u0) (hQy : HasFDerivAt Qy Qy' u0)
    (hg : (Px u0 - Qx u0) ^ 2 + (Py u0 - Qy u0) ^ 2 ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => Real.sqrt ((Px z - Qx z) ^ 2 + (Py z - Qy z) ^ 2))
      ((1 / (2 * Real.sqrt ((Px u0 - Qx u0) ^ 2 + (Py u0 - Qy u0) ^ 2)))
        • ((2 * (Px u0 - Qx u0)) • (Px' - Qx') + (2 * (Py u0 - Qy u0)) • (Py' - Qy'))) u0 := by
  have hX : HasFDerivAt (fun z : Fin 7 → ℝ => Px z - Qx z) (Px' - Qx') u0 := hPx.sub hQx
  have hY : HasFDerivAt (fun z : Fin 7 → ℝ => Py z - Qy z) (Py' - Qy') u0 := hPy.sub hQy
  have hx2 : HasFDerivAt (fun z : Fin 7 → ℝ => (Px z - Qx z) ^ 2)
      ((2 * (Px u0 - Qx u0)) • (Px' - Qx')) u0 := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using hX.pow 2
  have hy2 : HasFDerivAt (fun z : Fin 7 → ℝ => (Py z - Qy z) ^ 2)
      ((2 * (Py u0 - Qy u0)) • (Py' - Qy')) u0 := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using hY.pow 2
  exact (hx2.add hy2).sqrt hg

/-- `hasFDerivAt_dist` 沿 `Pi.single i 1` 的标量读数。 -/
theorem fderiv_dist_single
    (Px Py Qx Qy : (Fin 7 → ℝ) → ℝ)
    (Px' Py' Qx' Qy' : (Fin 7 → ℝ) →L[ℝ] ℝ)
    (hPx : HasFDerivAt Px Px' u0) (hPy : HasFDerivAt Py Py' u0)
    (hQx : HasFDerivAt Qx Qx' u0) (hQy : HasFDerivAt Qy Qy' u0)
    (hg : (Px u0 - Qx u0) ^ 2 + (Py u0 - Qy u0) ^ 2 ≠ 0) (i : Fin 7) :
    (fderiv ℝ (fun z : Fin 7 → ℝ =>
        Real.sqrt ((Px z - Qx z) ^ 2 + (Py z - Qy z) ^ 2)) u0) (Pi.single i 1)
      = (1 / (2 * Real.sqrt ((Px u0 - Qx u0) ^ 2 + (Py u0 - Qy u0) ^ 2)))
          * (2 * (Px u0 - Qx u0) * (Px' (Pi.single i 1) - Qx' (Pi.single i 1))
            + 2 * (Py u0 - Qy u0) * (Py' (Pi.single i 1) - Qy' (Pi.single i 1))) := by
  rw [(hasFDerivAt_dist Px Py Qx Qy Px' Py' Qx' Qy' hPx hPy hQx hQy hg).fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]

/-! ## 2. `B_k` 随 `z` 变：具名导数 -/

theorem hasFDerivAt_hub0_0 :
    HasFDerivAt (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0) (coord 4) u0 := by
  have h : (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0) = fun z => z 4 := by
    funext z
    rw [hub0_coord0, pad12_four]
  rw [h]
  exact ContinuousLinearMap.hasFDerivAt (f := coord 4) (x := u0)

theorem hasFDerivAt_hub1_0 :
    HasFDerivAt (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0) (coord 5) u0 := by
  have h : (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0) = fun z => z 5 := by
    funext z
    rw [hub1_coord0, pad12_five]
  rw [h]
  exact ContinuousLinearMap.hasFDerivAt (f := coord 5) (x := u0)

theorem hasFDerivAt_hub0_1 :
    HasFDerivAt (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1)
      (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) u0 := by
  have h : (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1) = fun _ => (0 : ℝ) := by
    funext z
    rw [hub0_coord1]
  rw [h]
  exact hasFDerivAt_const (0 : ℝ) u0

theorem hasFDerivAt_hub1_1 :
    HasFDerivAt (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1)
      (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) u0 := by
  have h : (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1) = fun _ => (0 : ℝ) := by
    funext z
    rw [hub1_coord1]
  rw [h]
  exact hasFDerivAt_const (0 : ℝ) u0

/-! ## 3. `wPoint` 的两个坐标（**都**依赖 `z`；坐标 1 又是 `sqrt`） -/

/-- `wPoint` 坐标 1 的 radicand 在盒心处的值（= `(z6)² − ((z5−z4)/2)²`）。 -/
def Wp : ℝ := (u0 6) ^ 2 - ((u0 5 - u0 4) / 2) ^ 2

theorem hasFDerivAt_wPoint_0 :
    HasFDerivAt (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0)
      ((1 / 2 : ℝ) • (coord 4 + coord 5)) u0 := by
  have h : (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0)
      = fun z => (1 / 2 : ℝ) * (z 4 + z 5) := by
    funext z
    rw [wPoint_coord0, pad12_four, pad12_five]
    ring
  rw [h]
  have h45 : HasFDerivAt (fun z : Fin 7 → ℝ => z 4 + z 5) (coord 4 + coord 5) u0 :=
    (ContinuousLinearMap.hasFDerivAt (f := coord 4) (x := u0)).add
      (ContinuousLinearMap.hasFDerivAt (f := coord 5) (x := u0))
  exact h45.const_mul (1 / 2)

theorem hasFDerivAt_wPoint_1 (hWp : Wp ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1)
      ((1 / (2 * Real.sqrt Wp)) • ((2 * u0 6) • coord 6
        - (2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))) u0 := by
  have h6 : HasFDerivAt (fun z : Fin 7 → ℝ => z 6) (coord 6) u0 :=
    ContinuousLinearMap.hasFDerivAt (f := coord 6) (x := u0)
  have h6sq : HasFDerivAt (fun z : Fin 7 → ℝ => (z 6) ^ 2) ((2 * u0 6) • coord 6) u0 := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using h6.pow 2
  have h54 : HasFDerivAt (fun z : Fin 7 → ℝ => z 5 - z 4) (coord 5 - coord 4) u0 :=
    (ContinuousLinearMap.hasFDerivAt (f := coord 5) (x := u0)).sub
      (ContinuousLinearMap.hasFDerivAt (f := coord 4) (x := u0))
  have hhalf : HasFDerivAt (fun z : Fin 7 → ℝ => (z 5 - z 4) / 2)
      ((1 / 2 : ℝ) • (coord 5 - coord 4)) u0 := by
    have he : (fun z : Fin 7 → ℝ => (z 5 - z 4) / 2)
        = fun z => (1 / 2 : ℝ) * (z 5 - z 4) := by
      funext z
      ring
    rw [he]
    exact h54.const_mul (1 / 2)
  have hhalf2 : HasFDerivAt (fun z : Fin 7 → ℝ => ((z 5 - z 4) / 2) ^ 2)
      ((2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))) u0 := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using hhalf.pow 2
  have hrad : HasFDerivAt (fun z : Fin 7 → ℝ => (z 6) ^ 2 - ((z 5 - z 4) / 2) ^ 2)
      ((2 * u0 6) • coord 6
        - (2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))) u0 :=
    h6sq.sub hhalf2
  have hfun : (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1)
      = fun z => Real.sqrt ((z 6) ^ 2 - ((z 5 - z 4) / 2) ^ 2) := by
    funext z
    rw [wPoint_coord1, pad12_six, pad12_five, pad12_four]
  rw [hfun]
  exact hrad.sqrt hWp

/-! ## 4. 通用残差分量节点 -/

/-- **通用残差分量节点**：`f_k z = dist (A (pad12 z)) (B (pad12 z)) − z₆`
（由 `hfun` 提供该表示），四个坐标导数 + 盒心两点分离 ⇒ `f_k` 沿 `Pi.single i 1` 的完整标量导数。
末项 `− (if i = 6 then 1 else 0)` 就是**残差里的 `−R` 项**。 -/
theorem fderiv_residualComp
    (k : Fin 5) (A B : (Fin 12 → ℝ) → Point)
    (A0' A1' B0' B1' : (Fin 7 → ℝ) →L[ℝ] ℝ)
    (hA0 : HasFDerivAt (fun z : Fin 7 → ℝ => (A (pad12 z)).ofLp 0) A0' u0)
    (hA1 : HasFDerivAt (fun z : Fin 7 → ℝ => (A (pad12 z)).ofLp 1) A1' u0)
    (hB0 : HasFDerivAt (fun z : Fin 7 → ℝ => (B (pad12 z)).ofLp 0) B0' u0)
    (hB1 : HasFDerivAt (fun z : Fin 7 → ℝ => (B (pad12 z)).ofLp 1) B1' u0)
    (hfun : ∀ z : Fin 7 → ℝ, residualFun z k = dist (A (pad12 z)) (B (pad12 z)) - z 6)
    (hg : ((A (pad12 u0)).ofLp 0 - (B (pad12 u0)).ofLp 0) ^ 2
        + ((A (pad12 u0)).ofLp 1 - (B (pad12 u0)).ofLp 1) ^ 2 ≠ 0)
    (i : Fin 7) :
    (fderiv ℝ (fun z : Fin 7 → ℝ => residualFun z k) u0) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((A (pad12 u0)).ofLp 0 - (B (pad12 u0)).ofLp 0) ^ 2
              + ((A (pad12 u0)).ofLp 1 - (B (pad12 u0)).ofLp 1) ^ 2)))
          * (2 * ((A (pad12 u0)).ofLp 0 - (B (pad12 u0)).ofLp 0)
              * (A0' (Pi.single i 1) - B0' (Pi.single i 1))
            + 2 * ((A (pad12 u0)).ofLp 1 - (B (pad12 u0)).ofLp 1)
              * (A1' (Pi.single i 1) - B1' (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) := by
  have hd := hasFDerivAt_dist (fun z : Fin 7 → ℝ => (A (pad12 z)).ofLp 0)
    (fun z : Fin 7 → ℝ => (A (pad12 z)).ofLp 1)
    (fun z : Fin 7 → ℝ => (B (pad12 z)).ofLp 0)
    (fun z : Fin 7 → ℝ => (B (pad12 z)).ofLp 1) A0' A1' B0' B1' hA0 hA1 hB0 hB1 hg
  have hz : HasFDerivAt (fun z : Fin 7 → ℝ => z 6) (coord 6) u0 :=
    ContinuousLinearMap.hasFDerivAt (f := coord 6) (x := u0)
  -- 显式写成 λ 形式（`hd.sub hz` 给的是「函数级」减法 `(fun z => √…) - fun z => z 6`，
  -- 与目标里的 λ 形式只差 eta ⇒ 用 defeq 容错，**不要** `simpa using`）
  have htot : HasFDerivAt (fun z : Fin 7 → ℝ =>
      Real.sqrt (((A (pad12 z)).ofLp 0 - (B (pad12 z)).ofLp 0) ^ 2
        + ((A (pad12 z)).ofLp 1 - (B (pad12 z)).ofLp 1) ^ 2) - z 6)
      (((1 / (2 * Real.sqrt (((A (pad12 u0)).ofLp 0 - (B (pad12 u0)).ofLp 0) ^ 2
              + ((A (pad12 u0)).ofLp 1 - (B (pad12 u0)).ofLp 1) ^ 2)))
          • ((2 * ((A (pad12 u0)).ofLp 0 - (B (pad12 u0)).ofLp 0)) • (A0' - B0')
            + (2 * ((A (pad12 u0)).ofLp 1 - (B (pad12 u0)).ofLp 1)) • (A1' - B1')))
        - coord 6) u0 :=
    hd.sub hz
  have hEq : (fun z : Fin 7 → ℝ => residualFun z k)
      = fun z : Fin 7 → ℝ => Real.sqrt (((A (pad12 z)).ofLp 0 - (B (pad12 z)).ofLp 0) ^ 2
          + ((A (pad12 z)).ofLp 1 - (B (pad12 z)).ofLp 1) ^ 2) - z 6 := by
    funext z
    rw [hfun z, dist_point_eq_sqrt]
  rw [hEq, htot.fderiv]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, coord_six_apply_single i]

/-! ## 5. 五个分量 -/

theorem fderiv_residual_0 (i : Fin 7) (hW1 : Wk 1 ≠ 0) (hW2 : Wk (1 + 1) ≠ 0)
    (hg : ((Uvec (pad12 u0) 1).ofLp 0 - (hub1 (pad12 u0)).ofLp 0) ^ 2
        + ((Uvec (pad12 u0) 1).ofLp 1 - (hub1 (pad12 u0)).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun z : Fin 7 → ℝ => residualFun z 0) u0) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((Uvec (pad12 u0) 1).ofLp 0 - (hub1 (pad12 u0)).ofLp 0) ^ 2
              + ((Uvec (pad12 u0) 1).ofLp 1 - (hub1 (pad12 u0)).ofLp 1) ^ 2)))
          * (2 * ((Uvec (pad12 u0) 1).ofLp 0 - (hub1 (pad12 u0)).ofLp 0)
              * ((dring0CLM 1 + dring0CLM (1 + 1) - darc0CLM 1) (Pi.single i 1)
                - (coord 5) (Pi.single i 1))
            + 2 * ((Uvec (pad12 u0) 1).ofLp 1 - (hub1 (pad12 u0)).ofLp 1)
              * ((dring1CLM 1 + dring1CLM (1 + 1) - darc1CLM 1) (Pi.single i 1)
                - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) :=
  fderiv_residualComp 0 (fun u => Uvec u 1) (fun u => hub1 u)
    (dring0CLM 1 + dring0CLM (1 + 1) - darc0CLM 1)
    (dring1CLM 1 + dring1CLM (1 + 1) - darc1CLM 1)
    (coord 5) 0
    (hasFDerivAt_Uvec0 1 hW1 hW2) (hasFDerivAt_Uvec1 1 hW1 hW2)
    hasFDerivAt_hub1_0 hasFDerivAt_hub1_1
    (fun z => by
      have h1 : residualFun z 0
          = dist (Uvec (pad12 z) 1) (hub1 (pad12 z)) - pad12 z 6 := rfl
      rw [h1, pad12_six])
    hg i

theorem fderiv_residual_1 (i : Fin 7) (hW2 : Wk 2 ≠ 0) (hW3 : Wk (2 + 1) ≠ 0)
    (hg : ((Uvec (pad12 u0) 2).ofLp 0 - (hub0 (pad12 u0)).ofLp 0) ^ 2
        + ((Uvec (pad12 u0) 2).ofLp 1 - (hub0 (pad12 u0)).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun z : Fin 7 → ℝ => residualFun z 1) u0) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((Uvec (pad12 u0) 2).ofLp 0 - (hub0 (pad12 u0)).ofLp 0) ^ 2
              + ((Uvec (pad12 u0) 2).ofLp 1 - (hub0 (pad12 u0)).ofLp 1) ^ 2)))
          * (2 * ((Uvec (pad12 u0) 2).ofLp 0 - (hub0 (pad12 u0)).ofLp 0)
              * ((dring0CLM 2 + dring0CLM (2 + 1) - darc0CLM 2) (Pi.single i 1)
                - (coord 4) (Pi.single i 1))
            + 2 * ((Uvec (pad12 u0) 2).ofLp 1 - (hub0 (pad12 u0)).ofLp 1)
              * ((dring1CLM 2 + dring1CLM (2 + 1) - darc1CLM 2) (Pi.single i 1)
                - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) :=
  fderiv_residualComp 1 (fun u => Uvec u 2) (fun u => hub0 u)
    (dring0CLM 2 + dring0CLM (2 + 1) - darc0CLM 2)
    (dring1CLM 2 + dring1CLM (2 + 1) - darc1CLM 2)
    (coord 4) 0
    (hasFDerivAt_Uvec0 2 hW2 hW3) (hasFDerivAt_Uvec1 2 hW2 hW3)
    hasFDerivAt_hub0_0 hasFDerivAt_hub0_1
    (fun z => by
      have h1 : residualFun z 1
          = dist (Uvec (pad12 z) 2) (hub0 (pad12 z)) - pad12 z 6 := rfl
      rw [h1, pad12_six])
    hg i

theorem fderiv_residual_2 (i : Fin 7) (hW3 : Wk 3 ≠ 0) (hW4 : Wk (3 + 1) ≠ 0)
    (hg : ((Uvec (pad12 u0) 3).ofLp 0 - (hub0 (pad12 u0)).ofLp 0) ^ 2
        + ((Uvec (pad12 u0) 3).ofLp 1 - (hub0 (pad12 u0)).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun z : Fin 7 → ℝ => residualFun z 2) u0) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((Uvec (pad12 u0) 3).ofLp 0 - (hub0 (pad12 u0)).ofLp 0) ^ 2
              + ((Uvec (pad12 u0) 3).ofLp 1 - (hub0 (pad12 u0)).ofLp 1) ^ 2)))
          * (2 * ((Uvec (pad12 u0) 3).ofLp 0 - (hub0 (pad12 u0)).ofLp 0)
              * ((dring0CLM 3 + dring0CLM (3 + 1) - darc0CLM 3) (Pi.single i 1)
                - (coord 4) (Pi.single i 1))
            + 2 * ((Uvec (pad12 u0) 3).ofLp 1 - (hub0 (pad12 u0)).ofLp 1)
              * ((dring1CLM 3 + dring1CLM (3 + 1) - darc1CLM 3) (Pi.single i 1)
                - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) :=
  fderiv_residualComp 2 (fun u => Uvec u 3) (fun u => hub0 u)
    (dring0CLM 3 + dring0CLM (3 + 1) - darc0CLM 3)
    (dring1CLM 3 + dring1CLM (3 + 1) - darc1CLM 3)
    (coord 4) 0
    (hasFDerivAt_Uvec0 3 hW3 hW4) (hasFDerivAt_Uvec1 3 hW3 hW4)
    hasFDerivAt_hub0_0 hasFDerivAt_hub0_1
    (fun z => by
      have h1 : residualFun z 2
          = dist (Uvec (pad12 z) 3) (hub0 (pad12 z)) - pad12 z 6 := rfl
      rw [h1, pad12_six])
    hg i

theorem fderiv_residual_3 (i : Fin 7) (hW8 : Wk 8 ≠ 0) (hW0 : Wk (8 + 1) ≠ 0)
    (hg : ((Uvec (pad12 u0) 8).ofLp 0 - (hub1 (pad12 u0)).ofLp 0) ^ 2
        + ((Uvec (pad12 u0) 8).ofLp 1 - (hub1 (pad12 u0)).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun z : Fin 7 → ℝ => residualFun z 3) u0) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((Uvec (pad12 u0) 8).ofLp 0 - (hub1 (pad12 u0)).ofLp 0) ^ 2
              + ((Uvec (pad12 u0) 8).ofLp 1 - (hub1 (pad12 u0)).ofLp 1) ^ 2)))
          * (2 * ((Uvec (pad12 u0) 8).ofLp 0 - (hub1 (pad12 u0)).ofLp 0)
              * ((dring0CLM 8 + dring0CLM (8 + 1) - darc0CLM 8) (Pi.single i 1)
                - (coord 5) (Pi.single i 1))
            + 2 * ((Uvec (pad12 u0) 8).ofLp 1 - (hub1 (pad12 u0)).ofLp 1)
              * ((dring1CLM 8 + dring1CLM (8 + 1) - darc1CLM 8) (Pi.single i 1)
                - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) :=
  fderiv_residualComp 3 (fun u => Uvec u 8) (fun u => hub1 u)
    (dring0CLM 8 + dring0CLM (8 + 1) - darc0CLM 8)
    (dring1CLM 8 + dring1CLM (8 + 1) - darc1CLM 8)
    (coord 5) 0
    (hasFDerivAt_Uvec0 8 hW8 hW0) (hasFDerivAt_Uvec1 8 hW8 hW0)
    hasFDerivAt_hub1_0 hasFDerivAt_hub1_1
    (fun z => by
      have h1 : residualFun z 3
          = dist (Uvec (pad12 z) 8) (hub1 (pad12 z)) - pad12 z 6 := rfl
      rw [h1, pad12_six])
    hg i

theorem fderiv_residual_4 (i : Fin 7) (hW6 : Wk 6 ≠ 0) (hWp : Wp ≠ 0)
    (hg : ((wPoint (pad12 u0)).ofLp 0 - (ringCenter (pad12 u0) 6).ofLp 0) ^ 2
        + ((wPoint (pad12 u0)).ofLp 1 - (ringCenter (pad12 u0) 6).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun z : Fin 7 → ℝ => residualFun z 4) u0) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((wPoint (pad12 u0)).ofLp 0 - (ringCenter (pad12 u0) 6).ofLp 0) ^ 2
              + ((wPoint (pad12 u0)).ofLp 1 - (ringCenter (pad12 u0) 6).ofLp 1) ^ 2)))
          * (2 * ((wPoint (pad12 u0)).ofLp 0 - (ringCenter (pad12 u0) 6).ofLp 0)
              * (((1 / 2 : ℝ) • (coord 4 + coord 5)) (Pi.single i 1) - dring0CLM 6 (Pi.single i 1))
            + 2 * ((wPoint (pad12 u0)).ofLp 1 - (ringCenter (pad12 u0) 6).ofLp 1)
              * (((1 / (2 * Real.sqrt Wp)) • ((2 * u0 6) • coord 6
                    - (2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))))
                  (Pi.single i 1) - dring1CLM 6 (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) :=
  fderiv_residualComp 4 (fun u => wPoint u) (fun u => ringCenter u 6)
    ((1 / 2 : ℝ) • (coord 4 + coord 5))
    ((1 / (2 * Real.sqrt Wp)) • ((2 * u0 6) • coord 6
      - (2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))))
    (dring0CLM 6) (dring1CLM 6)
    hasFDerivAt_wPoint_0 (hasFDerivAt_wPoint_1 hWp)
    (hasFDerivAt_ringCenter0' 6 hW6) (hasFDerivAt_ringCenter1' 6 hW6)
    (fun z => by
      have h1 : residualFun z 4
          = dist (wPoint (pad12 z)) (ringCenter (pad12 z) 6) - pad12 z 6 := rfl
      rw [h1, pad12_six])
    hg i

end N11Formalization
