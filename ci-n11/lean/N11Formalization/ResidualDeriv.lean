import N11Formalization.ResidualInterval
import N11Formalization.SmoothnessC2

/-!
# `D` 的**线性脊柱**：`u0` + `angleVec`/`thetaOf` 的整数 `fderiv` 矩阵

**目标对象**（`FmAssembly` 的 `hD`）：
`D : Fin 5 → Fin 7 → RatInterval`，`D k i ∋ fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1) k`，
`z = (a0,a1,a2,a3,y0,y1,R)`（`Fin 7`）、`k` 是 `f` 的 5 个分量。

**本文件（阶段 1：线性脊柱）** 交付可复核的最小单元：

* `u0 := first7 cCertR`（证书盒心的前 7 坐标；后 5 个是乘子 `λ`，不参与几何）；
* `dAngle : Fin 9 → Fin 7 → ℤ`（`∂a_j/∂z_i`，**整数**；`angleVec` 对 `z` 仿射）；
* `dThetaCoef : Fin 9 → Fin 9 → ℤ`（`thetaOf` 的系数）+ `dThetaSum`（**派生**的链式矩阵
  `∑_l dThetaCoef j l · dAngle l i`）+ `dTheta`（表）+ `dTheta_eq_dThetaSum`（表 = 派生，**用内核核对**）；
* `fderiv_angleVec` / `fderiv_thetaOf`（在 `u0` 处、沿 `Pi.single i 1` 的 `fderiv` 矩阵）；
* `dTheta_one_three_eq_zero` + `fderiv_thetaOf_1_3`：**结构性零的具名命中引理**——
  `∂θ₁/∂a₃ = 0`，因为 `a₄ = π − 2(a₀+a₁+a₂+a₃)` 的 `−2` 与 `θ₁ = −(a₁+2a₂+2a₃+a₄)` 里 `a₄`
  的系数 `−1` 精确相消。它同时是**负对照**（任何链式记账写错这条会先炸）。

**阶段 2/3（TODO，见文件末）**：非线性链 `rhoK` → `ringCenter`/`arcEnd` → `Uvec` →
`distInterval` → 残差 `−R`；每节点独立引理 + **逐节点**对
`evidence/box-rstar/fm_cert_values.out.txt` 的对应项做数值交叉核对；最后 5×7 全表装配。

**读数纪律（Lead R26/C1051）**：外部目标值**只能用来发现"我做错了"，不得用来收紧端点**
（`hD` 是 `Mem` 包络前提：区间偏窄**不是** sound 的方向）。该表的 `k=2` 列与另 4 格
（`(i=3,k=1)`、`(i=6,k=1)`、`(i=6,k=3)`）**已知有数值精度缺陷**（`sqrt` 近分支点 ⇒
Richardson 截断不可忽略），这 8 格**不得**作为验收判据；27 格可继续用（相对差 ≤ 4e-9）。

**端点来源（不变量，须全文件保持）**：`D`（及其所有中间节点）的 `Mem` 一律由本文件
**树行走的包含性引理**给出（形如 `fderiv_*`/`*_mem`/`eval_sound`），**不得引用任何数值表常数**。
外部表（`evidence/box-rstar/fm_cert_values.out.txt`、`evidence/interval-ad/dz_iv_enclosure.json`）
只用于：① 定位错误（**相交性**检查，无容差：两者都严格含真值 ⇒ 必须相交）；② 判断宽度余量。
**禁止**为了通过检查而把端点对齐到外部表的值（`interval-ad` 会查"端点恰等于表值"的红旗）。
-/

-- TODO（阶段 2）：`rhoK` 的 z-导数（`cos a_k`、`sin a_k`、`√W`、`W = R² − sin²a_k`，
--   `1/(2√W)`、`R/√W` 项；窗口内 `cos` 用 `cosWin`/`cosWinLag`，窗口外回退支计入宽度；
--   **radicand 近分支点**：盒心 `k=4` 的 `W ≈ 1.093e-3` ⇒ `1/(2√W) ≈ 15`，
--   该列宽度会放大 —— 请显式确认宽度预算，不行就如实报"方法极限"）；
-- TODO（阶段 3）：`ringCenter`/`arcEnd` 的乘积/链式 → `Uvec` 求和 → `distInterval`
--   （`√(Δx²+Δy²)` 链式）→ 残差的 `−R`（`i=6` 贡献 `−1`）→ 5×7 全表 `D`；
-- 每完成一个节点：`lake build` exit 0 / 0 warning，并对该节点做**相交性**错误探测。
-- 落地后按 `interval-ad` 的输入格式导出（JSON `{"entries":[{k,i,lo,hi}]}`，
-- 精确有理 `"num/den"`；或文本 `k i lo_num lo_den hi_num hi_den`）。

noncomputable section

-- 风格抑制：本文件的证明里有若干"单目标分支"上的 `<;>` 链（`linter.unnecessarySeqFocus`
-- 建议改成 `;`，但 `;` 会在 `simp` 已闭合的分支上报 "no goals"，故保留 `<;>`）。
set_option linter.unnecessarySeqFocus false

namespace N11Formalization

open RatInterval

/-- 证书盒心的前 7 个坐标 `z = (a0,a1,a2,a3,y0,y1,R)`。 -/
def u0 : Fin 7 → ℝ := first7 cCertR

/-- `∂a_j/∂z_i`（`Fin 9` 角槽 × `Fin 7` z 坐标），整数矩阵。 -/
def dAngle : Fin 9 → Fin 7 → ℤ
  | 0, i => if i = 0 then 1 else 0
  | 1, i => if i = 1 then 1 else 0
  | 2, i => if i = 2 then 1 else 0
  | 3, i => if i = 3 then 1 else 0
  | 4, i => if (i : ℕ) < 4 then -2 else 0
  | 5, i => if i = 3 then 1 else 0
  | 6, i => if i = 2 then 1 else 0
  | 7, i => if i = 1 then 1 else 0
  | 8, i => if i = 0 then 1 else 0

/-- `thetaOf` 的系数矩阵（`θ_j = ∑_l dThetaCoef j l · A_l`；逐字来自 `thetaOf` 的定义）。 -/
def dThetaCoef : Fin 9 → Fin 9 → ℤ
  | 0, l => if l = 0 then -1 else if l = 1 then -2 else if l = 2 then -2 else
      if l = 3 then -2 else if l = 4 then -1 else 0
  | 1, l => if l = 1 then -1 else if l = 2 then -2 else if l = 3 then -2 else
      if l = 4 then -1 else 0
  | 2, l => if l = 2 then -1 else if l = 3 then -2 else if l = 4 then -1 else 0
  | 3, l => if l = 3 then -1 else if l = 4 then -1 else 0
  | 4, _ => 0
  | 5, l => if l = 4 then 1 else if l = 5 then 1 else 0
  | 6, l => if l = 4 then 1 else if l = 5 then 2 else if l = 6 then 1 else 0
  | 7, l => if l = 4 then 1 else if l = 5 then 2 else if l = 6 then 2 else
      if l = 7 then 1 else 0
  | 8, l => if l = 4 then 1 else if l = 5 then 2 else if l = 6 then 2 else
      if l = 7 then 2 else if l = 8 then 1 else 0

/-- **派生**的链式矩阵：`∂θ_j/∂z_i = ∑_l (∂θ_j/∂A_l)(∂A_l/∂z_i)`。 -/
def dThetaSum : Fin 9 → Fin 7 → ℤ := fun j i => ∑ l : Fin 9, dThetaCoef j l * dAngle l i

/-- `∂θ_j/∂z_i` 的显式表（**由 `dTheta_eq_dThetaSum` 内核核对为 `dThetaSum`**，非手写断言）。 -/
def dTheta : Fin 9 → Fin 7 → ℤ
  | 0, i => if i = 0 then 1 else 0
  | 1, i => if i = 0 then 2 else if i = 1 then 1 else 0
  | 2, i => if i = 0 then 2 else if i = 1 then 2 else if i = 2 then 1 else 0
  | 3, i => if i = 0 then 2 else if i = 1 then 2 else if i = 2 then 2 else if i = 3 then 1 else 0
  | 4, _ => 0
  | 5, i => if i = 0 then -2 else if i = 1 then -2 else if i = 2 then -2 else
      if i = 3 then -1 else 0
  | 6, i => if i = 0 then -2 else if i = 1 then -2 else if i = 2 then -1 else 0
  | 7, i => if i = 0 then -2 else if i = 1 then -1 else 0
  | 8, i => if i = 0 then -1 else 0

/-- `Fin 7` 上的字面量求和展开（`∑ i, f i = f 0 + (f 1 + ... + f 6)`）。 -/
theorem sum_seven (f : Fin 7 → ℝ) :
    ∑ i : Fin 7, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp [Fin.sum_univ_succ]
  ring

/-- `Fin 9` 上的字面量求和展开。 -/
theorem sum_nine (f : Fin 9 → ℝ) :
    ∑ i : Fin 9, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp [Fin.sum_univ_succ]
  ring

/-- `dTheta` 表 = 链式派生（63 项逐项内核核对）。 -/
theorem dTheta_eq_dThetaSum : dTheta = dThetaSum := by
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [dTheta, dThetaSum, dThetaCoef, dAngle, Fin.sum_univ_succ]

/-- `thetaOf` 逐槽是 `A` 的整数线性组合（系数 = `dThetaCoef`）。 -/
theorem thetaOf_eq_linear (A : Fin 9 → ℝ) (j : Fin 9) :
    thetaOf A j = ∑ l : Fin 9, ((dThetaCoef j l : ℤ) : ℝ) * A l := by
  fin_cases j <;> simp [thetaOf, dThetaCoef, Fin.sum_univ_succ] <;> ring

/-- `Fin 7` 上的坐标线性泛函（自己做，避免 `ContinuousLinearMap.proj` 的类型类推断挂住）。 -/
def coord (i : Fin 7) : (Fin 7 → ℝ) →L[ℝ] ℝ where
  toFun := fun v => v i
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- 坐标投影的 `fderiv`（沿任意方向 `v`）。 -/
theorem fderiv_coord (i : Fin 7) (v : Fin 7 → ℝ) :
    fderiv ℝ (fun z : Fin 7 → ℝ => z i) u0 v = v i := by
  have h : (fun z : Fin 7 → ℝ => z i) = ⇑(coord i) := rfl
  rw [h, (ContinuousLinearMap.hasFDerivAt (f := coord i) (x := u0)).fderiv]
  rfl

/-- 一般线性组合的 `fderiv`（在 `u0` 处）。 -/
theorem fderiv_linComb (a : Fin 7 → ℝ) (v : Fin 7 → ℝ) :
    fderiv ℝ (fun z : Fin 7 → ℝ => ∑ i : Fin 7, a i * z i) u0 v = ∑ i : Fin 7, a i * v i := by
  have h : HasFDerivAt (fun z : Fin 7 → ℝ => ∑ i : Fin 7, a i * z i)
      (∑ i : Fin 7, a i • coord i) u0 := by
    rw [show (fun z : Fin 7 → ℝ => ∑ i : Fin 7, a i * z i)
        = ∑ i : Fin 7, fun z : Fin 7 → ℝ => a i * z i from rfl]
    refine HasFDerivAt.sum fun i _ => ?_
    have hc : HasFDerivAt (fun z : Fin 7 → ℝ => a i * z i) (a i • coord i) u0 := by
      have h1 : HasFDerivAt (⇑(coord i)) (coord i) u0 :=
        ContinuousLinearMap.hasFDerivAt (f := coord i) (x := u0)
      exact h1.const_mul (a i)
    exact hc
  rw [h.fderiv, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_apply, smul_eq_mul]
  rfl

/-- `∑ i, a i * (Pi.single i₀ 1) i = a i₀`。 -/
theorem sum_mul_single (a : Fin 7 → ℝ) (i₀ : Fin 7) :
    ∑ i : Fin 7, a i * (Pi.single i₀ 1 : Fin 7 → ℝ) i = a i₀ := by
  classical
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

/-- `angleVec (pad12 z)` 逐槽对 `z` **仿射**。 -/
theorem angleVec_pad12_affine (j : Fin 9) (z : Fin 7 → ℝ) :
    angleVec (pad12 z) j = angleVec (pad12 0) j + ∑ i : Fin 7, (dAngle j i : ℝ) * z i := by
  rw [sum_seven]
  fin_cases j <;> simp [angleVec, pad12, dAngle] <;> ring

/-- **`angleVec` 的 `fderiv` 矩阵**（在 `u0` 处，沿 `Pi.single i 1`）。 -/
theorem fderiv_angleVec (j : Fin 9) (i : Fin 7) :
    fderiv ℝ (fun z : Fin 7 → ℝ => angleVec (pad12 z) j) u0 (Pi.single i 1)
      = (dAngle j i : ℝ) := by
  have h : (fun z : Fin 7 → ℝ => angleVec (pad12 z) j)
      = fun z => angleVec (pad12 0) j + ∑ i' : Fin 7, (dAngle j i' : ℝ) * z i' := by
    funext z
    exact angleVec_pad12_affine j z
  rw [h, fderiv_const_add, fderiv_linComb, sum_mul_single]

/-- `thetaOf (angleVec (pad12 z))` 逐槽对 `z` **仿射**（方向 = `dTheta`）。 -/
theorem thetaOf_angleVec_affine (j : Fin 9) (z : Fin 7 → ℝ) :
    thetaOf (angleVec (pad12 z)) j
      = thetaOf (angleVec (pad12 0)) j + ∑ i : Fin 7, (dTheta j i : ℝ) * z i := by
  rw [sum_seven]
  fin_cases j <;> simp [thetaOf, angleVec, pad12, dTheta] <;> ring

/-- **`thetaOf ∘ angleVec ∘ pad12` 的 `fderiv` 矩阵**（在 `u0` 处，沿 `Pi.single i 1`）。 -/
theorem fderiv_thetaOf (j : Fin 9) (i : Fin 7) :
    fderiv ℝ (fun z : Fin 7 → ℝ => thetaOf (angleVec (pad12 z)) j) u0 (Pi.single i 1)
      = (dTheta j i : ℝ) := by
  have h : (fun z : Fin 7 → ℝ => thetaOf (angleVec (pad12 z)) j)
      = fun z => thetaOf (angleVec (pad12 0)) j + ∑ i' : Fin 7, (dTheta j i' : ℝ) * z i' := by
    funext z
    exact thetaOf_angleVec_affine j z
  rw [h, fderiv_const_add, fderiv_linComb, sum_mul_single]

/-- **结构性零（免费独立校验点）**：`∂θ₁/∂z₃ = 0`。
证明走**链式派生**（`dThetaSum`）：`θ₁` 只经 `A₁,A₂,A₃,A₄` 依赖 `a₃`，而
`dThetaCoef 1 3 · dAngle 3 3 + dThetaCoef 1 4 · dAngle 4 3 = (−1)·(1) + (−2)·(1) = −3`？
—— 不：`dAngle 4 3 = −2`（`a₄ = π − 2Σ`），故 `(−2)·1 + (−1)·(−2) = 0`。
即 `a₄` 的 `−2` 与 `θ₁` 中 `a₄` 系数 `−1` 精确相消。 -/
theorem dTheta_one_three_eq_zero : dTheta 1 3 = 0 := by
  rw [dTheta_eq_dThetaSum]
  simp [dThetaSum, dThetaCoef, dAngle, Fin.sum_univ_succ]

/-- 同款（`ℝ` 侧读数）：`∂θ₁/∂a₃ = 0`。 -/
theorem fderiv_thetaOf_1_3 :
    fderiv ℝ (fun z : Fin 7 → ℝ => thetaOf (angleVec (pad12 z)) 1) u0 (Pi.single 3 1) = 0 := by
  rw [fderiv_thetaOf, dTheta_one_three_eq_zero]
  norm_num

end N11Formalization
