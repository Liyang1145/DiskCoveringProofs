import N11Formalization.ResidualDerivJT
import N11Formalization.ResidualDerivD

/-!
# `Hess`（KKT×z 二阶块）的区间装配（H3）与 `hH` 收口（H4）

**对象**（`ResidualDerivJT.lean` 冻结；本文件**不重定义** `Jt`/`hessEntry`/`gFun`）：

* `hessEntry i j mm = ∂²f_mm/∂z_j∂z_i` 在盒心 `u0`（`i` = KKT 行指标 = 一阶方向，`j` = `z` 列指标）；
* `Jt Hess : Fin 12 → Fin 12 → RatInterval`：49 个 KKT×`z` 格 = `−dot lamRat (Hess i j)`；
* 唯一条件前提 `hH : ∀ i j mm, (Hess i j mm).Mem (hessEntry i j mm)`。

## 本文件的层（对应任务书的 H3/H4）

**第 1 层（H4 归约，无条件 / kernel-proved）**

* `secondPartial F x i j`：二阶偏导的通用记号（与 `hessEntry` 同序）。
* `secondPartial_eq_of_hasFDerivAt`：**接口形态**——H1/H2 的链式法则天然产出
  `HasFDerivAt (fun z => fderiv ℝ F z) F2 u0`，由它一条 `rw` 即得二阶偏导的取值。
* `hessEntry_eq_fderiv_gFun`：`hessEntry i j mm = (fderiv ℝ (gFun i mm) u0) (Pi.single j 1)`。
  ⇒ `hH` **恰好等价于**「`gFun i mm` 的 `fderiv` 的 7×7 格区间包络」。
* `hH_of_gfun` / `mem_Jt_at_center_of_gfun`：把 `hH` 换成上述包络后，`Jt` 的 12×12 总装闭环。

**第 2 层（H3 装配）**：由叶子（`ringCenter`/`arcEnd`/`wPoint`）的二阶区间拼出 `Hess` 并收口 `hH`。
依赖 **H1**（叶子二阶：实侧恒等式 + 区间 + `Mem`）与 **H2**（距离分量的二阶商法则 L7）。
在 `ResidualDerivJT.lean` 中两者**尚未产出**（见 `evidence/jt-build/HESS-SPEC.md`），
故此处按工程先例（`D` 曾是 `Fin 4`、`Jt` 带 `Hess` 参数）以**显式参数**挂接，**不用未证内容填满矩阵**。

**真实等级**：第 1 层无条件；第 2 层为**条件形态**（前提逐条显式列出）。

## 3. 写域之间的**冻结接口**（Lead 裁决 R?；不许两套口径）

本文件是**新文件**、归 `jth-assembly`；`ResidualDerivJT.lean` 归 `jt-build`（本文件只
`import` 它，不改它）。两边的**唯一接口**如下（**任何一侧改口径必须先改这里**）：

### 3.1 `jt-build` 的产出（H1：二阶叶子；在 `jt-build` 自己的文件里，**不依赖本文件**）

函数形状**逐字**如下（`pad12` 与 `ofLp` 沿用 `Transport.lean` / `Definitions.lean`）：

```lean
RingC (k : Fin 9) (c : Fin 2) : (Fin 7 → ℝ) → ℝ := fun z => (ringCenter (pad12 z) k).ofLp c
ArcC  (k : Fin 9) (c : Fin 2) : (Fin 7 → ℝ) → ℝ := fun z => (arcEnd   (pad12 z) k).ofLp c
WyF                          : (Fin 7 → ℝ) → ℝ := fun z => (wPoint   (pad12 z)).ofLp 1
```

对每个叶子族给**两件**（推荐形态 A，B 亦可）：

* **(A) 实侧**：`HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ Leaf z) L2 u0`，
  其中 `L2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)`；本文件 §1 的
  `secondPartial_eq_of_hasFDerivAt`（已 kernel 证明）把它一行接成二阶偏导取值。
* **(B) 区间侧**：`ring2 : Fin 9 → Fin 2 → Fin 7 → Fin 7 → RatInterval`（`arc2`、`Wy2` 同型）
  + `∀ k c i j, (ring2 k c i j).Mem (L2 (Pi.single j 1) (Pi.single i 1))`。

**不需要** `jt-build` 产出的（本文件负责，含 kernel 引理）：`wPoint` 的 `x` 分量（仿射 ⇒ 二阶 0）、
`hub0`/`hub1` 两分量（仿射 ⇒ 二阶 0）——见 `secondPartial_const` / `secondPartial_coord`。
`∂²a_k = ∂²θ_k = 0`（仿射表）同样由本文件用同一对引理接管。

### 3.2 本文件（`jth-assembly`）的产出

* **H2**：`hessEntry i j mm = distHessReal mm i j`（`dist` 的二阶商法则 L7；纯实数恒等式，
  只需 `P_k`/`Q_k` 的二阶 + `dist_point_eq_sqrt`）。
* **H3**：由 §3.1 的叶子区间经 `add/sub/mul/invPos/sqrt` 拼出 `Hess`。
* **H4**：`hH` 收口 + `Jt` 无条件化（第 1 层已给出归约）。

### 3.3 已量化的精度要求（读数，非证明；见 `evidence/jth-assembly/K-BUDGET.md`）

叶子宽度预算 **`eps* ≈ 3.39e-6`**（`Hess` 块宽度预算 `w* ≈ 0.383`）⇒ 叶子用 **Lagrange 级**（~`1e-19`）有余量 13 个数量级；
低阶 TOT 级（`1e-4`）会 `K ≈ 29.5 > 1` **闭不上**。两处校准（内核盒端点、源链 `Q`）逐位相同。
-/

noncomputable section

namespace N11Formalization

open RatInterval

/-! ## 1. 二阶偏导的通用记法与 `fderiv` 桥 -/

/-- 二阶偏导 `∂²F/∂z_j∂z_i`（盒心求值；`i` = 一阶方向、`j` = 二阶方向，与 `hessEntry` 同序）。 -/
def secondPartial (F : (Fin 7 → ℝ) → ℝ) (x : Fin 7 → ℝ) (i j : Fin 7) : ℝ :=
  ((fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ F y) x) (Pi.single j 1)) (Pi.single i 1)

/-- **接口形态**：只要给出「`fderiv F` 的导数」的显式 CLM，就能读出二阶偏导。
H1/H2 的链式法则（`HasFDerivAt.comp` / `clm_comp` / `mul` / `div`）天然产出左侧形态，
故这是装配层与叶子层之间的**唯一接口**。 -/
theorem secondPartial_eq_of_hasFDerivAt {F : (Fin 7 → ℝ) → ℝ}
    {F2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (h : HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ F y) F2 x) (i j : Fin 7) :
    secondPartial F x i j = F2 (Pi.single j 1) (Pi.single i 1) := by
  rw [secondPartial, h.fderiv]

/-- 接口吃下的形态：`HasFDerivAt` 版二阶数据 + 逐格区间包络 ⇒ 二阶偏导的区间包络。 -/
theorem mem_secondPartial_of_hasFDerivAt {F : (Fin 7 → ℝ) → ℝ}
    {F2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (h : HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ F y) F2 u0)
    {Iv : Fin 7 → Fin 7 → RatInterval}
    (hIv : ∀ i j, (Iv i j).Mem (F2 (Pi.single j 1) (Pi.single i 1))) (i j : Fin 7) :
    (Iv i j).Mem (secondPartial F u0 i j) := by
  rw [secondPartial_eq_of_hasFDerivAt h i j]
  exact hIv i j

/-! ## 1b. 两件「二阶为 0」的基元（冻结接口的一部分：`hub`/`wPoint.x`/仿射表都由它们接管） -/

/-- 常值函数的二阶偏导为 0。 -/
theorem secondPartial_const (c : ℝ) (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (fun _ : Fin 7 → ℝ => c) x i j = 0 := by
  have hfun : (fun y : Fin 7 → ℝ => fderiv ℝ (fun _ : Fin 7 → ℝ => c) y)
      = fun _ : Fin 7 → ℝ => (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) := by
    funext y
    exact fderiv_const_apply c
  rw [secondPartial, hfun]
  simp

/-- 坐标线性函数 `z ↦ z i₀`（= `coord i₀`）的二阶偏导为 0。 -/
theorem secondPartial_coord (i₀ : Fin 7) (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => coord i₀ z) x i j = 0 := by
  have hfun : (fun y : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => coord i₀ z) y)
      = fun _ : Fin 7 → ℝ => (coord i₀ : (Fin 7 → ℝ) →L[ℝ] ℝ) := by
    funext y
    exact (ContinuousLinearMap.hasFDerivAt (f := coord i₀) (x := y)).fderiv
  rw [secondPartial, hfun, fderiv_const_apply]
  simp

/-! ## 2. H4：`hessEntry` 就是 `gFun` 的 `fderiv` -/

/-- **H4 的归约（无条件）**：`hessEntry` = `gFun i mm` 在 `u0` 沿 `e_j` 的导数。
证明只用到 `ResidualDerivJT.lean` 已有的 `hasFDerivAt_gFun`（`evCLM` 复合的取值桥）。 -/
theorem hessEntry_eq_fderiv_gFun
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (i j : Fin 7) (mm : Fin 5) :
    hessEntry i j mm = (fderiv ℝ (gFun i mm) u0) (Pi.single j 1) := by
  have h := hasFDerivAt_gFun hadj i mm
  rw [hessEntry, h.fderiv, ContinuousLinearMap.comp_apply, evCLM_apply]

/-- `hH` 的参数化形态：把 `Hess` 写成「逐 `(i,mm)` 给 7 格」的族（次序 `i, mm, j`）。 -/
def HessOfGfun (Hg : Fin 7 → Fin 5 → Fin 7 → RatInterval) : Fin 7 → Fin 7 → Fin 5 → RatInterval :=
  fun i j mm => Hg i mm j

/-- **`hH` 的等价替换（无条件）**：`hH` ⟺ 「`gFun i mm` 的 `fderiv` 的区间包络」。 -/
theorem hH_of_gfun {Hg : Fin 7 → Fin 5 → Fin 7 → RatInterval}
    (hHg : ∀ i mm j, (Hg i mm j).Mem ((fderiv ℝ (gFun i mm) u0) (Pi.single j 1)))
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0) :
    ∀ i j mm, (HessOfGfun Hg i j mm).Mem (hessEntry i j mm) := by
  intro i j mm
  rw [hessEntry_eq_fderiv_gFun hadj i j mm]
  exact hHg i mm j

/-- **`Jt` 的 12×12 总装（`hH` 已被替换成显式 `Hg` 包络）**。 -/
theorem mem_Jt_at_center_of_gfun {Hg : Fin 7 → Fin 5 → Fin 7 → RatInterval}
    (hHg : ∀ i mm j, (Hg i mm j).Mem ((fderiv ℝ (gFun i mm) u0) (Pi.single j 1)))
    (hdT : DifferentiableAt ℝ TCSystem cCertR) (hd : DifferentiableAt ℝ residualFun u0)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo) (r c : Fin 12) :
    (Jt (HessOfGfun Hg) r c).Mem ((fderiv ℝ TCSystem cCertR (Pi.single c 1)) r) :=
  mem_Jt_at_center (HessOfGfun Hg) hdT hd hadj hWk hrad hWp (hH_of_gfun hHg hadj) r c

/-! ## 4. H2/H1 **共用**的 `√` 二阶基元（一维）

`dist` 的二阶商法则（H2）与 `ρ_k` 的二阶叶（H1）都只需要这**一个一维事实**：
`d/dt (2√t)⁻¹ = −2·((2√t)⁻¹)³`（等价 `−1/(4(√t)³)`）。
本文件把它 kernel 证明，两侧共用（避免两套口径）。 -/

/-- `√` 在 `x ≠ 0` 处的导数 = `1/(2√x)`（`Real.deriv_sqrt_aux` 的一阶部分；H1/H2 的入口）。 -/
theorem hasDerivAt_sqrt' {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
  (Real.deriv_sqrt_aux hx).1.hasDerivAt

/-! ## 5. T2：标量外层复合的**二阶**链式（H2/H1 共用的核心工具）

`secondPartial (fun z => u (g z))` 的取值形态（**H2 的 L7 与 H1 的 `ρ''` 共用**）。

**两条 `∀ᶠ … DifferentiableAt` 前提是本质的**：`fderiv_add`/`fderiv_comp` 要求**逐点**可微性，
而 `fderiv g z` 在 `g` 不可微处返回 `0` ⇒ **不许弱化成点态**（否则 T2 是假命题）。

**形态纪律（Lead 裁决，与 `ArcC` 成功模式一致）**：结论里保留 `u1`（= `fderiv (deriv u)`）与
`deriv u (g u0)` 的**原始形态**，**不做代数归一化**（归一化推给消费侧）。

**收尾手法的记录（两版分歧已由 Lead 裁定）**：`change` 一步吃掉 `comp_apply`/`Pi.smul_apply`
（二者都是 `rfl` 级）是**有效**手法；用 `simp only [Pi.smul_apply, smul_apply, smul_eq_mul]`
指望它自己消掉 CLM/`Pi` 的 smul 应用**无效**（Lead 的验证副本仍在 L45 报 `simp` 无进展）。 -/
theorem hasFDerivAt_fderiv_comp_scalar {g : (Fin 7 → ℝ) → ℝ} {g1 : (Fin 7 → ℝ) →L[ℝ] ℝ}
    {g2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} {u : ℝ → ℝ} {u1 : ℝ →L[ℝ] ℝ}
    (hg : HasFDerivAt g g1 u0) (hg2 : HasFDerivAt (fun z => fderiv ℝ g z) g2 u0)
    (hu2 : HasFDerivAt (fun t => deriv u t) u1 (g u0))
    (hgd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ g z)
    (hud : ∀ᶠ z in nhds u0, DifferentiableAt ℝ u (g z)) :
    HasFDerivAt (fun z => fderiv ℝ (fun z => u (g z)) z)
      ((deriv u (g u0)) • g2 + (u1.comp g1).smulRight g1) u0 := by
  have hc : HasFDerivAt (fun z => deriv u (g z)) (u1.comp g1) u0 :=
    hu2.comp u0 hg
  have hsmul := hc.smul hg2
  rw [hg.fderiv] at hsmul
  refine hsmul.congr_of_eventuallyEq ?_
  filter_upwards [hgd, hud] with z hz1 hz2
  have hcomp : fderiv ℝ (fun z => u (g z)) z
      = (fderiv ℝ u (g z)).comp (fderiv ℝ g z) :=
    (hz2.hasFDerivAt.comp z hz1.hasFDerivAt).fderiv
  rw [hcomp]
  ext v
  have hmap := map_smul (fderiv ℝ u (g z)) ((fderiv ℝ g z) v) (1 : ℝ)
  rw [smul_eq_mul, mul_one, fderiv_apply_one_eq_deriv] at hmap
  change (fderiv ℝ u (g z)) ((fderiv ℝ g z) v) = deriv u (g z) * ((fderiv ℝ g z) v)
  exact hmap.trans (mul_comm _ _)

/-! ## 6. T1（加减的二阶）+ `√` 的 1D 二阶基元

**T1**：`HasFDerivAt (fun z => fderiv ℝ (φ ± ψ) z) (φ2 ± ψ2) u0`。
前提照 T2：两条 `∀ᶠ … DifferentiableAt`（**本质前提，不许弱化成点态** —— 弱化则假：
`fderiv_add`/`fderiv_sub` 需逐点可微，不可微处 `fderiv` 返回 `0`）。

**`√` 的 1D 二阶**：`hasDerivAt_deriv_sqrt`（**原始形态** `-(2·(1/(2√x)))/(2√x)²`，不归一化）
—— 它就是 T2 在 `u := Real.sqrt` 时 `hu2`（`HasFDerivAt (fun t => deriv √ t) u1 (g u0)`）的来源。 -/

theorem hasFDerivAt_fderiv_add {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 u0)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 u0)
    (hφd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ ψ z) :
    HasFDerivAt (fun z => fderiv ℝ (fun z => φ z + ψ z) z) (φ2 + ψ2) u0 := by
  have h : HasFDerivAt (fun z => fderiv ℝ φ z + fderiv ℝ ψ z) (φ2 + ψ2) u0 := hφ.add hψ
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hφd, hψd] with z hz1 hz2
  change fderiv ℝ (φ + ψ) z = fderiv ℝ φ z + fderiv ℝ ψ z
  exact fderiv_add hz1 hz2

theorem hasFDerivAt_fderiv_sub {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 u0)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 u0)
    (hφd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ ψ z) :
    HasFDerivAt (fun z => fderiv ℝ (fun z => φ z - ψ z) z) (φ2 - ψ2) u0 := by
  have h : HasFDerivAt (fun z => fderiv ℝ φ z - fderiv ℝ ψ z) (φ2 - ψ2) u0 := hφ.sub hψ
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hφd, hψd] with z hz1 hz2
  change fderiv ℝ (φ - ψ) z = fderiv ℝ φ z - fderiv ℝ ψ z
  exact fderiv_sub hz1 hz2

/-- `deriv √` 的导数（`x > 0`），**原始形态**（不归一化）：`-(2·(1/(2√x)))/(2√x)²`。 -/
theorem hasDerivAt_deriv_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => deriv Real.sqrt t)
      (-(2 * (1 / (2 * Real.sqrt x))) / (2 * Real.sqrt x) ^ 2) x := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (2 * (1 / (2 * Real.sqrt x))) x :=
    (hasDerivAt_sqrt' hx.ne').const_mul 2
  have h2 : HasDerivAt (fun t : ℝ => (2 * Real.sqrt t)⁻¹)
      (-(2 * (1 / (2 * Real.sqrt x))) / (2 * Real.sqrt x) ^ 2) x := h1.inv (by positivity)
  have hev : (fun t : ℝ => deriv Real.sqrt t) =ᶠ[nhds x] (fun t : ℝ => (2 * Real.sqrt t)⁻¹) := by
    filter_upwards [eventually_gt_nhds hx] with t ht
    exact ((Real.deriv_sqrt_aux ht.ne').1.hasDerivAt.deriv).trans (one_div _)
  exact (hev.hasDerivAt_iff).mpr h2

/-! ## 7. T3（二阶乘积法则，自 `jt-build` 的 `Leaf2Dev.lean` 移居）+ `√` 规则（T2 特化）

T3 与 T1/T2 同族同住（Lead 裁决：一次审计覆盖三者）。**原样搬入，不改形态**。 -/

/-- **T3（二阶乘积法则）**：`(φ·ψ)'' = φ·ψ'' + φ'⊗ψ' + ψ·φ'' + ψ'⊗φ'`。 -/
theorem hasFDerivAt_fderiv_mul_scalar
    {φ ψ : (Fin 7 → ℝ) → ℝ} {φ1 ψ1 : (Fin 7 → ℝ) →L[ℝ] ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hφ : HasFDerivAt φ φ1 u0) (hφ2 : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 u0)
    (hψ : HasFDerivAt ψ ψ1 u0) (hψ2 : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 u0)
    (hφd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ ψ z) :
    HasFDerivAt (fun z => fderiv ℝ (fun y => φ y * ψ y) z)
      ((φ u0 • ψ2 + φ1.smulRight ψ1) + (ψ u0 • φ2 + ψ1.smulRight φ1)) u0 := by
  have hA : HasFDerivAt (fun z : Fin 7 → ℝ => φ z • fderiv ℝ ψ z)
      (φ u0 • ψ2 + φ1.smulRight ψ1) u0 := by
    have h := hφ.smul hψ2
    rw [hψ.fderiv] at h
    exact h
  have hB : HasFDerivAt (fun z : Fin 7 → ℝ => ψ z • fderiv ℝ φ z)
      (ψ u0 • φ2 + ψ1.smulRight φ1) u0 := by
    have h := hψ.smul hφ2
    rw [hφ.fderiv] at h
    exact h
  have hsum := hA.add hB
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hφd, hψd] with z hz1 hz2
  have hcomp : fderiv ℝ (fun y => φ y * ψ y) z
      = (φ z) • (fderiv ℝ ψ z) + (ψ z) • (fderiv ℝ φ z) :=
    (hz1.hasFDerivAt.mul hz2.hasFDerivAt).fderiv
  rw [hcomp]
  rfl

/-- **`√` 规则**：T2 在 `u := Real.sqrt` 的特化（`hu2` 由 `hasDerivAt_deriv_sqrt` +
`HasDerivAt.hasFDerivAt` 给 `toSpanSingleton`；**原始形态，不归一化**）。 -/
theorem hasFDerivAt_fderiv_sqrt_comp {g : (Fin 7 → ℝ) → ℝ} {g1 : (Fin 7 → ℝ) →L[ℝ] ℝ}
    {g2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hg : HasFDerivAt g g1 u0) (hg2 : HasFDerivAt (fun z => fderiv ℝ g z) g2 u0)
    (hpos : 0 < g u0)
    (hgd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ g z)
    (hud : ∀ᶠ z in nhds u0, DifferentiableAt ℝ Real.sqrt (g z)) :
    HasFDerivAt (fun z => fderiv ℝ (fun z => Real.sqrt (g z)) z)
      ((deriv Real.sqrt (g u0)) • g2
        + ((ContinuousLinearMap.toSpanSingleton ℝ
              (-(2 * (1 / (2 * Real.sqrt (g u0)))) / (2 * Real.sqrt (g u0)) ^ 2)).comp g1).smulRight g1)
      u0 := by
  have hu2 : HasFDerivAt (fun t : ℝ => deriv Real.sqrt t)
      (ContinuousLinearMap.toSpanSingleton ℝ
        (-(2 * (1 / (2 * Real.sqrt (g u0)))) / (2 * Real.sqrt (g u0)) ^ 2)) (g u0) :=
    (hasDerivAt_deriv_sqrt hpos).hasFDerivAt
  exact hasFDerivAt_fderiv_comp_scalar hg hg2 hu2 hgd hud

/-! ## 8. H3 装配（第一片）：`secondPartial` 的加减律

`Uvec = C_s + C_{s+1} − B_s`、`Δ = P − Q` 的**二阶**落地所需的第一步：由 §6 的 T1（加减的二阶）
+ §1 的桥，得到**二阶偏导级**的加减律。**前提照 T1**（两条 `∀ᶠ DifferentiableAt`，不弱化）。

**用途（§8 后续片）**：`Δ²_{mm,c}(i,j)` 由叶子（`ring2`/`arc2`/`Wy2`，`jt-build` 落根后即为）
按 `resSlot`/`resHub` 的加减组合得到；`hub`/`wPoint.x` 的零项走 §1b 的 `secondPartial_const`/`_coord`。 -/

theorem secondPartial_add {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 u0)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 u0)
    (hφd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ ψ z) (i j : Fin 7) :
    secondPartial (fun z => φ z + ψ z) u0 i j
      = secondPartial φ u0 i j + secondPartial ψ u0 i j := by
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_add hφ hψ hφd hψd),
    secondPartial_eq_of_hasFDerivAt hφ, secondPartial_eq_of_hasFDerivAt hψ]
  exact add_apply _ _ _

theorem secondPartial_sub {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 u0)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 u0)
    (hφd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ ψ z) (i j : Fin 7) :
    secondPartial (fun z => φ z - ψ z) u0 i j
      = secondPartial φ u0 i j - secondPartial ψ u0 i j := by
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_sub hφ hψ hφd hψd),
    secondPartial_eq_of_hasFDerivAt hφ, secondPartial_eq_of_hasFDerivAt hψ]
  exact sub_apply _ _ _

/-- **§8 第二片：`Uvec` 分量的二阶分解（Δ² 的实数侧）**。

`Uvec = C_s + C_{s+1} − B_s` 在 `.ofLp c` 下是根内 `rfl`（`SourceIdentity.Uvec_coord0/1`）
⇒ 本引理把它升到**二阶**（用 §8 第一片的 `secondPartial_add`/`secondPartial_sub`）。
前提 = 叶子二阶的 `HasFDerivAt`（冻结接口的**实侧**）+ 两条 `∀ᶠ DifferentiableAt`（不弱化）。

两处 scratch 试错留档：① `fin_cases c` 后 `c` 是 `⟨1, ⋯⟩` 而非字面量 ⇒ `rw [Uvec_coord1]` 不匹配，
改用 `exact`（按 defeq）；② `hCd.add hC'd`（点态）不能加在 `∀ᶠ` 上 ⇒ `(hCd.and hC'd).mono …`。 -/
theorem secondPartial_Uvec_coord (s : Fin 9) (c : Fin 2) (i j : Fin 7)
    {C2 C2' A2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hC : HasFDerivAt (fun z => fderiv ℝ (fun z => (ringCenter (pad12 z) s).ofLp c) z) C2 u0)
    (hC' : HasFDerivAt (fun z => fderiv ℝ (fun z => (ringCenter (pad12 z) (s + 1)).ofLp c) z) C2' u0)
    (hA : HasFDerivAt (fun z => fderiv ℝ (fun z => (arcEnd (pad12 z) s).ofLp c) z) A2 u0)
    (hCd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z => (ringCenter (pad12 z) s).ofLp c) z)
    (hC'd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z => (ringCenter (pad12 z) (s + 1)).ofLp c) z)
    (hAd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z => (arcEnd (pad12 z) s).ofLp c) z) :
    secondPartial (fun z => (Uvec (pad12 z) s).ofLp c) u0 i j
      = secondPartial (fun z => (ringCenter (pad12 z) s).ofLp c) u0 i j
        + secondPartial (fun z => (ringCenter (pad12 z) (s + 1)).ofLp c) u0 i j
        - secondPartial (fun z => (arcEnd (pad12 z) s).ofLp c) u0 i j := by
  have hcmp : ∀ z : Fin 7 → ℝ, (Uvec (pad12 z) s).ofLp c
      = (ringCenter (pad12 z) s).ofLp c + (ringCenter (pad12 z) (s + 1)).ofLp c
        - (arcEnd (pad12 z) s).ofLp c := by
    intro z
    fin_cases c
    · exact Uvec_coord0 (pad12 z) s
    · exact Uvec_coord1 (pad12 z) s
  have e1 : (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp c)
      = fun z : Fin 7 → ℝ => ((ringCenter (pad12 z) s).ofLp c
          + (ringCenter (pad12 z) (s + 1)).ofLp c) - (arcEnd (pad12 z) s).ofLp c :=
    funext hcmp
  rw [e1]
  have hsum2 : HasFDerivAt (fun z => fderiv ℝ (fun z : Fin 7 → ℝ =>
        (ringCenter (pad12 z) s).ofLp c + (ringCenter (pad12 z) (s + 1)).ofLp c) z) (C2 + C2') u0 :=
    hasFDerivAt_fderiv_add hC hC' hCd hC'd
  have hsumd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z : Fin 7 → ℝ =>
        (ringCenter (pad12 z) s).ofLp c + (ringCenter (pad12 z) (s + 1)).ofLp c) z :=
    (hCd.and hC'd).mono fun z hz => hz.1.add hz.2
  rw [secondPartial_sub hsum2 hA hsumd hAd]
  rw [secondPartial_add hC hC' hCd hC'd]

/-! ## 9. `hub` 零项 + 一般 CLM 的二阶为零 + L7 外框（H3 装配的构件）

**`hub` 分量**是仿射（`SourceIdentity.hub*_coord*` 皆 `rfl`）⇒ 二阶恒 0：x 走 `secondPartial_clm`、
y 走 `secondPartial_const`（见 §1b）。
**一条试错留档**：`coord` 的"取值"在目标里展开成**结构字面量应用** ⇒ `rw`/`rfl`/`simpa only` 都可能失败 ✗，
**正解 `exact (…).trans …`（按 defeq 比）** ✓。
**L7 外框**（`hessIv`/`HessOf`）只落**定义**（零风险）把区间表达式形状钉死；
参数 `d2xIv/d2yIv` = `Δ` 二阶区间族（叶子二阶的产出）；`−R`（`z₆`）线性 ⇒ 二阶无贡献 ⇒ 外框不出现 `δ_{i6}`。 -/

theorem secondPartial_hub0_coord0 (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0) u0 i j = 0 := by
  have hfun : (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0) = fun z => coord 4 z := by
    funext z
    exact (hub0_coord0 (pad12 z)).trans (pad12_four z)
  rw [hfun]
  exact secondPartial_coord 4 u0 i j

theorem secondPartial_hub0_coord1 (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1) u0 i j = 0 := by
  have hfun : (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1) = fun _ => (0 : ℝ) := by
    funext z
    rw [hub0_coord1]
  rw [hfun]
  exact secondPartial_const 0 u0 i j

theorem secondPartial_hub1_coord0 (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0) u0 i j = 0 := by
  have hfun : (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0) = fun z => coord 5 z := by
    funext z
    exact (hub1_coord0 (pad12 z)).trans (pad12_five z)
  rw [hfun]
  exact secondPartial_coord 5 u0 i j

theorem secondPartial_hub1_coord1 (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1) u0 i j = 0 := by
  have hfun : (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1) = fun _ => (0 : ℝ) := by
    funext z
    rw [hub1_coord1]
  rw [hfun]
  exact secondPartial_const 0 u0 i j

/-- **任何 CLM 的取值函数，二阶偏导恒为 0**（`coord` 情形是其特例；也覆盖
`(1/2 : ℝ) • (coord 4 + coord 5)` 这类组合 ⇒ `wPoint.x` 与仿射表直接可用）。 -/
theorem secondPartial_clm (L : (Fin 7 → ℝ) →L[ℝ] ℝ) (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => L z) x i j = 0 := by
  have hfun : (fun y : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => L z) y) = fun _ => L := by
    funext y
    exact (ContinuousLinearMap.hasFDerivAt (f := L) (x := y)).fderiv
  rw [secondPartial, hfun, fderiv_const_apply]
  simp

/-- `Δ` 的一阶 x 分量（`k = 4` 走 `wPoint` 版；与 `ResidualDerivD.D` 的写法同型）。 -/
def d1xIv (k : Fin 5) (i : Fin 7) : RatInterval :=
  if k = 4 then dUx4Iv i else dUxIv k i

/-- `Δ` 的一阶 y 分量。 -/
def d1yIv (k : Fin 5) (i : Fin 7) : RatInterval :=
  if k = 4 then dUy4Iv i else dUyIv k i

/-- **L7 外框**（区间侧）：`Hess` 单格 = `(d_i·d_j)/√S + (d·d_ij)/√S − (d·d_i)(d·d_j)/S^{3/2}`。
参数 `d2xIv/d2yIv` = `Δ` 的二阶区间族（叶子二阶产出）。 -/
def hessIv (d2xIv d2yIv : Fin 5 → Fin 7 → Fin 7 → RatInterval)
    (k : Fin 5) (i j : Fin 7) : RatInterval :=
  sub
    (add
      (mul (ofRat 2)
        (mul (invPos (twoRadSqrtIv k))
          (add (mul (d1xIv k i) (d1xIv k j)) (mul (d1yIv k i) (d1yIv k j)))))
      (mul (ofRat 2)
        (mul (invPos (twoRadSqrtIv k))
          (add (mul (DxIv k) (d2xIv k i j)) (mul (DyIv k) (d2yIv k i j))))))
    (mul (ofRat 2)
      (mul (invPos (mul (radIv k) (twoRadSqrtIv k)))
        (mul (add (mul (DxIv k) (d1xIv k i)) (mul (DyIv k) (d1yIv k i)))
             (add (mul (DxIv k) (d1xIv k j)) (mul (DyIv k) (d1yIv k j))))))

/-- **`Hess`（参数化形态）**：与冻结接口同型 `Fin 7 → Fin 7 → Fin 5 → RatInterval`。 -/
def HessOf (d2xIv d2yIv : Fin 5 → Fin 7 → Fin 7 → RatInterval) :
    Fin 7 → Fin 7 → Fin 5 → RatInterval :=
  fun i j mm => hessIv d2xIv d2yIv mm i j

end N11Formalization
