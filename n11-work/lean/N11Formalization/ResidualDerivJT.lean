import N11Formalization.ResidualDerivD
import N11Formalization.KrawczykMatrix

/-!
# `Jt`：G1 的 12×12 Jacobian 区间包络（**盒心点**版）

本文件是 `hsum`/`η`/`hres` 首次可实例化的**前置**：把 `Precond`/`KrawczykMatrix` 里
那条 `hJ`（Jacobian 的逐元素区间包络）从"外部要求"变成**本工程内可证的构造**。

## 消费方形状（逐字取自 `Precond.lean` / `KrawczykMatrix.lean`）

```
(Jt : Fin 12 → Fin 12 → RatInterval)
(hJ : ∀ x ∈ closedBall c ρ, ∀ k j : Fin 12,
        (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
```

## 本文件交付的形状（**诚实分层**）

* `Jt Hess : Fin 12 → Fin 12 → RatInterval` —— 12×12 的分块定义：

  | 行块 \ 列块 | `z` 列（`j < 7`，`u_j`） | `λ` 列（`j ≥ 7`，`u_{7+m}`） |
  |---|---|---|
  | 残差行（`r < 5`） | `D r j`（`D` 的 5×7 包络，**已证**） | `[0,0]`（`f` 不依赖 `λ`，**已证**） |
  | KKT 行（`r = 5+i`，`i < 7`） | `−Σ_m λ_m · Hess i j m`（`Hess` 为**供给的**二阶包络） | `−(D m i)`（即源文的 `−J_f^T`，**已证**） |

* **已证（不依赖 `Hess` 的 95 格）**：5 个残差行 × 12 列（60 格）+ 7 个 KKT 行 × 5 个 `λ` 列（35 格），
  在盒心 `cCertR` 处给出 `(fderiv ℝ TCSystem cCertR (Pi.single c 1)) r` 的包络。

* **未证（明确列出的一处 gap）**：**KKT 行 × `z` 列**（7×7 = 49 格）——源文的
  `−Σ_k λ_k H_k` 块，需要 `residualFun` 的**二阶**偏导。本文件把它**参数化**成
  `Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval`（每格一个 5 维区间向量 = `(H_l)_{i,j}` 的包络），
  并给出**它必须满足的精确义务**（`mem_hessEntry`，见 §7）。**没有用未证内容填满矩阵。**

## 接口冻结（供 `Hess` 实施者 H3/H4 对齐；Lead R65 已批准拆分）

* **`hessEntry`/`Jt`/`Hess` 的定义在本文件冻结**，实施者**只做装配**，不要重定义：
  ```
  hessEntry i j mm := ((fderiv ℝ (fun z => fderiv ℝ residualFun z) u0) (Pi.single j 1))
                        (Pi.single i 1) mm            -- = ∂²f_mm/∂z_i∂z_j 在盒心
  Jt Hess : Fin 12 → Fin 12 → RatInterval             -- KKT×z 格 = −dot lamRat (Hess i j)
  hH : ∀ i j mm, (Hess i j mm).Mem (hessEntry i j mm) -- H4 的目标（唯一条件前提）
  ```
* 消费点：`mem_Jt_kkt_z`（49 格）、`mem_Jt_at_center`（12×12 总装）。
* **解析二阶公式（已数值验证，非证明）与区间装配表见** `evidence/jt-build/HESS-SPEC.md`
  （脚本 `evidence/jt-build/hess_formula_check.py`；该步抓出两处初稿公式错误：`Wy` 的符号、
  `Wx`（和）与 `m`（差）的导数混用）。
* **宽度口径**：`Hess` 的宽度**尚无读数**；H3 出来时必须先给 `max(hi−lo)` 与它对 `hsum` 的 `K`
  的贡献读数（Krawczyk 口径用源链有理 `Yinv`，**不要**自己求逆；R65 已判定 `Y=J⁻¹` 口径错位）。

## 与消费方接口的两点**口径差**（必须显式记账，不得静默）

1. **点 vs 球**：`hJ` 量化在 `∀ x ∈ closedBall c ρ`（连续统）；本文件给的是 `x = cCertR`（盒心）
   的**逐点**包络。点 → 球需要**导数的 Lipschitz 界**（二阶增长），这是一个**独立未付义务**
   （§8 给出精确陈述），本文件不声称已付。
2. **`Hess` 是有理数据**：λ 权 `λ_m = (cCert ⟨m+7⟩ : ℝ)` 是证书里的**精确有理数**，
   故 `Hess` 一旦给出，KKT–`z` 块就是有限有理区间的组合（不需要实数语义前提）。

**真实等级**：本文件 kernel-proved（除 §7/§8 显式列出的 `Hess` 义务与球级义务外），
零 `sorry`、零自定义 `axiom`、零 `native_decide`。
-/

noncomputable section

namespace N11Formalization

open RatInterval

/-! ## 0. 索引工具（`Fin 5`/`Fin 7` ↔ `Fin 12`，统一具名字面量） -/

/-- 残差行（`F` 的前 5 个分量）在 12 维里的位置（= `z` 的前 5 个坐标）。 -/
def row5 (k : Fin 5) : Fin 12 := ⟨(k : ℕ), by omega⟩

/-- `z` 方向第 `i` 个坐标在 12 维里的位置。 -/
def up7 (i : Fin 7) : Fin 12 := ⟨(i : ℕ), by omega⟩

/-- `λ` 方向第 `m` 个坐标在 12 维里的位置：`λ_m ↦ u_{7+m}`。 -/
def up5 (m : Fin 5) : Fin 12 := ⟨(m : ℕ) + 7, by omega⟩

/-- KKT 行（`F` 的后 7 个分量）在 12 维里的位置：`z` 指标 `i ↦ F_{5+i}`。 -/
def kkt12 (i : Fin 7) : Fin 12 := ⟨5 + (i : ℕ), by omega⟩

@[simp] theorem row5_val (k : Fin 5) : ((row5 k : Fin 12) : ℕ) = (k : ℕ) := rfl
@[simp] theorem up7_val (i : Fin 7) : ((up7 i : Fin 12) : ℕ) = (i : ℕ) := rfl
@[simp] theorem up5_val (m : Fin 5) : ((up5 m : Fin 12) : ℕ) = (m : ℕ) + 7 := rfl
@[simp] theorem kkt12_val (i : Fin 7) : ((kkt12 i : Fin 12) : ℕ) = 5 + (i : ℕ) := rfl

theorem up7_inj : Function.Injective up7 := fun a b h =>
  Fin.ext (by simpa only [up7_val] using congrArg (Fin.val : Fin 12 → ℕ) h)

theorem up5_inj : Function.Injective up5 := fun a b h => by
  have hv : (a : ℕ) + 7 = (b : ℕ) + 7 := by
    simpa only [up5_val] using congrArg (Fin.val : Fin 12 → ℕ) h
  exact Fin.ext (by omega)

theorem up7_ne_up5 (i : Fin 7) (m : Fin 5) : up7 i ≠ up5 m := by
  intro h
  have hv : (i : ℕ) = (m : ℕ) + 7 := congrArg Fin.val h
  omega

theorem eq_up7_of_lt {c : Fin 12} (hc : (c : ℕ) < 7) : c = up7 ⟨(c : ℕ), hc⟩ := by
  refine Fin.ext ?_
  show (c : ℕ) = (c : ℕ)
  rfl

theorem eq_up5_of_le {c : Fin 12} (hc : 7 ≤ (c : ℕ)) : c = up5 ⟨(c : ℕ) - 7, by omega⟩ := by
  refine Fin.ext ?_
  show (c : ℕ) = ((c : ℕ) - 7) + 7
  omega

theorem eq_kkt12_of_le {r : Fin 12} (hr : 5 ≤ (r : ℕ)) : r = kkt12 ⟨(r : ℕ) - 5, by omega⟩ := by
  refine Fin.ext ?_
  show (r : ℕ) = 5 + ((r : ℕ) - 5)
  omega

theorem sub5_kkt12 (i : Fin 7) :
    (⟨((kkt12 i : Fin 12) : ℕ) - 5, by omega⟩ : Fin 7) = i := by
  refine Fin.ext ?_
  show (5 + (i : ℕ)) - 5 = (i : ℕ)
  omega

theorem sub7_up5 (m : Fin 5) :
    (⟨((up5 m : Fin 12) : ℕ) - 7, by omega⟩ : Fin 5) = m := by
  refine Fin.ext ?_
  show ((m : ℕ) + 7) - 7 = (m : ℕ)
  omega

theorem mk_row5 (k : Fin 5) : (⟨((row5 k : Fin 12) : ℕ), k.isLt⟩ : Fin 5) = k := rfl

theorem mk_up7 (j : Fin 7) : (⟨((up7 j : Fin 12) : ℕ), j.isLt⟩ : Fin 7) = j := rfl

/-! ## 1. `first7` 的 CLM 形态与链式法则 -/

/-- `first7`（取前 7 个坐标）作为连续线性映射。 -/
def proj7CLM : (Fin 12 → ℝ) →L[ℝ] (Fin 7 → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin 7 =>
    (ContinuousLinearMap.proj (up7 i) : (Fin 12 → ℝ) →L[ℝ] ℝ)

theorem proj7CLM_apply (u : Fin 12 → ℝ) (i : Fin 7) : proj7CLM u i = u (up7 i) := by
  simp only [proj7CLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]

theorem proj7CLM_apply_eq_first7 (u : Fin 12 → ℝ) : proj7CLM u = first7 u := by
  funext i
  rw [proj7CLM_apply]
  rfl

theorem proj7CLM_single_up7 (j : Fin 7) :
    proj7CLM (Pi.single (up7 j) (1 : ℝ)) = Pi.single j 1 := by
  funext i
  rw [proj7CLM_apply]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · have hne : (up7 i : Fin 12) ≠ up7 j := fun hh => h (up7_inj hh)
    rw [Pi.single_eq_of_ne (i := up7 j) (i' := up7 i) hne,
      Pi.single_eq_of_ne (i := j) (i' := i) h]

theorem proj7CLM_single_up5 (m : Fin 5) :
    proj7CLM (Pi.single (up5 m) (1 : ℝ)) = 0 := by
  funext i
  rw [proj7CLM_apply, Pi.single_eq_of_ne (i := up5 m) (i' := up7 i) (up7_ne_up5 i m)]
  rfl

/-- `first7` 的 Fréchet 导数就是 `proj7CLM`（`first7` 是线性的）。 -/
theorem hasFDerivAt_first7 (x : Fin 12 → ℝ) :
    HasFDerivAt (fun u : Fin 12 → ℝ => first7 u) proj7CLM x := by
  have he : (fun u : Fin 12 → ℝ => first7 u) = fun u => proj7CLM u := by
    funext u
    exact (proj7CLM_apply_eq_first7 u).symm
  rw [he]
  exact proj7CLM.hasFDerivAt

/-- `residualFun ∘ first7` 的 Fréchet 导数（链式法则）。 -/
theorem hasFDerivAt_residualFun_first7 (hd : DifferentiableAt ℝ residualFun u0) :
    HasFDerivAt (fun u : Fin 12 → ℝ => residualFun (first7 u))
      ((fderiv ℝ residualFun u0).comp proj7CLM) cCertR :=
  hd.hasFDerivAt.comp cCertR (hasFDerivAt_first7 cCertR)

theorem fderiv_residualFun_first7 (hd : DifferentiableAt ℝ residualFun u0) :
    fderiv ℝ (fun u : Fin 12 → ℝ => residualFun (first7 u)) cCertR
      = (fderiv ℝ residualFun u0).comp proj7CLM :=
  (hasFDerivAt_residualFun_first7 hd).fderiv

/-- `fderiv` 的**取值形态**：把 `(fderiv F x v) k` 降到 `F` 的第 `k` 个分量函数。 -/
theorem fderiv_apply_val {x : Fin 12 → ℝ} (hd : DifferentiableAt ℝ TCSystem x)
    (k : Fin 12) (v : Fin 12 → ℝ) :
    (fderiv ℝ TCSystem x v) k = (fderiv ℝ (fun u : Fin 12 → ℝ => TCSystem u k) x) v := by
  rw [fderiv_apply hd k]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-! ## 2. `Jt`：12×12 分块定义 -/

/-- λ 权（证书里的**精确有理数**）：`λ_m = cCert ⟨m+7⟩`。 -/
def lamRat : Fin 5 → ℚ := fun m => cCert ⟨(m : ℕ) + 7, by omega⟩

theorem lamRat_eq_last5 (m : Fin 5) : ((lamRat m : ℚ) : ℝ) = last5 cCertR m := by
  simp [lamRat, last5, cCertR]

/-- **G1 的 12×12 Jacobian 区间包络**（盒心点），按 `TCSystem` 的分块定义：

* 残差行（`r < 5`）：`z` 列用 `D`，`λ` 列是 `[0,0]`（`f` 不读 `λ`）；
* KKT 行（`r = 5+i`）：`λ` 列是 `−(D m i)`（= 源文的 `−J_f^T`），
  `z` 列是供给的 `Hess i j` 经有理权 `λ_m` 组合后取负（= 源文的 `−Σλ_k H_k`）。

`Hess` 是**未证块的参数**：它的义务见 §7。 -/
def Jt (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (r c : Fin 12) : RatInterval :=
  if hr : (r : ℕ) < 5 then
    if hc : (c : ℕ) < 7 then D ⟨(r : ℕ), hr⟩ ⟨(c : ℕ), hc⟩ else RatInterval.ofRat 0
  else
    if hc : (c : ℕ) < 7 then
      RatInterval.neg
        (RatInterval.dot lamRat (Hess ⟨(r : ℕ) - 5, by omega⟩ ⟨(c : ℕ), hc⟩))
    else RatInterval.neg (D ⟨(c : ℕ) - 7, by omega⟩ ⟨(r : ℕ) - 5, by omega⟩)

/-! ## 3. `Jt` 的逐块取值（形状引理） -/

theorem Jt_res_z (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (k : Fin 5) (j : Fin 7) :
    Jt Hess (row5 k) (up7 j) = D k j := by
  simp only [Jt]
  rw [dif_pos (show ((row5 k : Fin 12) : ℕ) < 5 from k.isLt),
    dif_pos (show ((up7 j : Fin 12) : ℕ) < 7 from j.isLt)]
  simp only [mk_row5, mk_up7]

theorem Jt_res_lam (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (k : Fin 5) (m : Fin 5) :
    Jt Hess (row5 k) (up5 m) = RatInterval.ofRat 0 := by
  simp only [Jt]
  rw [dif_pos (show ((row5 k : Fin 12) : ℕ) < 5 from k.isLt),
    dif_neg (show ¬ ((up5 m : Fin 12) : ℕ) < 7 by simp)]

theorem Jt_kkt_z (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (i j : Fin 7) :
    Jt Hess (kkt12 i) (up7 j)
      = RatInterval.neg (RatInterval.dot lamRat (Hess i j)) := by
  simp only [Jt]
  rw [dif_neg (show ¬ ((kkt12 i : Fin 12) : ℕ) < 5 by simp),
    dif_pos (show ((up7 j : Fin 12) : ℕ) < 7 from j.isLt)]
  simp only [sub5_kkt12, mk_up7]

theorem Jt_kkt_lam (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (i : Fin 7) (m : Fin 5) :
    Jt Hess (kkt12 i) (up5 m) = RatInterval.neg (D m i) := by
  simp only [Jt]
  rw [dif_neg (show ¬ ((kkt12 i : Fin 12) : ℕ) < 5 by simp),
    dif_neg (show ¬ ((up5 m : Fin 12) : ℕ) < 7 by simp)]
  simp only [sub7_up5, sub5_kkt12]

/-! ## 4. 残差行：`fderiv` 的解析降低 -/

/-- `TCSystem` 的前 5 个分量作为 12 维函数 = `residualFun ∘ first7` 的对应分量。 -/
theorem TCSystem_row_eq_residualFun (k : Fin 5) :
    (fun u : Fin 12 → ℝ => TCSystem u (row5 k)) = fun u => residualFun (first7 u) k := by
  funext u
  have hk : ((row5 k : Fin 12) : ℕ) < 5 := k.isLt
  rw [TCSystem, dif_pos hk, residualFun_eq (first7 u), ← residual_transport u]
  rfl

/-- **残差行 × `z` 列**：`fderiv TCSystem` 的第 `k` 行、`z_j` 列 = `∂f_k/∂z_j`（盒心）。 -/
theorem fderiv_TCSystem_res_z (hdT : DifferentiableAt ℝ TCSystem cCertR)
    (hd : DifferentiableAt ℝ residualFun u0) (k : Fin 5) (j : Fin 7) :
    (fderiv ℝ TCSystem cCertR (Pi.single (up7 j) (1 : ℝ))) (row5 k)
      = (fderiv ℝ residualFun u0 (Pi.single j 1)) k := by
  rw [fderiv_apply_val hdT (row5 k) (Pi.single (up7 j) (1 : ℝ)),
    TCSystem_row_eq_residualFun k]
  have hdiff : DifferentiableAt ℝ (fun u : Fin 12 → ℝ => residualFun (first7 u)) cCertR :=
    (hasFDerivAt_residualFun_first7 hd).differentiableAt
  rw [fderiv_apply hdiff k, fderiv_residualFun_first7 hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    proj7CLM_single_up7]

/-- **残差行 × `λ` 列 = 0**：`f` 不读乘子坐标。 -/
theorem fderiv_TCSystem_res_lam (hdT : DifferentiableAt ℝ TCSystem cCertR)
    (hd : DifferentiableAt ℝ residualFun u0) (k : Fin 5) (m : Fin 5) :
    (fderiv ℝ TCSystem cCertR (Pi.single (up5 m) (1 : ℝ))) (row5 k) = 0 := by
  rw [fderiv_apply_val hdT (row5 k) (Pi.single (up5 m) (1 : ℝ)),
    TCSystem_row_eq_residualFun k]
  have hdiff : DifferentiableAt ℝ (fun u : Fin 12 → ℝ => residualFun (first7 u)) cCertR :=
    (hasFDerivAt_residualFun_first7 hd).differentiableAt
  rw [fderiv_apply hdiff k, fderiv_residualFun_first7 hd]
  simp only [ContinuousLinearMap.comp_apply, proj7CLM_single_up5,
    ContinuousLinearMap.map_zero]

/-! ## 5. 残差行 × 12 列：区间包络（用 `D` 的 `hD_*`） -/

/-- `D` 的 5×7 无条件形态（把 `hD_0..hD_4` 的 `fin_cases` 分派收成一条）。 -/
theorem mem_D (hd : DifferentiableAt ℝ residualFun u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo) (k : Fin 5) (j : Fin 7) :
    (D k j).Mem ((fderiv ℝ residualFun u0 (Pi.single j 1)) k) := by
  fin_cases k
  · exact hD_0 hd hWk hrad j
  · exact hD_1 hd hWk hrad j
  · exact hD_2 hd hWk hrad j
  · exact hD_3 hd hWk hrad j
  · exact hD_4 hd hWk hWp hrad j

/-- **残差行（`r = k < 5`）× `z` 列**。 -/
theorem mem_Jt_res_z (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval)
    (hdT : DifferentiableAt ℝ TCSystem cCertR) (hd : DifferentiableAt ℝ residualFun u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo) (k : Fin 5) (j : Fin 7) :
    (Jt Hess (row5 k) (up7 j)).Mem
      ((fderiv ℝ TCSystem cCertR (Pi.single (up7 j) (1 : ℝ))) (row5 k)) := by
  rw [Jt_res_z, fderiv_TCSystem_res_z hdT hd k j]
  exact mem_D hd hWk hrad hWp k j

/-- **残差行（`r = k < 5`）× `λ` 列 = `[0,0]`**。 -/
theorem mem_Jt_res_lam (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval)
    (hdT : DifferentiableAt ℝ TCSystem cCertR) (hd : DifferentiableAt ℝ residualFun u0)
    (k : Fin 5) (m : Fin 5) :
    (Jt Hess (row5 k) (up5 m)).Mem
      ((fderiv ℝ TCSystem cCertR (Pi.single (up5 m) (1 : ℝ))) (row5 k)) := by
  rw [Jt_res_lam, fderiv_TCSystem_res_lam hdT hd k m]
  simpa using RatInterval.ofRat_mem (0 : ℚ)

/-- **残差行 12 列合一**（列指标 `c : Fin 12`，自动分 `z`/`λ` 两块）。 -/
theorem mem_Jt_res (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval)
    (hdT : DifferentiableAt ℝ TCSystem cCertR) (hd : DifferentiableAt ℝ residualFun u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo) (k : Fin 5) (c : Fin 12) :
    (Jt Hess (row5 k) c).Mem
      ((fderiv ℝ TCSystem cCertR (Pi.single c 1)) (row5 k)) := by
  by_cases hc : (c : ℕ) < 7
  · rw [eq_up7_of_lt hc]
    exact mem_Jt_res_z Hess hdT hd hWk hrad hWp k ⟨(c : ℕ), hc⟩
  · have hc7 : 7 ≤ (c : ℕ) := by omega
    rw [eq_up5_of_le hc7]
    exact mem_Jt_res_lam Hess hdT hd k ⟨(c : ℕ) - 7, by omega⟩

/-! ## 6. 二阶块：`residualFun` 的 Hessian 单元与 `adjointBlock` 的导数 -/

/-- `λ` 块与 Hessian 块共用的**一阶中间函数**：`g_{i,mm}(z) = (∂f_mm/∂z_i)(z)`。 -/
def gFun (i : Fin 7) (mm : Fin 5) (z : Fin 7 → ℝ) : ℝ :=
  (fderiv ℝ residualFun z (Pi.single i (1 : ℝ))) mm

/-- 取值泛函 `A ↦ (A (Pi.single i 1)) mm`（Hessian 单元的取值）。 -/
def evCLM (i : Fin 7) (mm : Fin 5) :
    ((Fin 7 → ℝ) →L[ℝ] (Fin 5 → ℝ)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj mm) ∘SL
    ((ContinuousLinearMap.apply ℝ (Fin 5 → ℝ)) (Pi.single i (1 : ℝ)))

theorem evCLM_apply (i : Fin 7) (mm : Fin 5) (A : (Fin 7 → ℝ) →L[ℝ] (Fin 5 → ℝ)) :
    evCLM i mm A = A (Pi.single i (1 : ℝ)) mm := by
  simp only [evCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.proj_apply]

/-- **二阶单元**（盒心）：`∂²f_mm/∂z_j∂z_i`（`i`：KKT 行指标，`j`：`z` 列指标）。 -/
def hessEntry (i j : Fin 7) (mm : Fin 5) : ℝ :=
  ((fderiv ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0) (Pi.single j (1 : ℝ)))
    (Pi.single i (1 : ℝ)) mm

theorem hasFDerivAt_gFun
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (i : Fin 7) (mm : Fin 5) :
    HasFDerivAt (gFun i mm)
      ((evCLM i mm).comp (fderiv ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)) u0 := by
  have h : HasFDerivAt (fun z : Fin 7 → ℝ => evCLM i mm (fderiv ℝ residualFun z))
      ((evCLM i mm).comp
        (fderiv ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)) u0 :=
    (ContinuousLinearMap.hasFDerivAt (evCLM i mm) (x := fderiv ℝ residualFun u0)).comp u0
      hadj.hasFDerivAt
  have he : (fun z : Fin 7 → ℝ => evCLM i mm (fderiv ℝ residualFun z)) = gFun i mm := by
    funext z
    rw [evCLM_apply]
    rfl
  rw [he] at h
  exact h

theorem hasFDerivAt_last5 (m : Fin 5) :
    HasFDerivAt (fun u : Fin 12 → ℝ => last5 u m)
      ((ContinuousLinearMap.proj (up5 m)) : (Fin 12 → ℝ) →L[ℝ] ℝ) cCertR := by
  have h : HasFDerivAt
      (fun u : Fin 12 → ℝ =>
        ((ContinuousLinearMap.proj (up5 m)) : (Fin 12 → ℝ) →L[ℝ] ℝ) u)
      ((ContinuousLinearMap.proj (up5 m)) : (Fin 12 → ℝ) →L[ℝ] ℝ) cCertR :=
    ContinuousLinearMap.hasFDerivAt _
  have he : (fun u : Fin 12 → ℝ =>
        ((ContinuousLinearMap.proj (up5 m)) : (Fin 12 → ℝ) →L[ℝ] ℝ) u)
      = fun u => last5 u m := by
    funext u
    rw [ContinuousLinearMap.proj_apply]
    rfl
  rw [he] at h
  exact h

theorem differentiableAt_adjointBlockRow
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (i : Fin 7) :
    DifferentiableAt ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) cCertR := by
  have hsum : (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i)
      = fun u => ∑ mm : Fin 5, last5 u mm * gFun i mm (first7 u) := rfl
  rw [hsum]
  refine DifferentiableAt.sum (𝕜 := ℝ) (u := Finset.univ)
    (A := fun mm : Fin 5 => fun u : Fin 12 → ℝ => last5 u mm * gFun i mm (first7 u)) ?_
  intro mm _
  exact (hasFDerivAt_last5 mm).differentiableAt.mul
    ((hasFDerivAt_gFun hadj i mm).comp cCertR (hasFDerivAt_first7 cCertR)).differentiableAt

/-- **`adjointBlock (first7 ·) (last5 ·) i` 沿方向 `v` 的导数**（值形态）。 -/
theorem fderiv_adjointBlock_val
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (i : Fin 7) (v : Fin 12 → ℝ) :
    (fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) cCertR) v
      = ∑ mm : Fin 5, ((last5 cCertR mm) * ((fderiv ℝ (gFun i mm) u0) (proj7CLM v))
          + (gFun i mm u0) * (v (up5 mm))) := by
  have hsum : (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i)
      = fun u => ∑ mm : Fin 5, last5 u mm * gFun i mm (first7 u) := rfl
  rw [hsum]
  have hdiff : ∀ mm : Fin 5, DifferentiableAt ℝ
      (fun u : Fin 12 → ℝ => last5 u mm * gFun i mm (first7 u)) cCertR := fun mm =>
    (hasFDerivAt_last5 mm).differentiableAt.mul
      ((hasFDerivAt_gFun hadj i mm).comp cCertR (hasFDerivAt_first7 cCertR)).differentiableAt
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun mm (u : Fin 12 → ℝ) => last5 u mm * gFun i mm (first7 u)) (fun mm _ => hdiff mm)]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun mm _ => ?_
  have hb : HasFDerivAt (fun u : Fin 12 → ℝ => gFun i mm (first7 u))
      ((fderiv ℝ (gFun i mm) u0).comp proj7CLM) cCertR := by
    have h := (hasFDerivAt_gFun hadj i mm).comp cCertR (hasFDerivAt_first7 cCertR)
    have he : (gFun i mm ∘ first7) = (fun u : Fin 12 → ℝ => gFun i mm (first7 u)) := rfl
    rw [he, ← (hasFDerivAt_gFun hadj i mm).fderiv] at h
    exact h
  have hprod : fderiv ℝ (fun u : Fin 12 → ℝ => last5 u mm * gFun i mm (first7 u)) cCertR
      = (last5 cCertR mm) • ((fderiv ℝ (gFun i mm) u0).comp proj7CLM)
        + (gFun i mm u0) • ((ContinuousLinearMap.proj (up5 mm)) :
            (Fin 12 → ℝ) →L[ℝ] ℝ) := by
    rw [show (fun u : Fin 12 → ℝ => last5 u mm * gFun i mm (first7 u))
        = ((fun u : Fin 12 → ℝ => last5 u mm)
          * (fun u : Fin 12 → ℝ => gFun i mm (first7 u))) from rfl]
    exact ((hasFDerivAt_last5 mm).mul hb).fderiv
  rw [hprod]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- **`λ` 列**：KKT 行的乘子方向导数 = `−(∂f_m/∂z_i)`。 -/
theorem fderiv_adjointBlock_up5
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (i : Fin 7) (m : Fin 5) :
    (fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) cCertR)
      (Pi.single (up5 m) (1 : ℝ)) = (fderiv ℝ residualFun u0 (Pi.single i (1 : ℝ))) m := by
  rw [fderiv_adjointBlock_val hadj i]
  have h0 : ∀ mm : Fin 5,
      (fderiv ℝ (gFun i mm) u0) (proj7CLM (Pi.single (up5 m) (1 : ℝ))) = 0 := fun mm => by
    rw [proj7CLM_single_up5, ContinuousLinearMap.map_zero]
  have h1 : ∀ mm : Fin 5,
      (Pi.single (up5 m) (1 : ℝ) : Fin 12 → ℝ) (up5 mm) = if mm = m then 1 else 0 := by
    intro mm
    by_cases h : mm = m
    · subst h
      rw [Pi.single_eq_same, if_pos rfl]
    · rw [Pi.single_eq_of_ne (i := up5 m) (i' := up5 mm) (fun hh => h (up5_inj hh)),
        if_neg h]
  rw [Finset.sum_eq_single m]
  · rw [h0 m, h1 m, if_pos rfl, mul_zero, mul_one, zero_add]
    rfl
  · intro mm _ hmm
    rw [h0 mm, h1 mm, if_neg hmm]
    simp only [mul_zero, add_zero]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

/-- **`z` 列**：KKT 行的 `z` 方向导数 = `−Σ_mm λ_mm · H_{i,j,m}`（Hessian 组合）。 -/
theorem fderiv_adjointBlock_up7
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (i j : Fin 7) :
    (fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) cCertR)
      (Pi.single (up7 j) (1 : ℝ))
      = ∑ mm : Fin 5, (last5 cCertR mm) * hessEntry i j mm := by
  rw [fderiv_adjointBlock_val hadj i]
  have h0 : ∀ mm : Fin 5,
      (fderiv ℝ (gFun i mm) u0) (proj7CLM (Pi.single (up7 j) (1 : ℝ))) = hessEntry i j mm := by
    intro mm
    rw [proj7CLM_single_up7, (hasFDerivAt_gFun hadj i mm).fderiv]
    simp only [ContinuousLinearMap.comp_apply, evCLM_apply, hessEntry]
  have h1 : ∀ mm : Fin 5,
      (Pi.single (up7 j) (1 : ℝ) : Fin 12 → ℝ) (up5 mm) = 0 := by
    intro mm
    rw [Pi.single_eq_of_ne (i := up7 j) (i' := up5 mm) (up7_ne_up5 j mm).symm]
  simp only [h0, h1, mul_zero, add_zero]

/-! ## 7. KKT 行的 `fderiv` 降低 -/

/-- `TCSystem` 的第 `5+i` 个分量作为 12 维函数。 -/
theorem TCSystem_row_eq_adjointBlock (i : Fin 7) :
    (fun u : Fin 12 → ℝ => TCSystem u (kkt12 i))
      = fun u => ((if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0)
          - adjointBlock (first7 u) (last5 u) i) := by
  funext u
  have h5 : ¬ (((kkt12 i : Fin 12) : ℕ) < 5) := by
    simp only [kkt12_val]
    omega
  rw [TCSystem, dif_neg h5, sub5_kkt12 i]

/-- **KKT 行 × `λ` 列**：真值 = `−(∂f_m/∂z_i)`。 -/
theorem fderiv_TCSystem_kkt_lam (hdT : DifferentiableAt ℝ TCSystem cCertR)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (i : Fin 7) (m : Fin 5) :
    (fderiv ℝ TCSystem cCertR (Pi.single (up5 m) (1 : ℝ))) (kkt12 i)
      = -((fderiv ℝ residualFun u0 (Pi.single i (1 : ℝ))) m) := by
  rw [fderiv_apply_val hdT (kkt12 i) (Pi.single (up5 m) (1 : ℝ)),
    TCSystem_row_eq_adjointBlock i]
  have hA : HasFDerivAt (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i)
      (fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) cCertR) cCertR :=
    (differentiableAt_adjointBlockRow hadj i).hasFDerivAt
  have hc : HasFDerivAt
      (fun _ : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0))
      (0 : (Fin 12 → ℝ) →L[ℝ] ℝ) cCertR :=
    hasFDerivAt_const _ _
  have hsub : fderiv ℝ (fun u : Fin 12 → ℝ =>
        (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0)
          - adjointBlock (first7 u) (last5 u) i) cCertR
      = 0 - fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) cCertR := by
    rw [show (fun u : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0)
          - adjointBlock (first7 u) (last5 u) i)
        = (fun _ : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0))
          - (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) from rfl]
    exact (hc.sub hA).fderiv
  rw [hsub, sub_apply]
  simp only [zero_apply, zero_sub]
  rw [fderiv_adjointBlock_up5 hadj i m]

/-- **KKT 行 × `z` 列**：真值 = `−Σ_mm (λ_mm · H_{i,j,mm})`。 -/
theorem fderiv_TCSystem_kkt_z (hdT : DifferentiableAt ℝ TCSystem cCertR)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (i j : Fin 7) :
    (fderiv ℝ TCSystem cCertR (Pi.single (up7 j) (1 : ℝ))) (kkt12 i)
      = -(∑ mm : Fin 5, (last5 cCertR mm) * hessEntry i j mm) := by
  rw [fderiv_apply_val hdT (kkt12 i) (Pi.single (up7 j) (1 : ℝ)),
    TCSystem_row_eq_adjointBlock i]
  have hA : HasFDerivAt (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i)
      (fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) cCertR) cCertR :=
    (differentiableAt_adjointBlockRow hadj i).hasFDerivAt
  have hc : HasFDerivAt
      (fun _ : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0))
      (0 : (Fin 12 → ℝ) →L[ℝ] ℝ) cCertR :=
    hasFDerivAt_const _ _
  have hsub : fderiv ℝ (fun u : Fin 12 → ℝ =>
        (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0)
          - adjointBlock (first7 u) (last5 u) i) cCertR
      = 0 - fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) cCertR := by
    rw [show (fun u : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0)
          - adjointBlock (first7 u) (last5 u) i)
        = (fun _ : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0))
          - (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) from rfl]
    exact (hc.sub hA).fderiv
  rw [hsub, sub_apply]
  simp only [zero_apply, zero_sub]
  rw [fderiv_adjointBlock_up7 hadj i j]

/-! ## 8. KKT 行的区间包络 -/

/-- **KKT 行 × `λ` 列**（35 格中的 35 格：`Jt` 的 `−(D m i)`）。 -/
theorem mem_Jt_kkt_lam (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval)
    (hdT : DifferentiableAt ℝ TCSystem cCertR) (hd : DifferentiableAt ℝ residualFun u0)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo) (i : Fin 7) (m : Fin 5) :
    (Jt Hess (kkt12 i) (up5 m)).Mem
      ((fderiv ℝ TCSystem cCertR (Pi.single (up5 m) (1 : ℝ))) (kkt12 i)) := by
  rw [Jt_kkt_lam, fderiv_TCSystem_kkt_lam hdT hadj i m]
  exact RatInterval.neg_mem (mem_D hd hWk hrad hWp m i)

/-- **KKT 行 × `z` 列**（49 格）：**条件形态** —— 前提 `hH` 是 `Hess` 必须满足的
**有限二阶区间义务**（`Hess i j mm` 包住 `∂²f_mm/∂z_j∂z_i`），**无条件部分到此为止**。 -/
theorem mem_Jt_kkt_z (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval)
    (hdT : DifferentiableAt ℝ TCSystem cCertR)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (hH : ∀ i j mm, (Hess i j mm).Mem (hessEntry i j mm)) (i j : Fin 7) :
    (Jt Hess (kkt12 i) (up7 j)).Mem
      ((fderiv ℝ TCSystem cCertR (Pi.single (up7 j) (1 : ℝ))) (kkt12 i)) := by
  rw [Jt_kkt_z, fderiv_TCSystem_kkt_z hdT hadj i j]
  refine RatInterval.neg_mem ?_
  have hdot := RatInterval.dot_mem (c := lamRat) (A := Hess i j)
    (x := fun mm : Fin 5 => hessEntry i j mm) (fun mm => hH i j mm)
  rw [dotR_eq_sum] at hdot
  have hsum_eq : (∑ mm : Fin 5, ((lamRat mm : ℚ) : ℝ) * hessEntry i j mm)
      = ∑ mm : Fin 5, (last5 cCertR mm) * hessEntry i j mm :=
    Finset.sum_congr rfl fun mm _ => by rw [lamRat_eq_last5 mm]
  rw [← hsum_eq]
  exact hdot

/-- **`Jt` 在盒心处的 12×12 完整包络**（唯一的条件前提是 `hH`：二阶块的有理区间义务）。 -/
theorem mem_Jt_at_center (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval)
    (hdT : DifferentiableAt ℝ TCSystem cCertR) (hd : DifferentiableAt ℝ residualFun u0)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo)
    (hH : ∀ i j mm, (Hess i j mm).Mem (hessEntry i j mm)) (r c : Fin 12) :
    (Jt Hess r c).Mem ((fderiv ℝ TCSystem cCertR (Pi.single c 1)) r) := by
  by_cases hr : (r : ℕ) < 5
  · exact mem_Jt_res Hess hdT hd hWk hrad hWp ⟨(r : ℕ), hr⟩ c
  · have hr5 : 5 ≤ (r : ℕ) := by omega
    rw [eq_kkt12_of_le hr5]
    by_cases hc : (c : ℕ) < 7
    · rw [eq_up7_of_lt hc]
      exact mem_Jt_kkt_z Hess hdT hadj hH ⟨(r : ℕ) - 5, by omega⟩ ⟨(c : ℕ), hc⟩
    · have hc7 : 7 ≤ (c : ℕ) := by omega
      rw [eq_up5_of_le hc7]
      exact mem_Jt_kkt_lam Hess hdT hd hadj hWk hrad hWp ⟨(r : ℕ) - 5, by omega⟩
        ⟨(c : ℕ) - 7, by omega⟩

/-! ## 9. H1 起步：`ρ_k` 二阶叶子的**实侧**底座

消费方契约见 `evidence/jt-build/HESS-SPEC.md`。本节先把 `ρ_k` 的**任意点**导数（不只是盒心）
写出来 —— 它同时是
* 二阶导（`z ↦ fderiv ρ z` 在 `u0` 附近的形式）的底座，
* **盒上求值**（Lead ⑤ 的点→球路线 1）的底座。 -/

/-- `radicand` `W_k(x) = (x 6)² − sin²(a_k x)`（`x` 任意点；盒心处即 `Wk k`）。 -/
def Wfun (k : Fin 9) (x : Fin 7 → ℝ) : ℝ :=
  (x 6) ^ 2 - (Real.sin (angleVec (pad12 x) k)) ^ 2

/-- `W_k` 在任意点的导数。 -/
def dWfun (k : Fin 9) (x : Fin 7 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  (2 * x 6) • coord 6
    - (2 * Real.sin (angleVec (pad12 x) k)) • ((Real.cos (angleVec (pad12 x) k)) • daCLM k)

/-- `a_k` 在**任意点** `x` 处的导数（`a` 是仿射的 ⇒ 每点同一 CLM）。 -/
theorem hasFDerivAt_angleVec_any (k : Fin 9) (x : Fin 7 → ℝ) :
    HasFDerivAt (fun z : Fin 7 → ℝ => angleVec (pad12 z) k) (daCLM k) x := by
  have hlin : HasFDerivAt (fun z : Fin 7 → ℝ => ∑ i : Fin 7, (dAngle k i : ℝ) * z i)
      (∑ i : Fin 7, (dAngle k i : ℝ) • coord i) x := by
    rw [show (fun z : Fin 7 → ℝ => ∑ i : Fin 7, (dAngle k i : ℝ) * z i)
        = ∑ i : Fin 7, fun z : Fin 7 → ℝ => (dAngle k i : ℝ) * z i from rfl]
    refine HasFDerivAt.sum fun i _ => ?_
    have h1 : HasFDerivAt (⇑(coord i)) (coord i) x :=
      ContinuousLinearMap.hasFDerivAt (f := coord i) (x := x)
    exact h1.const_mul ((dAngle k i : ℝ))
  have h : (fun z : Fin 7 → ℝ => angleVec (pad12 z) k)
      = fun z => angleVec (pad12 0) k + ∑ i : Fin 7, (dAngle k i : ℝ) * z i := by
    funext z
    exact angleVec_pad12_affine k z
  rw [h, daCLM]
  exact hlin.const_add (angleVec (pad12 0) k)

/-- `W_k` 在**任意点** `x` 处的导数（`Wfun k`/`dWfun k x`）。 -/
theorem hasFDerivAt_Wfun (k : Fin 9) (x : Fin 7 → ℝ) :
    HasFDerivAt (Wfun k) (dWfun k x) x := by
  have hR : HasFDerivAt (fun z : Fin 7 → ℝ => z 6) (coord 6) x :=
    ContinuousLinearMap.hasFDerivAt (f := coord 6) (x := x)
  have hR2 : HasFDerivAt (fun z : Fin 7 → ℝ => (z 6) ^ 2) ((2 * x 6) • coord 6) x := by
    have h := hR.pow 2
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using h
  have hs : HasFDerivAt (fun z : Fin 7 → ℝ => Real.sin (angleVec (pad12 z) k))
      ((Real.cos (angleVec (pad12 x) k)) • daCLM k) x :=
    (hasFDerivAt_angleVec_any k x).sin
  have hs2 : HasFDerivAt (fun z : Fin 7 → ℝ => (Real.sin (angleVec (pad12 z) k)) ^ 2)
      ((2 * Real.sin (angleVec (pad12 x) k))
        • ((Real.cos (angleVec (pad12 x) k)) • daCLM k)) x := by
    have h := hs.pow 2
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using h
  exact hR2.sub hs2

/-- `ρ_k` 在任意点的导数 CLM（`W_k(x) ≠ 0`）。 -/
def drhoAt (k : Fin 9) (x : Fin 7 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  -(Real.sin (angleVec (pad12 x) k)) • daCLM k
    - (1 / (2 * Real.sqrt (Wfun k x))) • dWfun k x

theorem hasFDerivAt_rhoK_any (k : Fin 9) (x : Fin 7 → ℝ) (hW : Wfun k x ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) (drhoAt k x) x := by
  have heq : (fun z : Fin 7 → ℝ => rhoK (pad12 z) k)
      = fun z => Real.cos (angleVec (pad12 z) k)
        - Real.sqrt ((z 6) ^ 2 - (Real.sin (angleVec (pad12 z) k)) ^ 2) := by
    funext z
    rw [rhoK_eq]
    rfl
  rw [heq, drhoAt]
  exact ((hasFDerivAt_angleVec_any k x).cos).sub ((hasFDerivAt_Wfun k x).sqrt hW)

/-- **`u0` 附近 `fderiv ρ_k` = 显式 `drhoAt k`**（二阶导与盒上求值都靠它）。 -/
theorem drhoAt_eq_fderiv (k : Fin 9) (hW : 0 < Wk k) :
    ∀ᶠ x in nhds u0, fderiv ℝ (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) x = drhoAt k x := by
  have hcont : ContinuousAt
      (fun x : Fin 7 → ℝ => (x 6) ^ 2 - (Real.sin (angleVec (pad12 x) k)) ^ 2) u0 :=
    (hasFDerivAt_Wfun k u0).continuousAt
  filter_upwards [hcont.eventually_ne (ne_of_gt hW)] with x hx
  exact (hasFDerivAt_rhoK_any k x hx).fderiv

/-- `∂W_k/∂z_i` 在盒心的显式值（`ρ` 二阶公式的构件）。 -/
def WkD1 (k : Fin 9) (i : Fin 7) : ℝ :=
  2 * u0 6 * (if i = 6 then (1 : ℝ) else 0)
    - 2 * Real.sin (angleVec (pad12 u0) k) * Real.cos (angleVec (pad12 u0) k) * (dAngle k i : ℝ)

/-- `∂²W_k/∂z_i∂z_j` 在盒心的显式值。 -/
def WkD2 (k : Fin 9) (i j : Fin 7) : ℝ :=
  2 * (if i = 6 then (1 : ℝ) else 0) * (if j = 6 then (1 : ℝ) else 0)
    - 2 * Real.cos (2 * angleVec (pad12 u0) k) * (dAngle k i : ℝ) * (dAngle k j : ℝ)

/-- `Eρ k i`：`∂ρ_k/∂z_i` 作为 `x` 的函数（`= fderiv ρ_k x (single i 1)` 在 `u0` 附近）。 -/
def Eρ (k : Fin 9) (i : Fin 7) (x : Fin 7 → ℝ) : ℝ :=
  (drhoAt k x) (Pi.single i (1 : ℝ))

theorem Eρ_eq (k : Fin 9) (i : Fin 7) (x : Fin 7 → ℝ) :
    Eρ k i x = -(Real.sin (angleVec (pad12 x) k)) * (dAngle k i : ℝ)
      - (1 / (2 * Real.sqrt (Wfun k x)))
        * ((2 * x 6) * (if i = 6 then (1 : ℝ) else 0)
          - 2 * Real.sin (angleVec (pad12 x) k) * Real.cos (angleVec (pad12 x) k)
            * (dAngle k i : ℝ)) := by
  simp only [Eρ, drhoAt, dWfun, sub_apply, smul_apply, smul_eq_mul, daCLM_apply_single,
    coord_six_apply_single]
  ring

/-! ## 10. H1 叶子：`ArcC`（弧端点 `B_k`，9×2）—— **不依赖 `ρ''`**

接口口径（与 `jth-assembly` 冻结，2026-09-27）：只交**原始叶子**（不替拼 `U_k`/`Δ`）；
**值形态** `((fderiv ℝ (fun y => fderiv ℝ Leaf y) u0) (Pi.single j 1)) (Pi.single i 1) = <显式值>`
（`i` = 一阶方向、`j` = 二阶方向，与 `secondPartial`/`hessEntry` 一致）。
`B_k = (cos φ_k, sin φ_k)`、`φ_k = θ_k + a_k` **仿射** ⇒ `∂²B = −cos/sin φ_k·(dθ+dα)_i(dθ+dα)_j`。

**形态纪律（`RingC`/`WyF` 与 `ρ''` 一律照此；Lead 已裁决）**：结论**保留原始叶子形态**
`(2√W)⁻¹` / `((2√W)²)⁻¹` / `toSpanSingleton`，**不做代数归一化**（归一化推给消费侧，与 `jth-assembly`
H3 的 `invPos (twoSqrtWkIv k)`、`invPos (sq (twoSqrtWkIv k))` 一一对应）。
**理由（已付 5 次尝试的代价，别重试）**：`ring`/`nlinarith` 把 `√W` 与 `W` 当**不同原子**（缺 `√W·√W = W`）；
`field_simp;ring`、`field_simp;rw[√W²=W];ring`、`rw [← Real.sq_sqrt] at *`（会**钻进 `√` 内部**造 `√(√X²)`）、
`simp only [pow_succ,…]`、`field_simp;nlinarith [√W·√W=W]` **五条全失败**。
**收尾用 `change` 一步钉形状 + 一次 `exact`/`rw`**（模板 = `evidence/jth-assembly/H2Dev.lean` 的 T2，已在根内，
公理画像只含 `[propext, Classical.choice, Quot.sound]`）。
**注意**：T2 在 `ResidualDerivJTHess.lean`（它 `import` 本模块）⇒ **本模块不能 import 它**（循环）；`RingC`/`WyF`
须落在**同时 import 双方**的新文件里（待 Lead 裁决文件名）。 -/

/-- jt-assembly 冻结的叶子：`B_k` 的第 `c` 个坐标（`c=0` → `cos φ_k`，`c=1` → `sin φ_k`）。 -/
def ArcC (k : Fin 9) (c : Fin 2) : (Fin 7 → ℝ) → ℝ := fun z => (arcEnd (pad12 z) k).ofLp c

/-- `φ_k = θ_k + a_k`（`z` 的仿射函数）。 -/
def phiA (k : Fin 9) (z : Fin 7 → ℝ) : ℝ :=
  thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k

/-- `φ_k` 的导数 CLM（仿射 ⇒ 与点无关）。 -/
def phiCLM (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ℝ := dthetaCLM k + daCLM k

theorem ArcC_zero (k : Fin 9) (z : Fin 7 → ℝ) : ArcC k 0 z = Real.cos (phiA k z) := rfl

theorem ArcC_one (k : Fin 9) (z : Fin 7 → ℝ) : ArcC k 1 z = Real.sin (phiA k z) := rfl

/-- `θ_k` 在**任意点**的导数（仿射）。 -/
theorem hasFDerivAt_thetaOf_any (k : Fin 9) (z : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => thetaOf (angleVec (pad12 y)) k) (dthetaCLM k) z := by
  have hlin : HasFDerivAt (fun y : Fin 7 → ℝ => ∑ i : Fin 7, (dTheta k i : ℝ) * y i)
      (∑ i : Fin 7, (dTheta k i : ℝ) • coord i) z := by
    rw [show (fun y : Fin 7 → ℝ => ∑ i : Fin 7, (dTheta k i : ℝ) * y i)
        = ∑ i : Fin 7, fun y : Fin 7 → ℝ => (dTheta k i : ℝ) * y i from rfl]
    refine HasFDerivAt.sum fun i _ => ?_
    exact (ContinuousLinearMap.hasFDerivAt (f := coord i) (x := z)).const_mul ((dTheta k i : ℝ))
  have h : (fun y : Fin 7 → ℝ => thetaOf (angleVec (pad12 y)) k)
      = fun y => thetaOf (angleVec (pad12 0)) k + ∑ i : Fin 7, (dTheta k i : ℝ) * y i := by
    funext y
    exact thetaOf_angleVec_affine k y
  rw [h, dthetaCLM]
  exact hlin.const_add (thetaOf (angleVec (pad12 0)) k)

/-- `φ_k` 在任意点的导数。 -/
theorem hasFDerivAt_phiA (k : Fin 9) (z : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => phiA k y) (phiCLM k) z := by
  rw [show (fun y : Fin 7 → ℝ => phiA k y)
      = (fun y : Fin 7 → ℝ => thetaOf (angleVec (pad12 y)) k)
        + (fun y : Fin 7 → ℝ => angleVec (pad12 y) k) from rfl]
  exact (hasFDerivAt_thetaOf_any k z).add (hasFDerivAt_angleVec_any k z)

theorem fderiv_ArcC_zero (k : Fin 9) (z : Fin 7 → ℝ) :
    fderiv ℝ (ArcC k 0) z = (-(Real.sin (phiA k z))) • phiCLM k := by
  have hc : ArcC k 0 = fun y : Fin 7 → ℝ => Real.cos (phiA k y) := by
    funext y
    exact ArcC_zero k y
  rw [hc]
  exact ((hasFDerivAt_phiA k z).cos).fderiv

theorem fderiv_ArcC_one (k : Fin 9) (z : Fin 7 → ℝ) :
    fderiv ℝ (ArcC k 1) z = (Real.cos (phiA k z)) • phiCLM k := by
  have hc : ArcC k 1 = fun y : Fin 7 → ℝ => Real.sin (phiA k y) := by
    funext y
    exact ArcC_one k y
  rw [hc]
  exact ((hasFDerivAt_phiA k z).sin).fderiv

/-- **`ArcC` 的二阶偏导（实侧，值形态）**：
`∂²(cos φ_k)/∂z_i∂z_j = −cos φ_k·(dθ+dα)_i(dθ+dα)_j`（`sin` 同型）。 -/
theorem secondPartial_ArcC (k : Fin 9) (c : Fin 2) (i j : Fin 7) :
    ((fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ (ArcC k c) y) u0) (Pi.single j 1)) (Pi.single i 1)
      = -(if c = 0 then Real.cos (phiA k u0) else Real.sin (phiA k u0))
        * ((dTheta k i : ℝ) + (dAngle k i : ℝ)) * ((dTheta k j : ℝ) + (dAngle k j : ℝ)) := by
  by_cases hc0 : c = 0
  · subst hc0
    have h1 : (fun y : Fin 7 → ℝ => fderiv ℝ (ArcC k 0) y)
        = fun y : Fin 7 → ℝ => (-(Real.sin (phiA k y))) • phiCLM k := by
      funext y
      exact fderiv_ArcC_zero k y
    have hL2 : HasFDerivAt (fun y : Fin 7 → ℝ => (-(Real.sin (phiA k y))) • phiCLM k)
        ((ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)).comp
          (-(Real.cos (phiA k u0) • phiCLM k))) u0 := by
      have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k))
        (x := -(Real.sin (phiA k u0)))).comp u0 ((hasFDerivAt_phiA k u0).sin.neg)
      have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)) ∘
            (-(fun x : Fin 7 → ℝ => Real.sin (phiA k x))))
          = fun y : Fin 7 → ℝ => (-(Real.sin (phiA k y))) • phiCLM k := by
        funext y
        rw [Function.comp_apply, Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply]
      rw [he] at h
      exact h
    rw [h1, hL2.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_apply, smul_eq_mul, neg_apply, phiCLM, add_apply, dthetaCLM_apply_single,
      daCLM_apply_single, if_true]
    ring
  · have hc1 : c = 1 := by fin_cases c <;> simp_all
    subst hc1
    have h1 : (fun y : Fin 7 → ℝ => fderiv ℝ (ArcC k 1) y)
        = fun y : Fin 7 → ℝ => (Real.cos (phiA k y)) • phiCLM k := by
      funext y
      exact fderiv_ArcC_one k y
    have hL2 : HasFDerivAt (fun y : Fin 7 → ℝ => (Real.cos (phiA k y)) • phiCLM k)
        ((ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)).comp
          ((-(Real.sin (phiA k u0))) • phiCLM k)) u0 := by
      have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k))
        (x := Real.cos (phiA k u0))).comp u0 (hasFDerivAt_phiA k u0).cos
      have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)) ∘
            (fun x : Fin 7 → ℝ => Real.cos (phiA k x)))
          = fun y : Fin 7 → ℝ => (Real.cos (phiA k y)) • phiCLM k := by
        funext y
        rw [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
      rw [he] at h
      exact h
    rw [h1, hL2.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_apply, smul_eq_mul, phiCLM, add_apply, dthetaCLM_apply_single,
      daCLM_apply_single, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    ring

/-! ### `arc2`：`ArcC` 二阶偏导的区间包络（Lag 级三角叶子 `cosTAIv`/`sinTAIv`） -/

/-- `∂²B_{k,c}/∂z_i∂z_j` 的区间包络（`c=0` 用 `cosTAIv`，`c=1` 用 `sinTAIv`）。 -/
def arc2 (k : Fin 9) (c : Fin 2) (i j : Fin 7) : RatInterval :=
  RatInterval.neg (RatInterval.mul (RatInterval.mul
    (RatInterval.ofRat (((dTheta k i + dAngle k i : ℤ) : ℚ)))
    (RatInterval.ofRat (((dTheta k j + dAngle k j : ℤ) : ℚ))))
    (if c = 0 then cosTAIv k else sinTAIv k))

theorem mem_arc2 (k : Fin 9) (c : Fin 2) (i j : Fin 7) :
    (arc2 k c i j).Mem
      (-(if c = 0 then Real.cos (phiA k u0) else Real.sin (phiA k u0))
        * ((dTheta k i : ℝ) + (dAngle k i : ℝ)) * ((dTheta k j : ℝ) + (dAngle k j : ℝ))) := by
  by_cases hc0 : c = 0
  · subst hc0
    have h := RatInterval.neg_mem (RatInterval.mul_mem (RatInterval.mul_mem
      (RatInterval.ofRat_mem (((dTheta k i + dAngle k i : ℤ) : ℚ)))
      (RatInterval.ofRat_mem (((dTheta k j + dAngle k j : ℤ) : ℚ))))
      (cosTAIv_mem k))
    simpa [arc2, if_true, phiA, RatInterval.ofRat, push_cast, mul_comm, mul_left_comm,
      mul_assoc] using h
  · have hc1 : c = 1 := by fin_cases c <;> simp_all
    subst hc1
    have h := RatInterval.neg_mem (RatInterval.mul_mem (RatInterval.mul_mem
      (RatInterval.ofRat_mem (((dTheta k i + dAngle k i : ℤ) : ℚ)))
      (RatInterval.ofRat_mem (((dTheta k j + dAngle k j : ℤ) : ℚ))))
      (sinTAIv_mem k))
    simpa [arc2, if_neg (by decide : ¬ ((1 : Fin 2) = 0)), phiA, RatInterval.ofRat, push_cast,
      mul_comm, mul_left_comm, mul_assoc] using h

end N11Formalization

