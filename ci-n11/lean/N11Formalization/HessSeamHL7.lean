import N11Formalization.HessSeamBridge

/-!
# hess-seam / `hL7` 第 ①-步：**分量投影链**

**目标**（`hL7` 的第一半）：把
`hessEntry i j mm = (fderiv ℝ (gFun i mm) u0) (Pi.single j 1)`（= **CLM 值**二阶的 `mm` 分量，根内已有）
接到
`secondPartial (fun z => residualFun z mm) u0 i j`（= **标量**函数 `f_mm` 的二阶偏导，L7 商法则的自然入口）。

**为什么这不是按定义成立**：`hessEntry` 走「`(Fin 5 → ℝ)` 值 CLM 的二阶导数在 `e_j` 处的**取值**再取 `mm` 分量」，
`secondPartial` 走「标量函数 `f_mm` 的二阶导数」。两者的桥 = **`fderiv` 与分量投影可交换**：
`fderiv ℝ (fun w => residualFun w mm) z = (ContinuousLinearMap.proj mm) ∘ (fderiv ℝ residualFun z)`
—— 而这条**只在 `residualFun` 于 `z` 可微时成立**（`fderiv` 在不可微点取 `0`：若 `f` 不可微而其某个分量可微，
两侧就差一个非零的标量导数）。

⇒ **本件因此多带一条前提** `hd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ residualFun z`（**不可由 `hadj` 推出**：
取 `residualFun = (光滑分量, Weierstrass 分量)`，则 `fderiv residualFun ≡ 0`（`hadj` 甚至无条件成立，因常值映射光滑），
而光滑分量的 `secondPartial ≠ 0` ⇒ 结论会假）。这条前提与本工程 T1/T2/T3 的既有形态
（`∀ᶠ z in nhds u0, DifferentiableAt ℝ g z`）**同形** ✓，故消费侧不增加负担。

**证明骨架**（`P := proj mm`、`Φ := compL ℝ (Fin 7 → ℝ) (Fin 5 → ℝ) ℝ P`（`L ↦ P ∘SL L`）、`H := fderiv ℝ (fun z => fderiv ℝ residualFun z) u0`）：

1. `∀ᶠ z`，`fderiv ℝ (fun w => residualFun w mm) z = Φ (fderiv ℝ residualFun z)`（链式 + `compL_apply`）；
2. 故 `fderiv ℝ (fun y => fderiv ℝ (fun w => residualFun w mm) y) u0 = Φ ∘SL H`
   （`Filter.EventuallyEq.fderiv_eq` + `HadFDerivAt.comp`）；
3. 两端都在 `(H (Pi.single j 1)) (Pi.single i 1) mm` 处取值：
   左端走根内 `hessEntry_eq_fderiv_gFun` + `hasFDerivAt_gFun` + `evCLM_apply`；
   右端走 `secondPartial` 定义 + 第 2 条 + `comp_apply`/`compL_apply`/`proj_apply`。

**口径**：盒心 `u0`；无 `sorry`/公理/`native_decide`。
-/

noncomputable section

namespace N11Formalization

namespace HessSeam

open RatInterval

/-- **`hL7` 第 ①-步（分量投影链）**：CLM 值二阶的 `mm` 分量 = 标量分量函数的二阶偏导。

前提 `hd`（`residualFun` 在 `u0` **邻域**内可微）是**本质的**（见件头：`hadj` 单独不够）。 -/
theorem hessEntry_eq_secondPartial_residualFun
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (hd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ residualFun z)
    (i j : Fin 7) (mm : Fin 5) :
    hessEntry i j mm = secondPartial (fun z : Fin 7 → ℝ => residualFun z mm) u0 i j := by
  let P : (Fin 5 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj mm
  let Φ : ((Fin 7 → ℝ) →L[ℝ] (Fin 5 → ℝ)) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin 7 → ℝ) (Fin 5 → ℝ) ℝ) P
  let H : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] (Fin 5 → ℝ)) :=
    fderiv ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0
  -- 第 1 步：`∀ᶠ z`，标量分量的 `fderiv` = 投影 ∘ CLM 的 `fderiv`
  have hpt : (fun z : Fin 7 → ℝ => fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w mm) z)
      =ᶠ[nhds u0] fun z : Fin 7 → ℝ => Φ (fderiv ℝ residualFun z) := by
    filter_upwards [hd] with z hz
    have hfun : (P ∘ residualFun) = fun w : Fin 7 → ℝ => residualFun w mm := by
      funext w
      rw [Function.comp_apply, ContinuousLinearMap.proj_apply]
    have hcomp : HasFDerivAt (P ∘ residualFun) (P ∘SL fderiv ℝ residualFun z) z :=
      (ContinuousLinearMap.hasFDerivAt P).comp z hz.hasFDerivAt
    rw [hfun] at hcomp
    rw [hcomp.fderiv, ContinuousLinearMap.compL_apply]
  -- 第 2 步：`fderiv` 与投影交换（二阶）
  have hM : fderiv ℝ (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w mm) y) u0 = Φ ∘SL H := by
    rw [hpt.fderiv_eq]
    exact ((ContinuousLinearMap.hasFDerivAt Φ).comp u0 hadj.hasFDerivAt).fderiv
  -- 第 3 步左：`hessEntry` = 同一个正规形
  have hleft : hessEntry i j mm = (H (Pi.single j 1)) (Pi.single i 1) mm := by
    rw [hessEntry_eq_fderiv_gFun hadj i j mm, (hasFDerivAt_gFun hadj i mm).fderiv,
      ContinuousLinearMap.comp_apply, evCLM_apply]
  -- 第 3 步右：`secondPartial` = 同一个正规形
  have hright : secondPartial (fun z : Fin 7 → ℝ => residualFun z mm) u0 i j
      = (H (Pi.single j 1)) (Pi.single i 1) mm := by
    rw [secondPartial, hM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [hleft, hright]

/-! ## 2. `hL7` 第 ②-步的**节点层**：`Δ` 的二阶 CLM（`√S` 商法则的输入）

`S_k := Δx_k² + Δy_k²`（乘号形态，便于 T3/T1 直接吃；终点再用 `pow_two` 换成 `^2`）。
本节的三个节点族（每个 `k` 一条）：`hasFDerivAt_DeltaX/Y`（一阶，T3 的 `hφ`）、
`hasFDerivAt_fderiv_DeltaX/Y`（二阶）、`eventually_diff_DeltaX/Y`（T3/T1 的 `∀ᶠ`）。 -/

/-- `Δx_k` 的二阶 CLM（5 支镜像 `Apt`/`Bpt` 的差；hub 侧仿射 ⇒ `0`）。 -/
def L2DeltaX : Fin 5 → (Fin 7 → ℝ) →L[ℝ] (Fin 7 → ℝ) →L[ℝ] ℝ
  | 0 => L2UvecC0 1 - 0
  | 1 => L2UvecC0 2 - 0
  | 2 => L2UvecC0 3 - 0
  | 3 => L2UvecC0 8 - 0
  | 4 => 0 - L2RingC0 6

/-- `Δy_k` 的二阶 CLM。 -/
def L2DeltaY : Fin 5 → (Fin 7 → ℝ) →L[ℝ] (Fin 7 → ℝ) →L[ℝ] ℝ
  | 0 => L2UvecC1 1 - 0
  | 1 => L2UvecC1 2 - 0
  | 2 => L2UvecC1 3 - 0
  | 3 => L2UvecC1 8 - 0
  | 4 => L2Wy - L2RingC1 6

theorem hasFDerivAt_fderiv_DeltaX (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (DeltaX k) z) (L2DeltaX k) u0 := by
  fin_cases k
  · have hA : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) 1).ofLp 0) z) (L2UvecC0 1) u0 :=
      hasFDerivAt_fderiv_UvecC0 1 h0 h1
    have hB : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0) z) 0 u0 :=
      hasFDerivAt_fderiv_of_eq_clm hub1xF_eq
    exact hasFDerivAt_fderiv_sub hA hB (eventually_diff_UvecC0 1 h0 h1)
      (eventually_diff_of_eq_clm hub1xF_eq)
  · have hA : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) 2).ofLp 0) z) (L2UvecC0 2) u0 :=
      hasFDerivAt_fderiv_UvecC0 2 h0 h1
    have hB : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0) z) 0 u0 :=
      hasFDerivAt_fderiv_of_eq_clm hub0xF_eq
    exact hasFDerivAt_fderiv_sub hA hB (eventually_diff_UvecC0 2 h0 h1)
      (eventually_diff_of_eq_clm hub0xF_eq)
  · have hA : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) 3).ofLp 0) z) (L2UvecC0 3) u0 :=
      hasFDerivAt_fderiv_UvecC0 3 h0 h1
    have hB : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0) z) 0 u0 :=
      hasFDerivAt_fderiv_of_eq_clm hub0xF_eq
    exact hasFDerivAt_fderiv_sub hA hB (eventually_diff_UvecC0 3 h0 h1)
      (eventually_diff_of_eq_clm hub0xF_eq)
  · have hA : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) 8).ofLp 0) z) (L2UvecC0 8) u0 :=
      hasFDerivAt_fderiv_UvecC0 8 h0 h1
    have hB : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0) z) 0 u0 :=
      hasFDerivAt_fderiv_of_eq_clm hub1xF_eq
    exact hasFDerivAt_fderiv_sub hA hB (eventually_diff_UvecC0 8 h0 h1)
      (eventually_diff_of_eq_clm hub1xF_eq)
  · have hW : 0 < Wfun 6 u0 := by
      rw [Wfun_u0_eq_Wk]
      exact lt_of_lt_of_le (by exact_mod_cast hW6) (mem_lo_le (WkIv_mem 6))
    have hA : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0) z) 0 u0 :=
      hasFDerivAt_fderiv_wxF
    have hB : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) 6).ofLp 0) z) (L2RingC0 6) u0 :=
      hasFDerivAt_fderiv_ringC0 6 hW
    exact hasFDerivAt_fderiv_sub hA hB eventually_diff_wxF (eventually_diff_ringC0 6 hW)

theorem hasFDerivAt_fderiv_DeltaY (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (DeltaY k) z) (L2DeltaY k) u0 := by
  have hWp' : 0 < Wpf u0 := by
    rw [Wpf_u0]
    exact lt_of_lt_of_le (by exact_mod_cast hWp) (mem_lo_le WpIv_mem)
  fin_cases k
  · have hA : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) 1).ofLp 1) z) (L2UvecC1 1) u0 :=
      hasFDerivAt_fderiv_UvecC1 1 h0 h1
    have hB : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1) z) 0 u0 :=
      hasFDerivAt_fderiv_of_eq_const hub1yF_eq
    exact hasFDerivAt_fderiv_sub hA hB (eventually_diff_UvecC1 1 h0 h1)
      (eventually_diff_of_eq_const hub1yF_eq)
  · have hA : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) 2).ofLp 1) z) (L2UvecC1 2) u0 :=
      hasFDerivAt_fderiv_UvecC1 2 h0 h1
    have hB : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1) z) 0 u0 :=
      hasFDerivAt_fderiv_of_eq_const hub0yF_eq
    exact hasFDerivAt_fderiv_sub hA hB (eventually_diff_UvecC1 2 h0 h1)
      (eventually_diff_of_eq_const hub0yF_eq)
  · have hA : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) 3).ofLp 1) z) (L2UvecC1 3) u0 :=
      hasFDerivAt_fderiv_UvecC1 3 h0 h1
    have hB : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1) z) 0 u0 :=
      hasFDerivAt_fderiv_of_eq_const hub0yF_eq
    exact hasFDerivAt_fderiv_sub hA hB (eventually_diff_UvecC1 3 h0 h1)
      (eventually_diff_of_eq_const hub0yF_eq)
  · have hA : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) 8).ofLp 1) z) (L2UvecC1 8) u0 :=
      hasFDerivAt_fderiv_UvecC1 8 h0 h1
    have hB : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1) z) 0 u0 :=
      hasFDerivAt_fderiv_of_eq_const hub1yF_eq
    exact hasFDerivAt_fderiv_sub hA hB (eventually_diff_UvecC1 8 h0 h1)
      (eventually_diff_of_eq_const hub1yF_eq)
  · have hW : 0 < Wfun 6 u0 := by
      rw [Wfun_u0_eq_Wk]
      exact lt_of_lt_of_le (by exact_mod_cast hW6) (mem_lo_le (WkIv_mem 6))
    have hA : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1) z) L2Wy u0 :=
      hasFDerivAt_fderiv_wyF hWp'
    have hB : HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) 6).ofLp 1) z) (L2RingC1 6) u0 :=
      hasFDerivAt_fderiv_ringC1 6 hW
    exact hasFDerivAt_fderiv_sub hA hB (eventually_diff_wyF hWp') (eventually_diff_ringC1 6 hW)

theorem eventually_diff_DeltaX (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (DeltaX k) z := by
  fin_cases k
  · exact (eventually_diff_UvecC0 1 h0 h1).and (eventually_diff_of_eq_clm hub1xF_eq) |>.mono
      (fun z hz => hz.1.sub hz.2)
  · exact (eventually_diff_UvecC0 2 h0 h1).and (eventually_diff_of_eq_clm hub0xF_eq) |>.mono
      (fun z hz => hz.1.sub hz.2)
  · exact (eventually_diff_UvecC0 3 h0 h1).and (eventually_diff_of_eq_clm hub0xF_eq) |>.mono
      (fun z hz => hz.1.sub hz.2)
  · exact (eventually_diff_UvecC0 8 h0 h1).and (eventually_diff_of_eq_clm hub1xF_eq) |>.mono
      (fun z hz => hz.1.sub hz.2)
  · have hW : 0 < Wfun 6 u0 := by
      rw [Wfun_u0_eq_Wk]
      exact lt_of_lt_of_le (by exact_mod_cast hW6) (mem_lo_le (WkIv_mem 6))
    exact eventually_diff_wxF.and (eventually_diff_ringC0 6 hW) |>.mono
      (fun z hz => hz.1.sub hz.2)

theorem eventually_diff_DeltaY (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (DeltaY k) z := by
  have hWp' : 0 < Wpf u0 := by
    rw [Wpf_u0]
    exact lt_of_lt_of_le (by exact_mod_cast hWp) (mem_lo_le WpIv_mem)
  fin_cases k
  · exact (eventually_diff_UvecC1 1 h0 h1).and (eventually_diff_of_eq_const hub1yF_eq) |>.mono
      (fun z hz => hz.1.sub hz.2)
  · exact (eventually_diff_UvecC1 2 h0 h1).and (eventually_diff_of_eq_const hub0yF_eq) |>.mono
      (fun z hz => hz.1.sub hz.2)
  · exact (eventually_diff_UvecC1 3 h0 h1).and (eventually_diff_of_eq_const hub0yF_eq) |>.mono
      (fun z hz => hz.1.sub hz.2)
  · exact (eventually_diff_UvecC1 8 h0 h1).and (eventually_diff_of_eq_const hub1yF_eq) |>.mono
      (fun z hz => hz.1.sub hz.2)
  · have hW : 0 < Wfun 6 u0 := by
      rw [Wfun_u0_eq_Wk]
      exact lt_of_lt_of_le (by exact_mod_cast hW6) (mem_lo_le (WkIv_mem 6))
    exact eventually_diff_wyF hWp' |>.and (eventually_diff_ringC1 6 hW) |>.mono
      (fun z hz => hz.1.sub hz.2)

/-- `Δx_k` 的**一阶**节点（`∀ᶠ` 事实在 `u0` 处读出；T3 的 `hφ`）。 -/
theorem hasFDerivAt_DeltaX (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) :
    HasFDerivAt (DeltaX k) (fderiv ℝ (DeltaX k) u0) u0 :=
  ((eventually_diff_DeltaX k h0 h1 hW6).self_of_nhds).hasFDerivAt

/-- `Δy_k` 的一阶节点。 -/
theorem hasFDerivAt_DeltaY (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    HasFDerivAt (DeltaY k) (fderiv ℝ (DeltaY k) u0) u0 :=
  ((eventually_diff_DeltaY k h0 h1 hW6 hWp).self_of_nhds).hasFDerivAt

/-! ## 3. `SRad` 的三节点 ＋ 两条**取值**引理（`√S` 商法则的直接输入）

`S_k := Δx_k·Δx_k + Δy_k·Δy_k`（**乘号形态**：T3/T1 的输出函数逐字匹配，避开 `^2` 的 `congr` 步骤；
`SRad k u0 = radR k` 在终点用 `pow_two` 换回 ✓）。

**收尾纪律（本轮试错）**：`SRad` 是具名 def，而 `hsum.fderiv` 的 LHS 是**展开形态**
⇒ `rw [hsum.fderiv]` 在 `reducible` 透明度下**匹配不上**具名形态 ✗ ⇒ 正解：先 `show`（defeq 容错）
把目标摊开成展开形态，再 `rw` ✓。 -/

/-- `S_k := Δx_k·Δx_k + Δy_k·Δy_k`（`u0` 处 = `radR k`）。 -/
def SRad (k : Fin 5) : (Fin 7 → ℝ) → ℝ :=
  fun z => DeltaX k z * DeltaX k z + DeltaY k z * DeltaY k z

theorem eventually_diff_DeltaX_sq (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun y : Fin 7 → ℝ => DeltaX k y * DeltaX k y) z :=
  (eventually_diff_DeltaX k h0 h1 hW6).mono fun _ hz => hz.mul hz

theorem eventually_diff_DeltaY_sq (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun y : Fin 7 → ℝ => DeltaY k y * DeltaY k y) z :=
  (eventually_diff_DeltaY k h0 h1 hW6 hWp).mono fun _ hz => hz.mul hz

theorem eventually_diff_SRad (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (SRad k) z := by
  filter_upwards [eventually_diff_DeltaX k h0 h1 hW6,
    eventually_diff_DeltaY k h0 h1 hW6 hWp] with z hzx hzy
  exact (hzx.mul hzx).add (hzy.mul hzy)

theorem hasFDerivAt_SRad (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    HasFDerivAt (SRad k) (fderiv ℝ (SRad k) u0) u0 :=
  ((eventually_diff_SRad k h0 h1 hW6 hWp).self_of_nhds).hasFDerivAt

/-- `S_k` 的**二阶 CLM**（两块平方的 T3 输出之和；逐字对齐 T3 的结合形）。 -/
def L2SRad (k : Fin 5) : (Fin 7 → ℝ) →L[ℝ] (Fin 7 → ℝ) →L[ℝ] ℝ :=
  ((DeltaX k u0) • L2DeltaX k + (fderiv ℝ (DeltaX k) u0).smulRight (fderiv ℝ (DeltaX k) u0)
      + ((DeltaX k u0) • L2DeltaX k
        + (fderiv ℝ (DeltaX k) u0).smulRight (fderiv ℝ (DeltaX k) u0)))
    + ((DeltaY k u0) • L2DeltaY k + (fderiv ℝ (DeltaY k) u0).smulRight (fderiv ℝ (DeltaY k) u0)
      + ((DeltaY k u0) • L2DeltaY k
        + (fderiv ℝ (DeltaY k) u0).smulRight (fderiv ℝ (DeltaY k) u0)))

theorem hasFDerivAt_fderiv_SRad (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (SRad k) z) (L2SRad k) u0 := by
  rw [L2SRad]
  have hx := hasFDerivAt_fderiv_mul_scalar (φ := DeltaX k) (ψ := DeltaX k)
    (hasFDerivAt_DeltaX k h0 h1 hW6) (hasFDerivAt_fderiv_DeltaX k h0 h1 hW6)
    (hasFDerivAt_DeltaX k h0 h1 hW6) (hasFDerivAt_fderiv_DeltaX k h0 h1 hW6)
    (eventually_diff_DeltaX k h0 h1 hW6) (eventually_diff_DeltaX k h0 h1 hW6)
  have hy := hasFDerivAt_fderiv_mul_scalar (φ := DeltaY k) (ψ := DeltaY k)
    (hasFDerivAt_DeltaY k h0 h1 hW6 hWp) (hasFDerivAt_fderiv_DeltaY k h0 h1 hW6 hWp)
    (hasFDerivAt_DeltaY k h0 h1 hW6 hWp) (hasFDerivAt_fderiv_DeltaY k h0 h1 hW6 hWp)
    (eventually_diff_DeltaY k h0 h1 hW6 hWp) (eventually_diff_DeltaY k h0 h1 hW6 hWp)
  exact hasFDerivAt_fderiv_add hx hy (eventually_diff_DeltaX_sq k h0 h1 hW6)
    (eventually_diff_DeltaY_sq k h0 h1 hW6 hWp)

/-- **`S` 的一阶取值**（`√S` 商法则里 `g1` 的取值；T3/T1 的 CLM 逐项求值）。 -/
theorem dSRad_single (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) (i : Fin 7) :
    (fderiv ℝ (SRad k) u0) (Pi.single i 1)
      = 2 * (DeltaX k u0) * ((fderiv ℝ (DeltaX k) u0) (Pi.single i 1))
        + 2 * (DeltaY k u0) * ((fderiv ℝ (DeltaY k) u0) (Pi.single i 1)) := by
  have hsum := ((hasFDerivAt_DeltaX k h0 h1 hW6).mul (hasFDerivAt_DeltaX k h0 h1 hW6)).add
    ((hasFDerivAt_DeltaY k h0 h1 hW6 hWp).mul (hasFDerivAt_DeltaY k h0 h1 hW6 hWp))
  have hval : (fderiv ℝ (DeltaX k * DeltaX k + DeltaY k * DeltaY k) u0) (Pi.single i 1)
      = 2 * (DeltaX k u0) * ((fderiv ℝ (DeltaX k) u0) (Pi.single i 1))
        + 2 * (DeltaY k u0) * ((fderiv ℝ (DeltaY k) u0) (Pi.single i 1)) := by
    rw [hsum.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  exact hval

/-- **`S` 的二阶取值**（`√S` 商法则里 `g2` 的取值）。 -/
theorem SRad2_single (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) (i j : Fin 7) :
    secondPartial (SRad k) u0 i j
      = 2 * ((DeltaX k u0) * secondPartial (DeltaX k) u0 i j
            + ((fderiv ℝ (DeltaX k) u0) (Pi.single i 1))
              * ((fderiv ℝ (DeltaX k) u0) (Pi.single j 1)))
        + 2 * ((DeltaY k u0) * secondPartial (DeltaY k) u0 i j
            + ((fderiv ℝ (DeltaY k) u0) (Pi.single i 1))
              * ((fderiv ℝ (DeltaY k) u0) (Pi.single j 1))) := by
  have hx := hasFDerivAt_fderiv_mul_scalar (φ := DeltaX k) (ψ := DeltaX k)
    (hasFDerivAt_DeltaX k h0 h1 hW6) (hasFDerivAt_fderiv_DeltaX k h0 h1 hW6)
    (hasFDerivAt_DeltaX k h0 h1 hW6) (hasFDerivAt_fderiv_DeltaX k h0 h1 hW6)
    (eventually_diff_DeltaX k h0 h1 hW6) (eventually_diff_DeltaX k h0 h1 hW6)
  have hy := hasFDerivAt_fderiv_mul_scalar (φ := DeltaY k) (ψ := DeltaY k)
    (hasFDerivAt_DeltaY k h0 h1 hW6 hWp) (hasFDerivAt_fderiv_DeltaY k h0 h1 hW6 hWp)
    (hasFDerivAt_DeltaY k h0 h1 hW6 hWp) (hasFDerivAt_fderiv_DeltaY k h0 h1 hW6 hWp)
    (eventually_diff_DeltaY k h0 h1 hW6 hWp) (eventually_diff_DeltaY k h0 h1 hW6 hWp)
  have hsum := hasFDerivAt_fderiv_add hx hy (eventually_diff_DeltaX_sq k h0 h1 hW6)
    (eventually_diff_DeltaY_sq k h0 h1 hW6 hWp)
  have hval : secondPartial (fun z : Fin 7 → ℝ =>
        DeltaX k z * DeltaX k z + DeltaY k z * DeltaY k z) u0 i j
      = 2 * ((DeltaX k u0) * secondPartial (DeltaX k) u0 i j
            + ((fderiv ℝ (DeltaX k) u0) (Pi.single i 1))
              * ((fderiv ℝ (DeltaX k) u0) (Pi.single j 1)))
        + 2 * ((DeltaY k u0) * secondPartial (DeltaY k) u0 i j
            + ((fderiv ℝ (DeltaY k) u0) (Pi.single i 1))
              * ((fderiv ℝ (DeltaY k) u0) (Pi.single j 1))) := by
    rw [secondPartial_eq_of_hasFDerivAt hsum i j]
    simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
      secondPartial]
    rw [← (hasFDerivAt_fderiv_DeltaX k h0 h1 hW6).fderiv,
      ← (hasFDerivAt_fderiv_DeltaY k h0 h1 hW6 hWp).fderiv]
    ring
  exact hval

/-! ## 4. `√S` 的**二阶商法则**（T2 = `hasFDerivAt_fderiv_comp_scalar`，`u = √`）

模板 = `D2Leaves.L2SqrtW` / `hasFDerivAt_fderiv_sqrtW` / `sqrtW2_single`（**逐字同型** ✓）。 -/

/-- `L2SRad` 的取值 = `secondPartial (SRad k)`（`L2SRad` 是 T3/T1 的显式 CLM，不是 `fderiv (fderiv ·)`，
故这条桥**必需**）。 -/
theorem L2SRad_apply (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) (i j : Fin 7) :
    (L2SRad k (Pi.single j 1)) (Pi.single i 1) = secondPartial (SRad k) u0 i j := by
  rw [← (hasFDerivAt_fderiv_SRad k h0 h1 hW6 hWp).fderiv, secondPartial]

/-- `√(S_k)` 的二阶 CLM（T2 的输出形态；`u = √`、`g = SRad k`）。 -/
def L2SqrtSRad (k : Fin 5) : (Fin 7 → ℝ) →L[ℝ] (Fin 7 → ℝ) →L[ℝ] ℝ :=
  (deriv Real.sqrt (SRad k u0)) • L2SRad k
    + (((fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (SRad k u0)).comp (fderiv ℝ (SRad k) u0)).smulRight
        (fderiv ℝ (SRad k) u0))

theorem hasFDerivAt_fderiv_sqrtSRad (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) (hpos : 0 < SRad k u0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => Real.sqrt (SRad k z)) z)
      (L2SqrtSRad k) u0 := by
  rw [L2SqrtSRad]
  refine hasFDerivAt_fderiv_comp_scalar (g := SRad k) (u := Real.sqrt)
    (hasFDerivAt_SRad k h0 h1 hW6 hWp) (hasFDerivAt_fderiv_SRad k h0 h1 hW6 hWp) ?_ ?_ ?_
  · have hu := (hasDerivAt_deriv_sqrt hpos).hasFDerivAt
    have hu' : HasFDerivAt (fun t : ℝ => deriv Real.sqrt t)
        (fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (SRad k u0)) (SRad k u0) := by
      rw [hu.fderiv]
      exact hu
    exact hu'
  · exact eventually_diff_SRad k h0 h1 hW6 hWp
  · have hcont : ContinuousAt (SRad k) u0 := (hasFDerivAt_SRad k h0 h1 hW6 hWp).continuousAt
    filter_upwards [hcont.eventually (IsOpen.mem_nhds isOpen_ne (ne_of_gt hpos))] with z hz
    exact (Real.hasDerivAt_sqrt hz).differentiableAt

/-- **`∂²(√S_k)` 的取值形态**（`deriv`/`fderiv` 全部显式化；= `hL7` 第 ②-步的标量结论）。
模板 = `D2Leaves.sqrtW2_single` ✓。 -/
theorem sqrtSRad2_single (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) (hpos : 0 < SRad k u0) (i j : Fin 7) :
    (L2SqrtSRad k (Pi.single j 1)) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (SRad k u0))) * (secondPartial (SRad k) u0 i j)
        + ((-2) * (1 / (2 * Real.sqrt (SRad k u0))))
            * ((2 * Real.sqrt (SRad k u0)) * (2 * Real.sqrt (SRad k u0)))⁻¹
            * ((fderiv ℝ (SRad k) u0) (Pi.single j 1))
            * ((fderiv ℝ (SRad k) u0) (Pi.single i 1)) := by
  rw [L2SqrtSRad]
  simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [d2_fderivReal_apply_eq_mul_one, fderiv_apply_one_eq_deriv]
  rw [HasDerivAt.deriv (Real.hasDerivAt_sqrt (ne_of_gt hpos))]
  rw [HasDerivAt.deriv (hasDerivAt_deriv_sqrt hpos)]
  rw [L2SRad_apply k h0 h1 hW6 hWp i j]
  ring

/-! ## 5. (v) 代数归一：`secondPartial (√∘SRad) = distHessReal`

先做三个**原子对齐**引理（把 z 空间量 `SRad k u0`/`DeltaX k u0` 换成 `HessSeamMain` 的具名靶
`radR k`/`DxR k`/`DyR k` —— **只换原子、不展开几何**，避免把 `secondPartial (DeltaX k)` 也摊开 ✗）。 -/

theorem DeltaX_u0_eq_DxR (k : Fin 5) : DeltaX k u0 = DxR k := rfl

theorem DeltaY_u0_eq_DyR (k : Fin 5) : DeltaY k u0 = DyR k := rfl

theorem SRad_u0_eq_radR (k : Fin 5) : SRad k u0 = radR k := by
  rw [SRad, DeltaX_u0_eq_DxR, DeltaY_u0_eq_DyR, radR, pow_two, pow_two]

theorem secondPartial_sqrtSRad (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) (hpos : 0 < SRad k u0) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => Real.sqrt (SRad k z)) u0 i j = distHessReal k i j := by
  have hA : secondPartial (fun z : Fin 7 → ℝ => Real.sqrt (SRad k z)) u0 i j
      = (L2SqrtSRad k (Pi.single j 1)) (Pi.single i 1) :=
    secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_sqrtSRad k h0 h1 hW6 hWp hpos) i j
  rw [hA, sqrtSRad2_single k h0 h1 hW6 hWp hpos i j,
    SRad2_single k h0 h1 hW6 hWp i j,
    dSRad_single k h0 h1 hW6 hWp i, dSRad_single k h0 h1 hW6 hWp j,
    fderiv_DeltaX k i (Wk_ne_zero (resSlot k) h0) (Wk_ne_zero ((resSlot k) + 1) h1)
      (Wk_ne_zero 6 hW6),
    fderiv_DeltaX k j (Wk_ne_zero (resSlot k) h0) (Wk_ne_zero ((resSlot k) + 1) h1)
      (Wk_ne_zero 6 hW6),
    fderiv_DeltaY k i (Wk_ne_zero (resSlot k) h0) (Wk_ne_zero ((resSlot k) + 1) h1)
      (Wk_ne_zero 6 hW6) (Wp_ne_zero hWp),
    fderiv_DeltaY k j (Wk_ne_zero (resSlot k) h0) (Wk_ne_zero ((resSlot k) + 1) h1)
      (Wk_ne_zero 6 hW6) (Wp_ne_zero hWp),
    SRad_u0_eq_radR k, DeltaX_u0_eq_DxR k, DeltaY_u0_eq_DyR k]
  rw [distHessReal, twoRadSqrtR, d2xR, d2yR]
  have hposRad : 0 < radR k := by rwa [← SRad_u0_eq_radR]
  have hsq : Real.sqrt (radR k) ^ 2 = radR k := Real.sq_sqrt (le_of_lt hposRad)
  have hne : Real.sqrt (radR k) ≠ 0 :=
    ne_of_gt (show (0 : ℝ) < Real.sqrt (radR k) by positivity)
  have hSne : radR k ≠ 0 := ne_of_gt hposRad
  field_simp
  ring_nf
  rw [hsq]
  ring

/-! ## 6. (vi) 终装：**`hL7_proved`**

`residualFun · mm = dist(Apt mm, Bpt mm) − z₆`（逐支 `rfl` ✓）→ `dist = √S`（`dist_point_eq_sqrt` ✓）
→ `secondPartial_sub` ＋ `√S` 商法则（(v) ✓）＋ `−z₆` 的二阶 = 0（`secondPartial_clm` ✓）⇒ `hL7` ✓。
**注意**：`−z₆` 支写成 `coord 6 z`（而非 `z 6`），以免 `rw` 在 `coord_apply` 上做非 `rfl` 的匹配 ✗。 -/

theorem residualFun_eq_dist_sub (mm : Fin 5) :
    (fun z : Fin 7 → ℝ => residualFun z mm)
      = fun z : Fin 7 → ℝ => dist ((Apt mm) (pad12 z)) ((Bpt mm) (pad12 z)) - z 6 := by
  funext z
  fin_cases mm <;> rfl

theorem dist_Apt_Bpt_eq_sqrt_SRad (mm : Fin 5) :
    (fun z : Fin 7 → ℝ => dist ((Apt mm) (pad12 z)) ((Bpt mm) (pad12 z)))
      = fun z : Fin 7 → ℝ => Real.sqrt (SRad mm z) := by
  funext z
  rw [dist_point_eq_sqrt]
  congr 1
  rw [SRad, DeltaX, DeltaY]
  ring

theorem eventually_diff_sqrtSRad (k : Fin 5)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) (hpos : 0 < SRad k u0) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z : Fin 7 → ℝ => Real.sqrt (SRad k z)) z := by
  have hcont : ContinuousAt (SRad k) u0 := (hasFDerivAt_SRad k h0 h1 hW6 hWp).continuousAt
  filter_upwards [eventually_diff_SRad k h0 h1 hW6 hWp,
    hcont.eventually (IsOpen.mem_nhds isOpen_ne (ne_of_gt hpos))] with z hzS hz
  exact ((Real.hasDerivAt_sqrt hz).differentiableAt).comp z hzS

/-- **`hL7`（具名 gap C1296）的内核证明**：`hessEntry i j mm = distHessReal mm i j`（∀ i j mm）。
前提 = ①的 `hadj` ＋ `hd`（`∀ᶠ` 可微性，见 `hessEntry_eq_secondPartial_residualFun`）＋
`hWk`/`hWp`（`Δ` 节点用）＋ `hrad`（⇒ `SRad mm u0 > 0`，供 `√` 链 ✓）。 -/
theorem hL7_proved
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (hd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ residualFun z)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hWp : 0 < WpIv.lo)
    (hrad : ∀ k : Fin 5, 0 < (radIv k).lo) (i j : Fin 7) (mm : Fin 5) :
    hessEntry i j mm = distHessReal mm i j := by
  have hpos : 0 < SRad mm u0 := by
    rw [SRad_u0_eq_radR]
    exact lt_of_lt_of_le (by exact_mod_cast hrad mm) (mem_lo_le (radIv_mem mm))
  have h0 : 0 < (WkIv (resSlot mm)).lo := hWk (resSlot mm)
  have h1 : 0 < (WkIv ((resSlot mm) + 1)).lo := hWk ((resSlot mm) + 1)
  have h6 : 0 < (WkIv 6).lo := hWk 6
  have hfun : (fun z : Fin 7 → ℝ => residualFun z mm)
      = fun z : Fin 7 → ℝ => Real.sqrt (SRad mm z) - coord 6 z := by
    funext z
    have hd1 : residualFun z mm
        = dist ((Apt mm) (pad12 z)) ((Bpt mm) (pad12 z)) - z 6 := by
      have h := congrFun (residualFun_eq_dist_sub mm) z
      exact h
    have hd2 : dist ((Apt mm) (pad12 z)) ((Bpt mm) (pad12 z)) = Real.sqrt (SRad mm z) :=
      congrFun (dist_Apt_Bpt_eq_sqrt_SRad mm) z
    rw [hd1, hd2, show coord 6 z = z 6 from rfl]
  rw [hessEntry_eq_secondPartial_residualFun hadj hd i j mm, hfun]
  rw [secondPartial_sub (hasFDerivAt_fderiv_sqrtSRad mm h0 h1 h6 hWp hpos)
    (hasFDerivAt_fderiv_clm (coord 6))
    (eventually_diff_sqrtSRad mm h0 h1 h6 hWp hpos)
    (Filter.Eventually.of_forall fun z =>
      (ContinuousLinearMap.hasFDerivAt (coord 6) (x := z)).differentiableAt),
    secondPartial_sqrtSRad mm h0 h1 h6 hWp hpos i j, secondPartial_clm (coord 6) u0 i j]
  ring

/-! ## 7. 收口：`hH` 与 `Jt` 的**无条件化**（mod 显式前提批）

`hL7` 已证 ⇒ `HessSeamMain.mem_hessEntry_of_leaves` 的**唯一二阶前提被付清** ⇒ `hH` 与盒心 `Jt`
只剩**有限有理不等式批 ＋ 3 条可微性/邻域可微性**（全为显式参数，根内均有供给 ✓）。 -/

/-- **`hH`（盒心）无条件化**：`Hess := HessOf d2xIv d2yIv` 包络 `hessEntry`。 -/
theorem mem_hessEntry_uncond
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (hd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ residualFun z)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hWp : 0 < WpIv.lo)
    (hrad : ∀ k : Fin 5, 0 < (radIv k).lo) (i j : Fin 7) (mm : Fin 5) :
    (HessOf d2xIv d2yIv i j mm).Mem (hessEntry i j mm) :=
  mem_hessEntry_of_leaves (fun i j mm => hL7_proved hadj hd hWk hWp hrad i j mm) hWk hrad hWp i j mm

/-- **盒心 `Jt`（12×12）无条件化**。 -/
theorem mem_Jt_at_center_uncond
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (hd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ residualFun z)
    (hdT : DifferentiableAt ℝ TCSystem cCertR)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hWp : 0 < WpIv.lo)
    (hrad : ∀ k : Fin 5, 0 < (radIv k).lo) (r c : Fin 12) :
    (Jt (HessOf d2xIv d2yIv) r c).Mem ((fderiv ℝ TCSystem cCertR (Pi.single c 1)) r) :=
  mem_Jt_at_center_of_leaves (fun i j mm => hL7_proved hadj hd hWk hWp hrad i j mm)
    hdT hd.self_of_nhds hadj hWk hrad hWp r c

end HessSeam

end N11Formalization
