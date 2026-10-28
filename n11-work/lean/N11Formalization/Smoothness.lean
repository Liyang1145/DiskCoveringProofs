import N11Formalization.TCSystem
import N11Formalization.SourceIdentity

/-!
# 源系统各构件的**平滑性**（G1 义务 (2) 的一阶半）

G1 的剩余义务 (2) 是「`TCSystem` 在盒上可微」。由于乘子块 `adjointBlock` 用 `fderiv ℝ residualFun`，
这内在地要求 `residualFun` 的 **C²** 性；而 C² 的第一步是**一阶可微**。本文件把一阶那一半
拆成**逐构件、具名、kernel 检查**的引理，并把每个构件的**非退化条件**列成显式假设：

| 构件 | 非退化条件 |
|---|---|
| `rhoK u k = cos a_k − √(R² − sin²a_k)` | `R² − sin²a_k ≠ 0`（根号内量） |
| `dist (Uvec u k) (hub_l u)` | `Uvec u k ≠ hub_l u`（源文 Python 写 `Q(dx·dx+dy·dy)`，零点不可微） |

这些条件的**箱内正下界由区间侧给出**（`Interval/*` 的有理界）；本文件只负责「条件 ⇒ 平滑」。
`Point` 上的距离用 `dist_point_eq_sqrt` 化成标量，从而**避开**对 `Point` 值函数直接做 `ContDiffAt`。

**真实等级**：kernel-proved，无条件（除显式非退化假设），零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

/-- 一般 hub：`!₂[u a, 0]`（`a = 4` 给 `hub0`，`a = 5` 给 `hub1`）。 -/
def hubOf (a : Fin 12) (u : Fin 12 → ℝ) : Point := !₂[u a, 0]

theorem hubOf_coord0 (a : Fin 12) (u : Fin 12 → ℝ) : (hubOf a u).ofLp 0 = u a := rfl
theorem hubOf_coord1 (a : Fin 12) (u : Fin 12 → ℝ) : (hubOf a u).ofLp 1 = 0 := rfl
theorem hub0_eq_hubOf (u : Fin 12 → ℝ) : hub0 u = hubOf 4 u := rfl
theorem hub1_eq_hubOf (u : Fin 12 → ℝ) : hub1 u = hubOf 5 u := rfl

/-- `ofLp` 相等 ⇒ `Point` 相等。 -/
theorem ofLp_eq_ofLp_iff {p q : Point} (h : p.ofLp = q.ofLp) : p = q :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).injective h

/-- `Uvec` 的两个坐标函数。 -/
noncomputable def UvecX (u : Fin 12 → ℝ) (k : Fin 9) : ℝ := (Uvec u k).ofLp 0
noncomputable def UvecY (u : Fin 12 → ℝ) (k : Fin 9) : ℝ := (Uvec u k).ofLp 1

theorem UvecX_eq (u : Fin 12 → ℝ) (k : Fin 9) :
    UvecX u k = rhoK u k * Real.cos (thetaOf (angleVec u) k)
      + rhoK u (k + 1) * Real.cos (thetaOf (angleVec u) (k + 1))
      - Real.cos (thetaOf (angleVec u) k + angleVec u k) := by
  rw [UvecX, Uvec_coord0, ringCenter_coord0, ringCenter_coord0, arcEnd_coord0]

theorem UvecY_eq (u : Fin 12 → ℝ) (k : Fin 9) :
    UvecY u k = rhoK u k * Real.sin (thetaOf (angleVec u) k)
      + rhoK u (k + 1) * Real.sin (thetaOf (angleVec u) (k + 1))
      - Real.sin (thetaOf (angleVec u) k + angleVec u k) := by
  rw [UvecY, Uvec_coord1, ringCenter_coord1, ringCenter_coord1, arcEnd_coord1]

/-- 坐标投影平滑。 -/
theorem contDiffAt_coord {n : WithTop ℕ∞} (i : Fin 12) (x : Fin 12 → ℝ) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => u i) x :=
  (ContinuousLinearMap.proj i : (Fin 12 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt

/-- `Real.cos ∘ f` 平滑（显式 `g := Real.cos`，避免被展开成 `Complex.re ∘ Complex.cos`）。 -/
theorem contDiffAt_cos_comp {n : WithTop ℕ∞} {f : (Fin 12 → ℝ) → ℝ} {x : Fin 12 → ℝ}
    (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun u => Real.cos (f u)) x :=
  ContDiffAt.comp (g := Real.cos) x (Real.contDiff_cos.contDiffAt (x := f x)) hf

/-- `Real.sin ∘ f` 平滑。 -/
theorem contDiffAt_sin_comp {n : WithTop ℕ∞} {f : (Fin 12 → ℝ) → ℝ} {x : Fin 12 → ℝ}
    (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun u => Real.sin (f u)) x :=
  ContDiffAt.comp (g := Real.sin) x (Real.contDiff_sin.contDiffAt (x := f x)) hf

/-- `angleVec` 每个坐标平滑。 -/
theorem contDiffAt_angleVec {n : WithTop ℕ∞} (k : Fin 9) (x : Fin 12 → ℝ) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => angleVec u k) x := by
  fin_cases k <;> simp [angleVec] <;> fun_prop

/-- `thetaOf (angleVec ·)` 每个坐标平滑（`thetaOf` 是显式有限和）。 -/
theorem contDiffAt_thetaOf_angleVec {n : WithTop ℕ∞} (k : Fin 9) (x : Fin 12 → ℝ) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => thetaOf (angleVec u) k) x := by
  fin_cases k <;> simp [thetaOf, angleVec] <;> fun_prop

/-- **`rhoK` 平滑**（非退化条件：根号内量 `R² − sin²a_k ≠ 0`）。 -/
theorem contDiffAt_rhoK {n : WithTop ℕ∞} (k : Fin 9) (x : Fin 12 → ℝ)
    (h : (x 6) ^ 2 - (Real.sin (angleVec x k)) ^ 2 ≠ 0) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => rhoK u k) x := by
  have hrew : (fun u : Fin 12 → ℝ => rhoK u k)
      = fun u => Real.cos (angleVec u k) - Real.sqrt ((u 6) ^ 2 - (Real.sin (angleVec u k)) ^ 2) :=
    funext fun u => rfl
  rw [hrew]
  have hcos : ContDiffAt ℝ n (fun u : Fin 12 → ℝ => Real.cos (angleVec u k)) x :=
    contDiffAt_cos_comp (n := n) (contDiffAt_angleVec (n := n) k x)
  have hsin : ContDiffAt ℝ n (fun u : Fin 12 → ℝ => Real.sin (angleVec u k)) x :=
    contDiffAt_sin_comp (n := n) (contDiffAt_angleVec (n := n) k x)
  have hrad : ContDiffAt ℝ n
      (fun u : Fin 12 → ℝ => (u 6) ^ 2 - (Real.sin (angleVec u k)) ^ 2) x :=
    ((contDiffAt_coord (n := n) 6 x).pow 2).sub (hsin.pow 2)
  exact hcos.sub (hrad.sqrt h)

/-- `Uvec` 的 x 坐标平滑。 -/
theorem contDiffAt_UvecX {n : WithTop ℕ∞} (k : Fin 9) (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => UvecX u k) x := by
  rw [show (fun u : Fin 12 → ℝ => UvecX u k)
      = fun u => rhoK u k * Real.cos (thetaOf (angleVec u) k)
          + rhoK u (k + 1) * Real.cos (thetaOf (angleVec u) (k + 1))
          - Real.cos (thetaOf (angleVec u) k + angleVec u k) from funext fun u => UvecX_eq u k]
  have h1 : ContDiffAt ℝ n (fun u : Fin 12 → ℝ =>
      rhoK u k * Real.cos (thetaOf (angleVec u) k)) x :=
    (contDiffAt_rhoK (n := n) k x (hrho k)).mul
      (contDiffAt_cos_comp (n := n) (contDiffAt_thetaOf_angleVec (n := n) k x))
  have h2 : ContDiffAt ℝ n (fun u : Fin 12 → ℝ =>
      rhoK u (k + 1) * Real.cos (thetaOf (angleVec u) (k + 1))) x :=
    (contDiffAt_rhoK (n := n) (k + 1) x (hrho (k + 1))).mul
      (contDiffAt_cos_comp (n := n) (contDiffAt_thetaOf_angleVec (n := n) (k + 1) x))
  have h3 : ContDiffAt ℝ n (fun u : Fin 12 → ℝ =>
      Real.cos (thetaOf (angleVec u) k + angleVec u k)) x :=
    contDiffAt_cos_comp (n := n)
      ((contDiffAt_thetaOf_angleVec (n := n) k x).add (contDiffAt_angleVec (n := n) k x))
  exact (h1.add h2).sub h3

/-- `Uvec` 的 y 坐标平滑。 -/
theorem contDiffAt_UvecY {n : WithTop ℕ∞} (k : Fin 9) (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => UvecY u k) x := by
  rw [show (fun u : Fin 12 → ℝ => UvecY u k)
      = fun u => rhoK u k * Real.sin (thetaOf (angleVec u) k)
          + rhoK u (k + 1) * Real.sin (thetaOf (angleVec u) (k + 1))
          - Real.sin (thetaOf (angleVec u) k + angleVec u k) from funext fun u => UvecY_eq u k]
  have h1 : ContDiffAt ℝ n (fun u : Fin 12 → ℝ =>
      rhoK u k * Real.sin (thetaOf (angleVec u) k)) x :=
    (contDiffAt_rhoK (n := n) k x (hrho k)).mul
      (contDiffAt_sin_comp (n := n) (contDiffAt_thetaOf_angleVec (n := n) k x))
  have h2 : ContDiffAt ℝ n (fun u : Fin 12 → ℝ =>
      rhoK u (k + 1) * Real.sin (thetaOf (angleVec u) (k + 1))) x :=
    (contDiffAt_rhoK (n := n) (k + 1) x (hrho (k + 1))).mul
      (contDiffAt_sin_comp (n := n) (contDiffAt_thetaOf_angleVec (n := n) (k + 1) x))
  have h3 : ContDiffAt ℝ n (fun u : Fin 12 → ℝ =>
      Real.sin (thetaOf (angleVec u) k + angleVec u k)) x :=
    contDiffAt_sin_comp (n := n)
      ((contDiffAt_thetaOf_angleVec (n := n) k x).add (contDiffAt_angleVec (n := n) k x))
  exact (h1.add h2).sub h3

/-- **`dist (Uvec · k) (hubOf a ·)` 平滑**（非退化条件：两点不重合）。 -/
theorem contDiffAt_dist_Uvec_hubOf {n : WithTop ℕ∞} (k : Fin 9) (a : Fin 12)
    (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (h : Uvec x k ≠ hubOf a x) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => dist (Uvec u k) (hubOf a u)) x := by
  have hrew : (fun u : Fin 12 → ℝ => dist (Uvec u k) (hubOf a u))
      = fun u => Real.sqrt ((UvecX u k - u a) ^ 2 + (UvecY u k) ^ 2) := by
    funext u
    rw [dist_point_eq_sqrt, UvecX, UvecY, hubOf_coord0, hubOf_coord1, sub_zero]
  rw [hrew]
  refine ContDiffAt.sqrt ?_ ?_
  · have hX : ContDiffAt ℝ n (fun u : Fin 12 → ℝ => UvecX u k) x := contDiffAt_UvecX (n := n) k x hrho
    have hY : ContDiffAt ℝ n (fun u : Fin 12 → ℝ => UvecY u k) x := contDiffAt_UvecY (n := n) k x hrho
    exact (((hX.sub (contDiffAt_coord (n := n) a x)).pow 2).add (hY.pow 2))
  · intro hzero
    apply h
    have h2 : (UvecX x k - x a) ^ 2 = 0 ∧ (UvecY x k) ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hzero
    have hx0 : UvecX x k = x a := sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2.1)
    have hy0 : UvecY x k = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2.2
    refine ofLp_eq_ofLp_iff ?_
    funext i
    fin_cases i
    · simpa [UvecX, hubOf_coord0] using hx0
    · simpa [UvecY, hubOf_coord1] using hy0

/-! ## 第五条残差：`wPoint` 与 `ringCenter` -/

/-- `wPoint` 的两个坐标函数。 -/
noncomputable def WX (u : Fin 12 → ℝ) : ℝ := (wPoint u).ofLp 0
noncomputable def WY (u : Fin 12 → ℝ) : ℝ := (wPoint u).ofLp 1

theorem WX_eq (u : Fin 12 → ℝ) : WX u = (u 4 + u 5) / 2 := rfl
theorem WY_eq (u : Fin 12 → ℝ) :
    WY u = Real.sqrt ((u 6) ^ 2 - ((u 5 - u 4) / 2) ^ 2) := rfl

theorem contDiffAt_zero {n : WithTop ℕ∞} (x : Fin 12 → ℝ) :
    ContDiffAt ℝ n (fun _ : Fin 12 → ℝ => (0 : ℝ)) x := contDiffAt_const

theorem contDiffAt_div_const {n : WithTop ℕ∞} {f : (Fin 12 → ℝ) → ℝ} {x : Fin 12 → ℝ}
    (hf : ContDiffAt ℝ n f x) (c : ℝ) : ContDiffAt ℝ n (fun u => f u / c) x := by
  simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using hf.const_smul c⁻¹

/-- `wPoint` 的 x 坐标平滑（线性）。 -/
theorem contDiffAt_WX {n : WithTop ℕ∞} (x : Fin 12 → ℝ) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => WX u) x := by
  rw [show (fun u : Fin 12 → ℝ => WX u) = fun u => (u 4 + u 5) / 2 from funext fun u => WX_eq u]
  exact ((contDiffAt_coord (n := n) 4 x).add (contDiffAt_coord (n := n) 5 x)).div_const 2

/-- `wPoint` 的 y 坐标平滑（非退化条件：`R² − d² ≠ 0`，`d = (y1−y0)/2`）。 -/
theorem contDiffAt_WY {n : WithTop ℕ∞} (x : Fin 12 → ℝ)
    (h : (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => WY u) x := by
  rw [show (fun u : Fin 12 → ℝ => WY u)
      = fun u => Real.sqrt ((u 6) ^ 2 - ((u 5 - u 4) / 2) ^ 2) from funext fun u => WY_eq u]
  refine ContDiffAt.sqrt ?_ h
  exact ((contDiffAt_coord (n := n) 6 x).pow 2).sub
    ((((contDiffAt_coord (n := n) 5 x).sub (contDiffAt_coord (n := n) 4 x)).div_const 2).pow 2)

/-- `ringCenter` 的 x 坐标平滑。 -/
theorem contDiffAt_ringCenterX {n : WithTop ℕ∞} (k : Fin 9) (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => (ringCenter u k).ofLp 0) x := by
  rw [show (fun u : Fin 12 → ℝ => (ringCenter u k).ofLp 0)
      = fun u => rhoK u k * Real.cos (thetaOf (angleVec u) k) from
        funext fun u => ringCenter_coord0 u k]
  exact (contDiffAt_rhoK (n := n) k x (hrho k)).mul
    (contDiffAt_cos_comp (n := n) (contDiffAt_thetaOf_angleVec (n := n) k x))

/-- `ringCenter` 的 y 坐标平滑。 -/
theorem contDiffAt_ringCenterY {n : WithTop ℕ∞} (k : Fin 9) (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => (ringCenter u k).ofLp 1) x := by
  rw [show (fun u : Fin 12 → ℝ => (ringCenter u k).ofLp 1)
      = fun u => rhoK u k * Real.sin (thetaOf (angleVec u) k) from
        funext fun u => ringCenter_coord1 u k]
  exact (contDiffAt_rhoK (n := n) k x (hrho k)).mul
    (contDiffAt_sin_comp (n := n) (contDiffAt_thetaOf_angleVec (n := n) k x))

/-- **`dist (wPoint ·) (ringCenter · 6)` 平滑**（非退化条件：两点不重合）。 -/
theorem contDiffAt_dist_wPoint_ringCenter {n : WithTop ℕ∞} (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hradW : (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (h : wPoint x ≠ ringCenter x 6) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => dist (wPoint u) (ringCenter u 6)) x := by
  have hrew : (fun u : Fin 12 → ℝ => dist (wPoint u) (ringCenter u 6))
      = fun u => Real.sqrt (((wPoint u).ofLp 0 - (ringCenter u 6).ofLp 0) ^ 2
          + ((wPoint u).ofLp 1 - (ringCenter u 6).ofLp 1) ^ 2) := by
    funext u
    rw [dist_point_eq_sqrt]
  rw [hrew]
  refine ContDiffAt.sqrt ?_ ?_
  · have hX := contDiffAt_WX (n := n) x
    have hY := contDiffAt_WY (n := n) x hradW
    have hRX := contDiffAt_ringCenterX (n := n) 6 x hrho
    have hRY := contDiffAt_ringCenterY (n := n) 6 x hrho
    exact (((hX.sub hRX).pow 2).add ((hY.sub hRY).pow 2))
  · intro hzero
    apply h
    have h2 : ((wPoint x).ofLp 0 - (ringCenter x 6).ofLp 0) ^ 2 = 0
        ∧ ((wPoint x).ofLp 1 - (ringCenter x 6).ofLp 1) ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hzero
    refine ofLp_eq_ofLp_iff ?_
    funext i
    fin_cases i
    · exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2.1)
    · exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2.2)

/-! ## 组装：`residual` 的五个分量（逐条具名，便于独立审计） -/

theorem contDiffAt_residual_0 {n : WithTop ℕ∞} (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hU1 : Uvec x 1 ≠ hub1 x) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => residual u 0) x := by
  have h1 : Uvec x 1 ≠ hubOf 5 x := by simpa [hub1_eq_hubOf] using hU1
  rw [show (fun u : Fin 12 → ℝ => residual u 0)
      = fun u => dist (Uvec u 1) (hubOf 5 u) - u 6 from
        funext fun u => by rw [residual_comp_0, hub1_eq_hubOf]]
  exact (contDiffAt_dist_Uvec_hubOf (n := n) 1 5 x hrho h1).sub (contDiffAt_coord (n := n) 6 x)

theorem contDiffAt_residual_1 {n : WithTop ℕ∞} (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hU2 : Uvec x 2 ≠ hub0 x) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => residual u 1) x := by
  have h2 : Uvec x 2 ≠ hubOf 4 x := by simpa [hub0_eq_hubOf] using hU2
  rw [show (fun u : Fin 12 → ℝ => residual u 1)
      = fun u => dist (Uvec u 2) (hubOf 4 u) - u 6 from
        funext fun u => by rw [residual_comp_1, hub0_eq_hubOf]]
  exact (contDiffAt_dist_Uvec_hubOf (n := n) 2 4 x hrho h2).sub (contDiffAt_coord (n := n) 6 x)

theorem contDiffAt_residual_2 {n : WithTop ℕ∞} (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hU3 : Uvec x 3 ≠ hub0 x) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => residual u 2) x := by
  have h3 : Uvec x 3 ≠ hubOf 4 x := by simpa [hub0_eq_hubOf] using hU3
  rw [show (fun u : Fin 12 → ℝ => residual u 2)
      = fun u => dist (Uvec u 3) (hubOf 4 u) - u 6 from
        funext fun u => by rw [residual_comp_2, hub0_eq_hubOf]]
  exact (contDiffAt_dist_Uvec_hubOf (n := n) 3 4 x hrho h3).sub (contDiffAt_coord (n := n) 6 x)

theorem contDiffAt_residual_3 {n : WithTop ℕ∞} (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hU8 : Uvec x 8 ≠ hub1 x) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => residual u 3) x := by
  have h8 : Uvec x 8 ≠ hubOf 5 x := by simpa [hub1_eq_hubOf] using hU8
  rw [show (fun u : Fin 12 → ℝ => residual u 3)
      = fun u => dist (Uvec u 8) (hubOf 5 u) - u 6 from
        funext fun u => by rw [residual_comp_3, hub1_eq_hubOf]]
  exact (contDiffAt_dist_Uvec_hubOf (n := n) 8 5 x hrho h8).sub (contDiffAt_coord (n := n) 6 x)

theorem contDiffAt_residual_4 {n : WithTop ℕ∞} (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hradW : (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hW : wPoint x ≠ ringCenter x 6) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => residual u 4) x := by
  rw [show (fun u : Fin 12 → ℝ => residual u 4)
      = fun u => dist (wPoint u) (ringCenter u 6) - u 6 from
        funext fun u => by rw [residual_comp_4]]
  exact (contDiffAt_dist_wPoint_ringCenter (n := n) x hrho hradW hW).sub
    (contDiffAt_coord (n := n) 6 x)

/-- **`residual` 的每个分量平滑**（G1 义务 (2) 一阶半的**完整**形式）。

非退化条件（箱内有理下界由区间侧给）：
* `hrho`：九个 `rhoK` 的根号内量非零；
* `hradW`：`R² − ((y1−y0)/2)² ≠ 0`；
* `hU1`,`hU2`,`hU3`,`hU8`：四条 `dist` 的两点不重合；
* `hW`：`wPoint ≠ ringCenter 6`。 -/
theorem contDiffAt_residual {n : WithTop ℕ∞} (i : Fin 5) (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hradW : (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hU1 : Uvec x 1 ≠ hub1 x) (hU2 : Uvec x 2 ≠ hub0 x)
    (hU3 : Uvec x 3 ≠ hub0 x) (hU8 : Uvec x 8 ≠ hub1 x)
    (hW : wPoint x ≠ ringCenter x 6) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => residual u i) x := by
  fin_cases i
  · exact contDiffAt_residual_0 (n := n) x hrho hU1
  · exact contDiffAt_residual_1 (n := n) x hrho hU2
  · exact contDiffAt_residual_2 (n := n) x hrho hU3
  · exact contDiffAt_residual_3 (n := n) x hrho hU8
  · exact contDiffAt_residual_4 (n := n) x hrho hradW hW

end N11Formalization
