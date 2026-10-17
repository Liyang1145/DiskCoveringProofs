import N11Formalization.FlashTenBoundary

/-!
# C450 的解析 consumer（第一层）：圆上非负密度的积分覆盖不等式

**命题**（generic，无语义漂移）：设 `γ : ℝ → Point` 连续（"测试圆"的参数化），
`W : ℝ → ℝ` 连续且处处非负。若有限个 disk `B(c i, r)`（`i : Fin n`）**覆盖该测试圆**
（`∀ θ, ∃ i, dist (γ θ) (c i) ≤ r`），则

`∫ θ in 0..2π, W θ  ≤  Σ_i ∫ θ in 0..2π, (if dist (γ θ) (c i) ≤ r then W θ else 0)`

即"**弧积分之和 ≥ 总质量**"：右端每一求和项就是第 `i` 个盘在该测试圆上截出的**弧积分**
（被积函数在弧外取 0）。允许
* **重叠**（不做互不相交假设：证明只用逐点重数 `Σ_i 1_{A_i} ≥ 1`）；
* **退化弧**（盘与圆内切：弧是单点 `{θ₀}` ⇒ 被积函数**不恒为 0**，仅在一点非零，
  但其**积分为 0** —— 下游 `t = 0` / `ℓ ≥ 2R` 两端点即此口径）；
* **空弧**（盘与该圆不相交：被积函数恒 0，积分 0）。

## 与源文的变量对应（`solo-20260922/M10-038-EXCLUSION.md` §2–§3）

| 源文 | 本文件 |
|---|---|
| 单位圆 `∂D`（圆心 0，半径 1） | `γ θ = angPt θ = !₂[cos θ, sin θ]`（`h = 0, q = 1`） |
| hub 中心圆 `S(h,q)`，`R < q < 1-e` | `γ θ = h + q • angPt θ`（`h = c hub`，取 `q ↓ R` 的极限） |
| 十个环盘 `B(c_i,R)` | `c : Fin n → Point`，`r := R = 19/50`（消费时 `n = 10`） |
| 密度 `Wj(θ) = a_j0 + Σ_{k≤3} a_jk cos(kθ)` | 本文件通用 `W`；三角情形见 `TrigDensity` |
| "弧积分除以 2" `a_0 t + Σ a_k sin(kt)cos(kφ)/k` | `(1/2) * ∫`（闭式属下一层 lemma，本文件不用） |
| 需求 `B = π(a_00+a_10)` | `(1/2)∫_0^{2π} W0 + (1/2)∫_0^{2π} W1`（`TrigDensity.integral_toFun`） |

**覆盖假设量化在全 `θ ∈ ℝ` 不是加强**：`angPt` 以 `2π` 为周期（`angPt_add_two_pi`），
故"整个圆被覆盖"给出所有 `θ ∈ ℝ`。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

open scoped Interval
open MeasureTheory
open Filter

section

/-- 单位圆的角参数化点 `(cos θ, sin θ) ∈ ℝ²`。 -/
noncomputable def angPt (θ : ℝ) : Point := !₂[Real.cos θ, Real.sin θ]

theorem continuous_angPt : Continuous angPt := by
  have h1 : Continuous fun θ : ℝ => ![Real.cos θ, Real.sin θ] := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> continuity
  have h2 : Continuous fun θ : ℝ => (EuclideanSpace.equiv (Fin 2) ℝ) (angPt θ) := by
    convert h1 using 1
    ext θ i; fin_cases i <;> simp [angPt]
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp h2

/-- `angPt` 以 `2π` 为周期（故"整圆"与全 `θ ∈ ℝ` 等价）。 -/
theorem angPt_add_two_pi (θ : ℝ) : angPt (θ + 2 * Real.pi) = angPt θ := by
  simp [angPt, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- **核心解析 consumer**：非负连续密度 + 有限 disk 覆盖测试圆 ⟹ 弧积分之和 ≥ 总质量。

证明只用：`Finset.single_le_sum`（重数 ≥ 1）→ `intervalIntegral.integral_mono`
→ `intervalIntegral.integral_finsetSum` + `IntervalIntegrable.sum`；
弧集可测性来自 `isClosed_le`。**不用** `S¹` 上的测度/Haar 积分。 -/
theorem circle_integral_le_sum_arc_integrals {γ : ℝ → Point} (hγ : Continuous γ)
    {W : ℝ → ℝ} (hWc : Continuous W) (hWn : ∀ θ, 0 ≤ W θ)
    {n : ℕ} {c : Fin n → Point} {r : ℝ}
    (hcov : ∀ θ : ℝ, ∃ i : Fin n, dist (γ θ) (c i) ≤ r) :
    ∫ θ in (0)..(2 * Real.pi), W θ ≤
      ∑ i : Fin n, ∫ θ in (0)..(2 * Real.pi),
        (if dist (γ θ) (c i) ≤ r then W θ else 0) := by
  classical
  -- (1) 逐点：覆盖 + W ≥ 0 ⟹ `W ≤ Σ_i 弧内密度`
  have hpt : ∀ θ : ℝ, W θ ≤
      ∑ i : Fin n, (if dist (γ θ) (c i) ≤ r then W θ else 0) := by
    intro θ
    obtain ⟨j, hj⟩ := hcov θ
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (0 : ℝ) ≤ (if dist (γ θ) (c i) ≤ r then W θ else 0) := by
      intro i _
      by_cases h : dist (γ θ) (c i) ≤ r
      · simp [h, hWn θ]
      · simp [h]
    have hle := Finset.single_le_sum hnn (Finset.mem_univ j)
    have hfin : (if dist (γ θ) (c j) ≤ r then W θ else 0) = W θ := by simp [hj]
    rwa [hfin] at hle
  -- (2) 每个弧内密度在区间上可积：以连续密度 W 作控制函数（`g = 1_{A_i} · W ≤ W`，因 W ≥ 0）
  have hint : ∀ i : Fin n,
      IntervalIntegrable (fun θ : ℝ => (if dist (γ θ) (c i) ≤ r then W θ else 0))
        volume 0 (2 * Real.pi) := by
    intro i
    have hWint : IntervalIntegrable W volume 0 (2 * Real.pi) :=
      hWc.intervalIntegrable (μ := volume) 0 (2 * Real.pi)
    have hmeas : MeasurableSet {θ : ℝ | dist (γ θ) (c i) ≤ r} :=
      IsClosed.measurableSet (isClosed_le (hγ.dist continuous_const) continuous_const)
    have hgm : AEStronglyMeasurable
        (fun θ : ℝ => (if dist (γ θ) (c i) ≤ r then W θ else 0))
        (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) :=
      (Measurable.ite hmeas hWc.measurable measurable_const).aestronglyMeasurable
    refine hWint.mono_fun hgm ?_
    filter_upwards with θ
    by_cases h : dist (γ θ) (c i) ≤ r
    · simp only [h, if_true, Real.norm_eq_abs, abs_of_nonneg (hWn θ)]
      exact le_rfl
    · simp only [h, if_false, norm_zero, Real.norm_eq_abs, abs_of_nonneg (hWn θ)]
      exact hWn θ
  -- (3) 和可积 + 积分单调 + 和/积分互换
  have hsum : IntervalIntegrable
      (fun θ : ℝ => ∑ i : Fin n, (if dist (γ θ) (c i) ≤ r then W θ else 0))
      volume 0 (2 * Real.pi) := by
    have heq : (∑ i : Fin n, (fun θ : ℝ =>
          (if dist (γ θ) (c i) ≤ r then W θ else 0)))
        = fun θ : ℝ => ∑ i : Fin n, (if dist (γ θ) (c i) ≤ r then W θ else 0) := by
      funext θ
      simp only [Finset.sum_apply]
    rw [← heq]
    exact IntervalIntegrable.sum (Finset.univ : Finset (Fin n)) (fun i _ => hint i)
  have hmain : ∫ θ in (0)..(2 * Real.pi), W θ ≤
      ∫ θ in (0)..(2 * Real.pi),
        ∑ i : Fin n, (if dist (γ θ) (c i) ≤ r then W θ else 0) :=
    intervalIntegral.integral_mono (f := W)
      (g := fun θ : ℝ => ∑ i : Fin n, (if dist (γ θ) (c i) ≤ r then W θ else 0))
      (by positivity)
      (hWc.intervalIntegrable (μ := volume) 0 (2 * Real.pi)) hsum hpt
  have hsplit : ∫ θ in (0)..(2 * Real.pi),
        ∑ i : Fin n, (if dist (γ θ) (c i) ≤ r then W θ else 0)
      = ∑ i : Fin n, ∫ θ in (0)..(2 * Real.pi),
        (if dist (γ θ) (c i) ≤ r then W θ else 0) := by
    simpa using intervalIntegral.integral_finsetSum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => hint i)
  rwa [hsplit] at hmain

/-- 测试圆 = 圆心 `h`、半径 `q` 的圆（`q = 0` 也成立：退化为一点，不等式仍真）。 -/
theorem circle_integral_le_sum_arc_integrals_circle {h : Point} {q : ℝ}
    {W : ℝ → ℝ} (hWc : Continuous W) (hWn : ∀ θ, 0 ≤ W θ)
    {n : ℕ} {c : Fin n → Point} {r : ℝ}
    (hcov : ∀ θ : ℝ, ∃ i : Fin n, dist (h + q • angPt θ) (c i) ≤ r) :
    ∫ θ in (0)..(2 * Real.pi), W θ ≤
      ∑ i : Fin n, ∫ θ in (0)..(2 * Real.pi),
        (if dist (h + q • angPt θ) (c i) ≤ r then W θ else 0) := by
  refine circle_integral_le_sum_arc_integrals (γ := fun θ : ℝ => h + q • angPt θ)
    (continuous_const.add (continuous_angPt.const_smul q)) hWc hWn ?_
  intro θ
  exact hcov θ

/-! ## 三角密度：非负性与总质量

源文权函数 `Wj(θ) = a_j0 + Σ_{k=1..3} a_jk cos(kθ)` 的非负性由精确有理比较
`a_j0 ≥ Σ|a_jk|` 保证（源 §4）；总质量 = `π a_j0`（即 `(1/2)∫_0^{2π} Wj = π a_j0`）。 -/

/-- 三阶余弦三角多项式（源文权函数的一般形状）+ 保证非负性的域条件。 -/
structure TrigDensity where
  /-- 常数项（源文 `a_j0`）。 -/
  a0 : ℝ
  /-- 一次谐波（源文 `a_j1`）。 -/
  a1 : ℝ
  /-- 二次谐波（源文 `a_j2`）。 -/
  a2 : ℝ
  /-- 三次谐波（源文 `a_j3`）。 -/
  a3 : ℝ
  /-- 源文 `a_j0 ≥ Σ|a_jk|` 的实侧形式（保证处处非负）。 -/
  hnonneg : |a1| + |a2| + |a3| ≤ a0

namespace TrigDensity

/-- 密度函数 `θ ↦ a0 + a1 cos θ + a2 cos 2θ + a3 cos 3θ`。 -/
noncomputable def toFun (W : TrigDensity) (θ : ℝ) : ℝ :=
  W.a0 + W.a1 * Real.cos θ + W.a2 * Real.cos (2 * θ) + W.a3 * Real.cos (3 * θ)

theorem continuous_toFun (W : TrigDensity) : Continuous W.toFun := by
  unfold toFun
  continuity

/-- **非负性**（`a0 ≥ Σ|a_k|` ⟹ 处处非负）。 -/
theorem nonneg_toFun (W : TrigDensity) (θ : ℝ) : 0 ≤ W.toFun θ := by
  have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have h2 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h3 : |Real.cos (3 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have habs : |W.a1 * Real.cos θ + W.a2 * Real.cos (2 * θ) + W.a3 * Real.cos (3 * θ)|
      ≤ |W.a1| + |W.a2| + |W.a3| := by
    calc |W.a1 * Real.cos θ + W.a2 * Real.cos (2 * θ) + W.a3 * Real.cos (3 * θ)|
        ≤ |W.a1 * Real.cos θ| + |W.a2 * Real.cos (2 * θ)| + |W.a3 * Real.cos (3 * θ)| :=
          abs_add_three _ _ _
      _ = |W.a1| * |Real.cos θ| + |W.a2| * |Real.cos (2 * θ)| + |W.a3| * |Real.cos (3 * θ)| := by
          rw [abs_mul, abs_mul, abs_mul]
      _ ≤ |W.a1| * 1 + |W.a2| * 1 + |W.a3| * 1 := by gcongr
      _ = |W.a1| + |W.a2| + |W.a3| := by ring
  have hneg := neg_le_abs (W.a1 * Real.cos θ + W.a2 * Real.cos (2 * θ) + W.a3 * Real.cos (3 * θ))
  unfold toFun
  linarith [W.hnonneg]

/-- `∫_0^{2π} cos (k θ) = 0`（`k ≥ 1`；`k = 0` 时为 `2π`，故必须排除）。 -/
theorem integral_cos_nat_mul {k : ℕ} (hk : 0 < k) :
    ∫ θ in (0)..(2 * Real.pi), Real.cos ((k : ℝ) * θ) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hk
  have hinner : ∀ x : ℝ, HasDerivAt (fun θ : ℝ => (k : ℝ) * θ) (k : ℝ) x :=
    fun x => by simpa using (hasDerivAt_id x).const_mul (k : ℝ)
  have hderiv : ∀ x ∈ [[(0 : ℝ), 2 * Real.pi]],
      HasDerivAt (fun θ : ℝ => Real.sin ((k : ℝ) * θ) / (k : ℝ))
        (Real.cos ((k : ℝ) * x)) x := by
    intro x _
    have h2 := ((Real.hasDerivAt_sin ((k : ℝ) * x)).comp x (hinner x)).div_const (k : ℝ)
    have hval : Real.cos ((k : ℝ) * x) * (k : ℝ) / (k : ℝ) = Real.cos ((k : ℝ) * x) :=
      mul_div_cancel_right₀ _ hk'
    rwa [hval] at h2
  have hint : IntervalIntegrable (fun θ : ℝ => Real.cos ((k : ℝ) * θ)) volume 0 (2 * Real.pi) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable
      (μ := volume) _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  have hsin : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    have hcast : (k : ℝ) * (2 * Real.pi) = ((2 * k : ℕ) : ℤ) * Real.pi := by
      push_cast; ring
    rw [hcast, Real.sin_int_mul_pi]
  rw [hsin]
  simp

/-- **总质量**：`∫_0^{2π} W = 2π a_0`（源文 `B` 的半数口径）。
用单个原函数 `F θ = a0 θ + a1 sin θ + (a2/2) sin 2θ + (a3/3) sin 3θ`，
端点 `sin(2π) = sin(4π) = sin(6π) = 0`。 -/
theorem integral_toFun (W : TrigDensity) :
    ∫ θ in (0)..(2 * Real.pi), W.toFun θ = 2 * Real.pi * W.a0 := by
  have hderiv : ∀ x ∈ [[(0 : ℝ), 2 * Real.pi]],
      HasDerivAt (fun θ : ℝ => W.a0 * θ + W.a1 * Real.sin θ
          + (W.a2 / 2) * Real.sin (2 * θ) + (W.a3 / 3) * Real.sin (3 * θ))
        (W.toFun x) x := by
    intro x _
    have d0 : HasDerivAt (fun θ : ℝ => W.a0 * θ) W.a0 x := by
      simpa using (hasDerivAt_id x).const_mul W.a0
    have d1 : HasDerivAt (fun θ : ℝ => W.a1 * Real.sin θ) (W.a1 * Real.cos x) x :=
      (Real.hasDerivAt_sin x).const_mul W.a1
    have d2 : HasDerivAt (fun θ : ℝ => (W.a2 / 2) * Real.sin (2 * θ))
        ((W.a2 / 2) * (Real.cos (2 * x) * 2)) x :=
      ((Real.hasDerivAt_sin (2 * x)).comp x (by simpa using (hasDerivAt_id x).const_mul (2 : ℝ))).const_mul (W.a2 / 2)
    have d3 : HasDerivAt (fun θ : ℝ => (W.a3 / 3) * Real.sin (3 * θ))
        ((W.a3 / 3) * (Real.cos (3 * x) * 3)) x :=
      ((Real.hasDerivAt_sin (3 * x)).comp x (by simpa using (hasDerivAt_id x).const_mul (3 : ℝ))).const_mul (W.a3 / 3)
    have total := ((d0.add d1).add d2).add d3
    have hfun : ((fun θ : ℝ => W.a0 * θ) + (fun θ : ℝ => W.a1 * Real.sin θ)
          + (fun θ : ℝ => (W.a2 / 2) * Real.sin (2 * θ))
          + (fun θ : ℝ => (W.a3 / 3) * Real.sin (3 * θ)))
        = fun θ : ℝ => W.a0 * θ + W.a1 * Real.sin θ
            + (W.a2 / 2) * Real.sin (2 * θ) + (W.a3 / 3) * Real.sin (3 * θ) := rfl
    have hval : W.a0 + W.a1 * Real.cos x + (W.a2 / 2) * (Real.cos (2 * x) * 2)
          + (W.a3 / 3) * (Real.cos (3 * x) * 3) = W.toFun x := by
      unfold toFun
      ring
    rw [hfun, hval] at total
    exact total
  have hint : IntervalIntegrable W.toFun volume 0 (2 * Real.pi) :=
    W.continuous_toFun.intervalIntegrable (μ := volume) _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  have e1 : Real.sin (2 * Real.pi) = 0 := by
    have hcast : 2 * Real.pi = ((2 : ℤ) : ℝ) * Real.pi := by push_cast; ring
    rw [hcast, Real.sin_int_mul_pi]
  have e2 : Real.sin (2 * (2 * Real.pi)) = 0 := by
    have hcast : 2 * (2 * Real.pi) = ((4 : ℤ) : ℝ) * Real.pi := by push_cast; ring
    rw [hcast, Real.sin_int_mul_pi]
  have e3 : Real.sin (3 * (2 * Real.pi)) = 0 := by
    have hcast : 3 * (2 * Real.pi) = ((6 : ℤ) : ℝ) * Real.pi := by push_cast; ring
    rw [hcast, Real.sin_int_mul_pi]
  simp [e1, e2, e3, Real.sin_zero]
  ring

end TrigDensity

/-- **三角密度版的积分覆盖不等式**（下游真正要用的形状）：
非负三角多项式密度 + 有限 disk 覆盖测试圆 ⟹ `2π a_0 ≤ Σ_i (第 i 盘的弧积分)`。 -/
theorem two_pi_mul_le_sum_arc_integrals {γ : ℝ → Point} (hγ : Continuous γ)
    {W : TrigDensity} {n : ℕ} {c : Fin n → Point} {r : ℝ}
    (hcov : ∀ θ : ℝ, ∃ i : Fin n, dist (γ θ) (c i) ≤ r) :
    2 * Real.pi * W.a0 ≤
      ∑ i : Fin n, ∫ θ in (0)..(2 * Real.pi),
        (if dist (γ θ) (c i) ≤ r then W.toFun θ else 0) := by
  calc 2 * Real.pi * W.a0 = ∫ θ in (0)..(2 * Real.pi), W.toFun θ :=
        (W.integral_toFun).symm
    _ ≤ _ := circle_integral_le_sum_arc_integrals hγ W.continuous_toFun W.nonneg_toFun hcov

/-! ## 第二层：排 hub 的极限引理（`q ↓ R`，**不交换积分极限**）

源文 §2 的内圆论证：对每个 `R < q < 1 − e`，内圆 `S(h,q)` 在 `D` 内且整圈在 hub 闭盘之外，
故必须由**十个环盘**覆盖。把 `q ↓ R` 写成**拓扑**命题（不是积分的极限交换）：对 `q > R`
整圈落在非 hub 盘的并里；令 `q ↓ R`，"**有限个闭盘的并是闭集**" + `dist` 连续 ⟹ `S(h,R)`
**仍**被非 hub 盘整圈覆盖。于是下游可直接对 `q = R` 用第一层不等式，无需指示函数/积分的极限交换。

**口径（源 §5 自查 + Lead 复核）**：`q = R` 时 `S(h,R)` **确实**被 hub 闭盘覆盖，
"`S(h,R)` 未被 hub 覆盖"是错的；正确结论是"`S(h,R)` 已被**非 hub 盘**覆盖"（闭集极限）。

前提：`R > 0`；`‖hub‖ + R < 1`（源文 `R = 19/50`、`‖hub‖ ≤ 7/50` 给余量 `0.48 > 0`）；
覆盖前提只要求 "`D` 被 `n` 个非 hub 盘或 hub 盘覆盖"（= 源文十一盘覆盖 `D`）。 -/

theorem norm_angPt (θ : ℝ) : ‖angPt θ‖ = 1 := by
  rw [angPt, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.cos_sq_add_sin_sq]

/-- `dist (h + a) h = ‖a‖`（算 hub 到测点的距离用）。 -/
theorem dist_add_self (h a : Point) : dist (h + a) h = ‖a‖ := by
  rw [dist_eq_norm, add_sub_cancel_left]

/-- 有限个半径 `R` 闭盘的并是闭集（`∃ i` 形式的并，不需要选下标）。 -/
theorem isClosed_exists_dist_le {n : ℕ} (c : Fin n → Point) (R : ℝ) :
    IsClosed {x : Point | ∃ i : Fin n, dist x (c i) ≤ R} := by
  have hset : {x : Point | ∃ i : Fin n, dist x (c i) ≤ R}
      = ⋃ i : Fin n, Metric.closedBall (c i) R := by
    ext x
    simp [Metric.mem_closedBall]
  rw [hset]
  exact isClosed_iUnion_of_finite fun i => Metric.isClosed_closedBall

/-- **排 hub 的极限引理**：`R > 0`、`‖h‖ + R < 1`，且 `D` 被 `n` 个半径 `R` 的盘与
hub 盘 `B(h,R)` 覆盖 ⟹ hub 中心、半径 `R` 的整圆 `S(h,R)` 已被那 `n` 个盘覆盖。 -/
theorem circle_covered_by_others {h : Point} {R : ℝ} (hR : 0 < R) (hmargin : ‖h‖ + R < 1)
    {n : ℕ} {c : Fin n → Point}
    (hcov : ∀ x : Point, ‖x‖ ≤ 1 → (∃ i : Fin n, dist x (c i) ≤ R) ∨ dist x h ≤ R) :
    ∀ θ : ℝ, ∃ i : Fin n, dist (h + R • angPt θ) (c i) ≤ R := by
  intro θ
  have hU := isClosed_exists_dist_le c R
  have hδ : 0 < 1 - ‖h‖ - R := by linarith
  have hq : Tendsto (fun k : ℕ => R + 1 / ((k : ℝ) + 1)) atTop (nhds R) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmap : Continuous fun q : ℝ => h + q • angPt θ :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hx : Tendsto (fun k : ℕ => h + (R + 1 / ((k : ℝ) + 1)) • angPt θ) atTop
      (nhds (h + R • angPt θ)) := hmap.tendsto R |>.comp hq
  have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < 1 - ‖h‖ - R :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds hδ)
  have hpos_k : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) :=
    fun k => one_div_pos.mpr (by positivity)
  have hev : ∀ᶠ k : ℕ in atTop,
      h + (R + 1 / ((k : ℝ) + 1)) • angPt θ ∈ {x : Point | ∃ i : Fin n, dist x (c i) ≤ R} := by
    filter_upwards [hsmall] with k hk
    have hcoef : (0 : ℝ) < R + 1 / ((k : ℝ) + 1) := by linarith [hpos_k k]
    have hnormv : ‖(R + 1 / ((k : ℝ) + 1)) • angPt θ‖ = R + 1 / ((k : ℝ) + 1) := by
      rw [norm_smul, norm_angPt, mul_one, Real.norm_eq_abs, abs_of_pos hcoef]
    have hnorm : ‖h + (R + 1 / ((k : ℝ) + 1)) • angPt θ‖ ≤ 1 := by
      calc ‖h + (R + 1 / ((k : ℝ) + 1)) • angPt θ‖
          ≤ ‖h‖ + ‖(R + 1 / ((k : ℝ) + 1)) • angPt θ‖ := norm_add_le _ _
        _ = ‖h‖ + (R + 1 / ((k : ℝ) + 1)) := by rw [hnormv]
        _ ≤ 1 := by linarith
    rcases hcov _ hnorm with ⟨i, hi⟩ | hhub
    · exact ⟨i, hi⟩
    · exfalso
      have hdist : dist (h + (R + 1 / ((k : ℝ) + 1)) • angPt θ) h
          = R + 1 / ((k : ℝ) + 1) := by rw [dist_add_self, hnormv]
      linarith [hpos_k k]
  exact hU.mem_of_tendsto hx hev

end

end N11Formalization
