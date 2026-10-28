/-
n11-formalization —— **G2 / `C892Attainment`：源构型 11 盘覆盖闭单位盘 D**

本文件只放**在本会话内真正证成**的东西（零 `sorry`、零自定义 `axiom`、零 `native_decide`）：

| # | 内容 | 等级 |
|---|---|---|
| A | 证书盒心 7 个坐标的**精确有理**对象 `uCert : Fin 12 → ℝ`（几何只读前 7 槽） | 定义 |
| B | **内区**：`B(0, rIn)` 被 hub1 盘覆盖，`rIn = R - \|y1\|`（精确有理） | kernel-proved |
| C | **2D→1D 化归**：外环覆盖 ⟺ 逐方向的**射线区间**判据（`OuterRayObligation`，具名） | kernel-proved（化归） |
| D | **精确紧性**：`dist (arcEnd u k) (ringCenter u k) = u 6`（**无余量**：弧端点恰在盘边界上） | kernel-proved |
| E | 圆周层：`S¹` 被 9 个环盘覆盖（弧拼接 + `cos` 单调性） | kernel-proved |

**为什么 D 重要（对 G2 的路线判断）**：D 说明「覆盖半径 = `u 6`」是**恰好**的：`S¹` 上每个弧端点
到相邻两个环盘中心的距离**正好**等于 `u 6`。因此
`Covers (centersOfRoot u) r` 对 `r < u 6` **为假**（无正余量），任何
「区间算术 + 正余量」的证书方法（含本工程现有区间内核）**不可能**证明 G2 —— G2 必须走
**精确代数 + 方向拼接**的路线。数值地图见 `evidence/g2-cover/`。

写域：本文件 + `evidence/g2-cover/`（不触碰其它成员文件）。
-/
import Mathlib
import N11Formalization.Definitions
import N11Formalization.TCSystem
import N11Formalization.SourceIdentity
import N11Formalization.Geometry.CapArc
import N11Formalization.Geometry.ArcCovering
import N11Formalization.Geometry.InnerRoot
import N11Formalization.Geometry.ArcRoots

set_option linter.unusedVariables false

noncomputable section

namespace N11Formalization

/-! ## A. 证书盒心的精确有理坐标 -/

/-- `a0`（证书盒心，精确有理）。 -/
def qA0 : ℚ := 6701511529285631 / 18014398509481984
/-- `a1`。 -/
def qA1 : ℚ := 6140082802885973 / 18014398509481984
/-- `a2`。 -/
def qA2 : ℚ := 5058838003133637 / 18014398509481984
/-- `a3`。 -/
def qA3 : ℚ := 6899731189335755 / 18014398509481984
/-- `y0`。 -/
def qY0 : ℚ := 4917524862872097 / 18014398509481984
/-- `y1`（负）。 -/
def qY1 : ℚ := -2691864528343895 / 18014398509481984
/-- `R`（= `u 6`；≈ 0.37998385…）。 -/
def qR : ℚ := 6845180557269243 / 18014398509481984

/-- 源构型的**精确有理见证**：前 7 槽 = 证书盒心（`a0,a1,a2,a3,y0,y1,R`），后 5 槽（KKT 乘子）
置 0 —— **几何只读前 7 槽**（`angleVec`/`rhoK`/`hub0`/`hub1` 全部只用 `u 0..u 6`）。 -/
def uCert : Fin 12 → ℝ :=
  ![(qA0 : ℝ), (qA1 : ℝ), (qA2 : ℝ), (qA3 : ℝ), (qY0 : ℝ), (qY1 : ℝ), (qR : ℝ),
    0, 0, 0, 0, 0]

@[simp] theorem uCert_zero : uCert 0 = (qA0 : ℝ) := rfl
@[simp] theorem uCert_one : uCert 1 = (qA1 : ℝ) := rfl
@[simp] theorem uCert_two : uCert 2 = (qA2 : ℝ) := rfl
@[simp] theorem uCert_three : uCert 3 = (qA3 : ℝ) := rfl
@[simp] theorem uCert_four : uCert 4 = (qY0 : ℝ) := rfl
@[simp] theorem uCert_five : uCert 5 = (qY1 : ℝ) := rfl
@[simp] theorem uCert_six : uCert 6 = (qR : ℝ) := rfl

theorem qR_pos : 0 < qR := by norm_num [qR]

theorem qY1_neg : qY1 < 0 := by norm_num [qY1]

theorem qY0_pos : 0 < qY0 := by norm_num [qY0]

/-- `qR < 1`（`R` 是半径，须 `< 1`）。 -/
theorem qR_lt_one : qR < 1 := by norm_num [qR]

/-- 内区半径 `r_in = R - |y1|`（**取小者**：两个 hub 各自给出一个内球，取较大的那个 =
`R - min(|y0|,|y1|)`；本数据 `|y1| < |y0|`，故 `r_in = R + y1`）。 -/
def rIn : ℚ := 4153316028925348 / 18014398509481984

/-- `r_in = R - |y1|` 的精确有理读数。 -/
theorem rIn_eq : rIn = qR + qY1 := by norm_num [rIn, qR, qY1]

/-- 另一个 hub 给出的内球半径 `R - |y0|`（较小，仅作对照）。 -/
def rIn0 : ℚ := 1927655694397146 / 18014398509481984

theorem rIn0_eq : rIn0 = qR - qY0 := by norm_num [rIn0, qR, qY0]

theorem rIn_pos : 0 < rIn := by norm_num [rIn]

/-- `(uCert 6 : ℝ) - |uCert 5| = (rIn : ℝ)`：把「精确有理内区半径」接到构型上。 -/
theorem uCert_six_sub_abs_five : uCert 6 - |uCert 5| = (rIn : ℝ) := by
  have hneg : (qY1 : ℝ) < 0 := by exact_mod_cast qY1_neg
  rw [uCert_six, uCert_five, abs_of_neg hneg]
  have hr : (rIn : ℝ) = (qR : ℝ) + (qY1 : ℝ) := by
    rw [rIn_eq]; push_cast; ring
  rw [hr]; ring

/-! ## B. 内区：hub 盘覆盖以原点为心的球 -/

/-- 坐标分量被范数控制：`|x.ofLp i| ≤ ‖x‖`（`EuclideanSpace ℝ (Fin 2)`）。 -/
theorem abs_ofLp_le_norm (x : Point) (i : Fin 2) : |x.ofLp i| ≤ ‖x‖ := by
  have hsum : ‖x‖ ^ 2 = ∑ j : Fin 2, (x.ofLp j) ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have hb : (x.ofLp i) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hsum]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x.ofLp j)) (Finset.mem_univ i)
  rw [abs_le]
  constructor <;> nlinarith [hb, norm_nonneg x]

/-- **轴上的盘**：中心 `(y,0)`、半径 `R` 的闭盘覆盖 `B(0, R - |y|)`。
证明用 `dist² = ‖x‖² - 2·y·x₀ + y² ≤ (‖x‖ + |y|)²`（不需坐标逐项估计）。 -/
theorem dist_axisDisk_le {x : Point} {y R : ℝ} (hx : ‖x‖ ≤ R - |y|) :
    dist x (!₂[y, (0 : ℝ)] : Point) ≤ R := by
  have hqnorm : ‖(!₂[y, (0 : ℝ)] : Point)‖ = |y| := cons_norm_eq_abs y
  have hinner : inner ℝ x (!₂[y, (0 : ℝ)] : Point) = y * x.ofLp 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct, Fin.sum_univ_two]
    simp
  have hd2 : dist x (!₂[y, (0 : ℝ)] : Point) ^ 2
      = ‖x‖ ^ 2 - 2 * (y * x.ofLp 0) + y ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hqnorm, sq_abs, hinner]
  have hstep : -(2 * (y * x.ofLp 0)) ≤ 2 * |y| * ‖x‖ := by
    have h1 : |x.ofLp 0| ≤ ‖x‖ := abs_ofLp_le_norm x 0
    have h2 : -(y * x.ofLp 0) ≤ |y * x.ofLp 0| := neg_le_abs _
    rw [abs_mul] at h2
    nlinarith [h2, abs_nonneg y, norm_nonneg x, h1]
  have h3 : ‖x‖ ^ 2 - 2 * (y * x.ofLp 0) + y ^ 2 ≤ (‖x‖ + |y|) ^ 2 := by
    nlinarith [hstep, sq_abs y, abs_nonneg y, norm_nonneg x]
  have h4 : ‖x‖ + |y| ≤ R := by linarith
  have h5 : 0 ≤ ‖x‖ + |y| := by positivity
  have hR0 : 0 ≤ R := by linarith [norm_nonneg x, abs_nonneg y]
  have hsq : dist x (!₂[y, (0 : ℝ)] : Point) ^ 2 ≤ R ^ 2 := by
    rw [hd2]
    nlinarith [h3, h4, h5]
  nlinarith [(dist_nonneg : (0 : ℝ) ≤ dist x (!₂[y, (0 : ℝ)] : Point)), hsq, hR0]

/-- `hub1 = (y1, 0)` 的盘覆盖 `B(0, R - |y1|)`。 -/
theorem hub1_covers_ball (u : Fin 12 → ℝ) {x : Point} (hx : ‖x‖ ≤ u 6 - |u 5|) :
    dist x (hub1 u) ≤ u 6 := by
  simpa [hub1] using dist_axisDisk_le (x := x) (y := u 5) (R := u 6) hx

/-- `hub0 = (y0, 0)` 的盘覆盖 `B(0, R - |y0|)`。 -/
theorem hub0_covers_ball (u : Fin 12 → ℝ) {x : Point} (hx : ‖x‖ ≤ u 6 - |u 4|) :
    dist x (hub0 u) ≤ u 6 := by
  simpa [hub0] using dist_axisDisk_le (x := x) (y := u 4) (R := u 6) hx

/-- **内区覆盖（具体实例，kernel-proved，无条件）**：`B(0, rIn)`（`rIn ≈ 0.230555354193`）
被第 10 个盘（`hub1`）覆盖。**注意**：提示里的 `R - max(|y0|,|y1|)` 是偏小的写法；
两 hub 各自给出一个内球，取 min 才是**更强**的正确形式（本数据 `|y1| = 0.1494 < |y0| = 0.2730`）。 -/
theorem covers_inner_lower (x : Point) (hx : ‖x‖ ≤ (rIn : ℝ)) :
    ∃ i : Fin 11, dist x (centersOfRoot uCert i) ≤ (qR : ℝ) := by
  refine ⟨10, ?_⟩
  rw [centersOfRoot_ten]
  refine hub1_covers_ball uCert ?_
  rw [uCert_six_sub_abs_five]
  exact hx

/-! ## C. 2D → 1D：逐方向的射线区间判据 -/

/-- **盘 ∩ 射线 = 区间（1D 判据）**：`‖y‖ = 1`、`r ≥ 0`、`R ≥ 0` 时
`dist (r • y) c ≤ R ⟺ r² - 2 r ⟪y,c⟫ + (‖c‖² - R²) ≤ 0`。

这是把 2D 覆盖问题压到「每个方向上的一维区间覆盖」的接口：
把中心 `c` 换成 `ringCenter u k`，就得到本工程 G2 剩余义务的形状。 -/
theorem ray_mem_iff {y c : Point} {r R : ℝ} (hy : ‖y‖ = 1) (hr : 0 ≤ r) (hR : 0 ≤ R) :
    dist (r • y) c ≤ R ↔ r ^ 2 - 2 * r * inner ℝ y c + (‖c‖ ^ 2 - R ^ 2) ≤ 0 := by
  have hnorm : ‖r • y‖ = r := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one, abs_of_nonneg hr]
  have hsq : dist (r • y) c ^ 2 = r ^ 2 - 2 * r * inner ℝ y c + ‖c‖ ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hnorm]
    rw [real_inner_smul_left]
    ring
  have hiff : dist (r • y) c ≤ R ↔ dist (r • y) c ^ 2 ≤ R ^ 2 := by
    constructor
    · intro h; nlinarith [(dist_nonneg : (0 : ℝ) ≤ dist (r • y) c)]
    · intro h; nlinarith [(dist_nonneg : (0 : ℝ) ≤ dist (r • y) c), hR]
  rw [hiff, hsq]
  constructor <;> intro h <;> linarith

/-- **G2 的外环义务（具名，本会话未证）**：每个单位方向 `y` 上，9 个环盘在射线
`{r • y}` 上的区间覆盖整个 `[rIn, 1]`。等价地（由 `ray_mem_iff`）：对每个
`r ∈ [rIn,1]` 至少一个环盘满足一维二次判据。 -/
def OuterRayObligation (u : Fin 12 → ℝ) (rIn : ℝ) : Prop :=
  ∀ (y : Point), ‖y‖ = 1 → ∀ r : ℝ, rIn ≤ r → r ≤ 1 →
    ∃ k : Fin 9, r ^ 2 - 2 * r * inner ℝ y (ringCenter u k)
      + (‖ringCenter u k‖ ^ 2 - (u 6) ^ 2) ≤ 0

/-- **外环的 2D→1D 化归（kernel-proved）**：`OuterRayObligation` ⟹ 外环 `{rIn ≤ ‖x‖ ≤ 1}`
被 9 个环盘覆盖。 -/
theorem outer_covered_of_ray (u : Fin 12 → ℝ) {rIn : ℝ} (hrIn : 0 < rIn) (hR : 0 ≤ u 6)
    (h : OuterRayObligation u rIn) {x : Point} (hx0 : rIn ≤ ‖x‖) (hx1 : ‖x‖ ≤ 1) :
    ∃ k : Fin 9, dist x (ringCenter u k) ≤ u 6 := by
  have hxne : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx0
    linarith
  have hrne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hxne
  set y : Point := (‖x‖)⁻¹ • x with hy
  have hynorm : ‖y‖ = 1 := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ hrne]
  have hxr : ‖x‖ • y = x := by
    rw [hy, smul_smul, mul_inv_cancel₀ hrne, one_smul]
  have hr0 : 0 ≤ ‖x‖ := norm_nonneg x
  obtain ⟨k, hk⟩ := h y hynorm ‖x‖ hx0 hx1
  refine ⟨k, ?_⟩
  rw [← hxr]
  exact (ray_mem_iff hynorm hr0 hR).mpr hk

/-- **G2 分解（kernel-proved）**：内区（球 `B(0,rIn)`）+ 外环（`rIn ≤ ‖x‖ ≤ 1`）覆盖 ⟹ `Covers`。 -/
theorem covers_of_inner_and_outer (u : Fin 12 → ℝ) {rIn r : ℝ}
    (hinner : ∀ x : Point, ‖x‖ ≤ rIn → ∃ i : Fin 11, dist x (centersOfRoot u i) ≤ r)
    (houter : ∀ x : Point, rIn ≤ ‖x‖ → ‖x‖ ≤ 1 → ∃ i : Fin 11, dist x (centersOfRoot u i) ≤ r) :
    Covers (centersOfRoot u) r := by
  intro x hx
  by_cases h : ‖x‖ ≤ rIn
  · exact hinner x h
  · exact houter x (le_of_lt (not_le.mp h)) hx

/-- **`Covers` 的条形式（定义展开，供下游按 `Covers` 调用）**。 -/
theorem covers_iff (c : Fin 11 → Point) (r : ℝ) : Covers c r ↔ ∀ x ∈ unitDisk, ∃ i, dist x (c i) ≤ r :=
  Iff.rfl

/-- **条件形态：外环义务 ⟹ `Covers (centersOfRoot uCert) qR`**（其余部分已无条件证明）。 -/
theorem covers_cert_of_outer (h : OuterRayObligation uCert (rIn : ℝ)) :
    Covers (centersOfRoot uCert) (qR : ℝ) := by
  refine covers_of_inner_and_outer (rIn := (rIn : ℝ)) (r := (qR : ℝ)) uCert ?_ ?_
  · intro x hx
    exact covers_inner_lower x hx
  · intro x hx0 hx1
    obtain ⟨k, hk⟩ := outer_covered_of_ray uCert (by norm_num [rIn]) (by norm_num [qR]) h hx0 hx1
    exact ⟨⟨(k : ℕ), by omega⟩, by simpa [centersOfRoot_ring] using hk⟩

/-! ## D. 证书角上的 `sin` 控制（`S = a0+a1+a2+a3`） -/

/-- `S = a0+a1+a2+a3`（精确有理，`≈ 1.3766856279762705`）。 -/
def qS : ℚ := 24800163524640996 / 18014398509481984

theorem qS_eq : qS = qA0 + qA1 + qA2 + qA3 := by norm_num [qS, qA0, qA1, qA2, qA3]

/-- 实数形式的同一读数（`simp` 可用的重写方向）。 -/
theorem qA_sum_eq_qS : (qA0 : ℝ) + (qA1 : ℝ) + (qA2 : ℝ) + (qA3 : ℝ) = (qS : ℝ) := by
  norm_num [qA0, qA1, qA2, qA3, qS]

theorem qR_pos_real : (0 : ℝ) < (qR : ℝ) := by exact_mod_cast qR_pos

theorem qR_lt_one_real : (qR : ℝ) < 1 := by exact_mod_cast qR_lt_one

theorem uCert_sum_three : uCert 0 + uCert 1 + uCert 2 + uCert 3 = (qS : ℝ) := by
  rw [uCert_zero, uCert_one, uCert_two, uCert_three, qA_sum_eq_qS]

/-- **五阶 `sin` 上界**（mathlib 只有一阶上界 `sin x ≤ x` 与三阶下界 `x - x³/6 ≤ sin x`）。
路线：先由三阶下界 + 单调性得四阶 `cos` 上界，再由它得五阶 `sin` 上界。 -/
theorem cos_le_one_sub_sq_div_two_add_fourth (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hanti : AntitoneOn (fun t : ℝ => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24)) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      have hsin : t - t ^ 3 / 6 ≤ Real.sin t := Real.sin_ge_sub_cube ht0
      have hd : deriv (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)) t
          = -Real.sin t + t - t ^ 3 / 6 := by
        have h := (Real.hasDerivAt_cos t).sub (((hasDerivAt_const t (1 : ℝ)).sub
          ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24))
        exact (h.congr_deriv (by ring)).deriv
      rw [hd]; linarith
  simpa using hanti (le_refl (0 : ℝ)) hx hx

theorem sin_le_sub_cube_add_fifth (x : ℝ) (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hmono : MonotoneOn (fun t : ℝ => (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      have hcos := cos_le_one_sub_sq_div_two_add_fourth t ht0
      have hd : deriv (fun s : ℝ => (s - s ^ 3 / 6 + s ^ 5 / 120) - Real.sin s) t
          = (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t := by
        have h := (((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub (Real.hasDerivAt_sin t)
        exact (h.congr_deriv (by ring)).deriv
      rw [hd]; linarith
  simpa using hmono (le_refl (0 : ℝ)) hx hx

/-- 五阶多项式 `x - x³/6 + x⁵/120` 在 `[0,1]` 上单调不减（导数 `1 - x²/2 + x⁴/24 ≥ 1/2`）。 -/
theorem poly5_monoOn : MonotoneOn (fun x : ℝ => x - x ^ 3 / 6 + x ^ 5 / 120) (Set.Icc 0 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro t ht
    have ht1 : t ^ 2 ≤ 1 := by
      have h := interior_subset ht
      rw [Set.mem_Icc] at h
      nlinarith [h.1, h.2]
    have hd : deriv (fun s : ℝ => s - s ^ 3 / 6 + s ^ 5 / 120) t = 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
      have h := ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)
      exact (h.congr_deriv (by ring)).deriv
    rw [hd]
    nlinarith [sq_nonneg (t ^ 2), ht1]

theorem sin_qA0_le : Real.sin (qA0 : ℝ) ≤ (qR : ℝ) := by
  have h1 := Real.sin_le (show (0 : ℝ) ≤ (qA0 : ℝ) by norm_num [qA0])
  have h2 : (qA0 : ℝ) ≤ (qR : ℝ) := by norm_num [qA0, qR]
  linarith

theorem sin_qA1_le : Real.sin (qA1 : ℝ) ≤ (qR : ℝ) := by
  have h1 := Real.sin_le (show (0 : ℝ) ≤ (qA1 : ℝ) by norm_num [qA1])
  have h2 : (qA1 : ℝ) ≤ (qR : ℝ) := by norm_num [qA1, qR]
  linarith

theorem sin_qA2_le : Real.sin (qA2 : ℝ) ≤ (qR : ℝ) := by
  have h1 := Real.sin_le (show (0 : ℝ) ≤ (qA2 : ℝ) by norm_num [qA2])
  have h2 : (qA2 : ℝ) ≤ (qR : ℝ) := by norm_num [qA2, qR]
  linarith

theorem sin_qA3_le : Real.sin (qA3 : ℝ) ≤ (qR : ℝ) := by
  have h1 := sin_le_sub_cube_add_fifth (qA3 : ℝ) (by norm_num [qA3])
  have h2 : (qA3 : ℝ) - (qA3 : ℝ) ^ 3 / 6 + (qA3 : ℝ) ^ 5 / 120 ≤ (qR : ℝ) := by
    norm_num [qA3, qR]
  linarith

/-- `a4 = π - 2S ≈ 0.3882214` 处的 `sin` 上界（**余量 1.44e-3**，`p(x) ≤ R`）。 -/
theorem sin_a4_le : Real.sin (Real.pi - 2 * (qS : ℝ)) ≤ (qR : ℝ) := by
  set x : ℝ := Real.pi - 2 * (qS : ℝ) with hxdef
  have hx0 : 0 ≤ x := by
    have h1 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
    have h2 : (qS : ℝ) ≤ (1.3766857 : ℝ) := by norm_num [qS]
    rw [hxdef]; linarith
  have hx1 : x ≤ (0.3882218 : ℝ) := by
    have h1 : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
    have h2 : (1.3766856 : ℝ) ≤ (qS : ℝ) := by norm_num [qS]
    rw [hxdef]; linarith
  have hb := sin_le_sub_cube_add_fifth x hx0
  have hm : x - x ^ 3 / 6 + x ^ 5 / 120
      ≤ (0.3882218 : ℝ) - (0.3882218 : ℝ) ^ 3 / 6 + (0.3882218 : ℝ) ^ 5 / 120 :=
    poly5_monoOn ⟨hx0, by linarith⟩ (by norm_num) hx1
  have h2 : (0.3882218 : ℝ) - (0.3882218 : ℝ) ^ 3 / 6 + (0.3882218 : ℝ) ^ 5 / 120
      ≤ (qR : ℝ) := by norm_num [qR]
  linarith

/-- `angleVec uCert` 的显式九槽表（把 `a4 = π - 2S` 写成 `qS`）。 -/
theorem angleVec_uCert_eq : angleVec uCert =
    ![(qA0 : ℝ), (qA1 : ℝ), (qA2 : ℝ), (qA3 : ℝ), Real.pi - 2 * (qS : ℝ),
      (qA3 : ℝ), (qA2 : ℝ), (qA1 : ℝ), (qA0 : ℝ)] := by
  funext i
  fin_cases i <;> simp [angleVec_eq_list, uCert, qA_sum_eq_qS]

/-- 每个证书角都在 `[0, 1]`（`a4` 处用 `π ∈ (3.141592, 3.141593)`）。 -/
theorem angleVec_uCert_mem01 (k : Fin 9) :
    0 ≤ angleVec uCert k ∧ angleVec uCert k ≤ 1 := by
  rw [angleVec_uCert_eq]
  fin_cases k <;>
    · constructor <;>
      norm_num [qA0, qA1, qA2, qA3, qS] <;>
      linarith [Real.pi_gt_d6, Real.pi_lt_d6, Real.pi_pos]

/-- 每个证书角都在 `[0, π]`。 -/
theorem angleVec_uCert_mem (k : Fin 9) :
    0 ≤ angleVec uCert k ∧ angleVec uCert k ≤ Real.pi :=
  ⟨(angleVec_uCert_mem01 k).1, le_trans (angleVec_uCert_mem01 k).2 (by linarith [Real.pi_gt_three])⟩

/-- **九个证书角上 `sin a_k ≤ R`**（`a0,a1,a2` 用一阶界；`a3`、`a4` 用五阶界）。 -/
theorem sin_angleVec_le_R (k : Fin 9) : Real.sin (angleVec uCert k) ≤ (qR : ℝ) := by
  rw [angleVec_uCert_eq]
  fin_cases k <;>
    simp only [Fin.reduceFinMk]
  · exact sin_qA0_le
  · exact sin_qA1_le
  · exact sin_qA2_le
  · exact sin_qA3_le
  · exact sin_a4_le
  · exact sin_qA3_le
  · exact sin_qA2_le
  · exact sin_qA1_le
  · exact sin_qA0_le

/-- **`sin² a_k ≤ R²`**（弧/盘相交的非退化条件；`k=0..4` 即全部，`k=5..8` 由回文性）。 -/
theorem sin_sq_angleVec_le (k : Fin 9) :
    Real.sin (angleVec uCert k) ^ 2 ≤ (uCert 6) ^ 2 := by
  have h1 := sin_angleVec_le_R k
  have h0 : 0 ≤ Real.sin (angleVec uCert k) := by
    have hm := angleVec_uCert_mem k
    exact Real.sin_nonneg_of_nonneg_of_le_pi hm.1 hm.2
  rw [uCert_six]
  nlinarith [h1, h0, qR_pos]

/-! ## E. 精确紧性：弧端点恰在环盘边界上（**零余量**） -/

/-- **径向根的代数关系**：`ρ = cos a - √(R² - sin²a)` 满足 `ρ² - 2ρ cos a + 1 = R²`
（即「盘 `B(C,R)` 与单位圆的两交点恰在方向 `θ ± a`」的代数核心）。 -/
theorem radial_root_relation {a R : ℝ} (hs : Real.sin a ^ 2 ≤ R ^ 2) :
    (Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) ^ 2
      - 2 * (Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) * Real.cos a + 1 = R ^ 2 := by
  have hsq : Real.sqrt (R ^ 2 - Real.sin a ^ 2) ^ 2 = R ^ 2 - Real.sin a ^ 2 :=
    Real.sq_sqrt (by linarith)
  nlinarith [hsq, Real.sin_sq_add_cos_sq a]

theorem ringCenter_eq_smul (u : Fin 12 → ℝ) (k : Fin 9) :
    ringCenter u k = rhoK u k • circleMap (thetaOf (angleVec u) k) := by
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp [ringCenter, circleMap, PiLp.smul_apply]

theorem arcEnd_eq_circleMap (u : Fin 12 → ℝ) (k : Fin 9) :
    arcEnd u k = circleMap (thetaOf (angleVec u) k + angleVec u k) := by
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp [arcEnd, circleMap]

/-- **`ρ ≥ 0` 的一般引理**：`|R| ≤ 1`、`sin²a ≤ R²`、`cos a ≥ 0` ⟹ `cos a - √(R²-sin²a) ≥ 0`。 -/
theorem radial_root_nonneg {a R : ℝ} (hR0 : -1 ≤ R) (hR1 : R < 1) (hs : Real.sin a ^ 2 ≤ R ^ 2)
    (hc : 0 ≤ Real.cos a) :
    0 ≤ Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2) := by
  have hs2 : Real.sqrt (R ^ 2 - Real.sin a ^ 2) ^ 2 = R ^ 2 - Real.sin a ^ 2 :=
    Real.sq_sqrt (by linarith)
  have hcos2 : Real.cos a ^ 2 = 1 - Real.sin a ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq a]
  have hsq : Real.sqrt (R ^ 2 - Real.sin a ^ 2) ^ 2 ≤ Real.cos a ^ 2 := by
    rw [hs2, hcos2]; nlinarith
  have h2 := sq_le_sq.mp hsq
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hc] at h2
  linarith

/-- `ρ_k ≥ 0`（具体数据：`cos a_k > 0` 由 `a_k ≤ 1` 与二阶 `cos` 下界给出）。 -/
theorem rhoK_nonneg_cert (k : Fin 9) : 0 ≤ rhoK uCert k := by
  have ha1 : angleVec uCert k ^ 2 ≤ 1 := by
    have h := angleVec_uCert_mem01 k
    nlinarith [h.1, h.2]
  have hcospos : 0 < Real.cos (angleVec uCert k) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := angleVec uCert k)
    nlinarith
  simp only [rhoK]
  exact radial_root_nonneg (R := uCert 6) (a := angleVec uCert k)
    (by rw [uCert_six]; linarith [qR_pos_real]) (by rw [uCert_six]; exact qR_lt_one_real)
    (sin_sq_angleVec_le k) hcospos.le

/-- **盘边界的统一形态**：`‖x‖ = 1` 且 `⟪x, û_k⟫ = cos a_k`（`û_k` = 弧中点方向）
时 `dist x (C_k) = u 6` —— 弧的两个端点都满足该条件，故都**恰在盘边界上**。 -/
theorem dist_eq_radius_of_inner (u : Fin 12 → ℝ) (k : Fin 9) (x : Point) (hx : ‖x‖ = 1)
    (hs : Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6)
    (hip : inner ℝ x (circleMap (thetaOf (angleVec u) k)) = Real.cos (angleVec u k)) :
    dist x (ringCenter u k) = u 6 := by
  have hroot := radial_root_relation (a := angleVec u k) (R := u 6) hs
  have hnorm2 : ‖ringCenter u k‖ ^ 2
      = (Real.cos (angleVec u k) - Real.sqrt ((u 6) ^ 2 - Real.sin (angleVec u k) ^ 2)) ^ 2 := by
    rw [ringCenter_eq_smul, norm_smul, circleMap_norm, mul_one, Real.norm_eq_abs, sq_abs]
    simp only [rhoK]
  have hinner : inner ℝ x (ringCenter u k)
      = (Real.cos (angleVec u k) - Real.sqrt ((u 6) ^ 2 - Real.sin (angleVec u k) ^ 2))
        * Real.cos (angleVec u k) := by
    rw [ringCenter_eq_smul, real_inner_smul_right, hip]
    simp only [rhoK]
  have hdist : dist x (ringCenter u k) ^ 2 = (u 6) ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hx, hnorm2, hinner]
    nlinarith [hroot]
  nlinarith [(dist_nonneg : (0 : ℝ) ≤ dist x (ringCenter u k)), hdist, hR]

/-- **右弧端点**：`B_k = (cos(θ_k+a_k), sin(θ_k+a_k))` 到 `C_k` 的距离**恰为** `u 6`。 -/
theorem dist_arcEnd_ringCenter (u : Fin 12 → ℝ) (k : Fin 9)
    (hs : Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) :
    dist (arcEnd u k) (ringCenter u k) = u 6 := by
  refine dist_eq_radius_of_inner u k (arcEnd u k) ?_ hs hR ?_
  · rw [arcEnd_eq_circleMap, circleMap_norm]
  · rw [arcEnd_eq_circleMap, inner_circleMap]
    congr 1
    ring

/-- **左弧端点**同样恰在盘边界上（`cos` 为偶函数：`cos(-a_k) = cos a_k`）。 -/
theorem dist_arcLo_ringCenter (u : Fin 12 → ℝ) (k : Fin 9)
    (hs : Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) :
    dist (circleMap (thetaOf (angleVec u) k - angleVec u k)) (ringCenter u k) = u 6 := by
  refine dist_eq_radius_of_inner u k (circleMap (thetaOf (angleVec u) k - angleVec u k))
    (circleMap_norm _) hs hR ?_
  rw [inner_circleMap]
  have harg : (thetaOf (angleVec u) k - angleVec u k) - thetaOf (angleVec u) k
      = -angleVec u k := by ring
  rw [harg, Real.cos_neg]

/-- 具体读数：九个**右**弧端点各自到对应环盘中心的距离 **恰为 `qR`**。 -/
theorem dist_arcEnd_centersOfRoot_cert (k : Fin 9) :
    dist (arcEnd uCert k) (centersOfRoot uCert ⟨(k : ℕ), by omega⟩) = (qR : ℝ) := by
  rw [centersOfRoot_ring]
  refine dist_arcEnd_ringCenter uCert k (sin_sq_angleVec_le k) ?_
  rw [uCert_six]; exact_mod_cast qR_pos.le

/-- 具体读数：九个**左**弧端点（`circleMap (θ_k - a_k)`）同理。 -/
theorem dist_arcLo_centersOfRoot_cert (k : Fin 9) :
    dist (circleMap (thetaOf (angleVec uCert) k - angleVec uCert k))
      (centersOfRoot uCert ⟨(k : ℕ), by omega⟩) = (qR : ℝ) := by
  rw [centersOfRoot_ring]
  refine dist_arcLo_ringCenter uCert k (sin_sq_angleVec_le k) ?_
  rw [uCert_six]; exact_mod_cast qR_pos.le

/-! ## G. 统一形式的硬点：`φ = π`（负 x 轴）由残差方程**精确**闭合

（本节放在文件末，便于复用前面的 `circleMap_pi` 等工具。）

零余量方向的处理**不靠数值**：在源系统里 `residual u 3 = 0`（即 `|U_8 − H1| = u 6`）**精确**
蕴含「hub1 盘覆盖 `[0, R−y1]`、环盘 0/8 覆盖 `[ρ²−R², 1]`」且两区间**恰好相接**
（`R − y1 = ρ² − R²`）。这是 G2 统一形式 `residual u = 0 ⟹ Covers (centersOfRoot u) (u 6)`
的可行技术：**紧处用残差方程代数消掉，不紧处才用带余量的分块证书**。

（对照：盒心 `uCert` 的 `residual 3 = −6.9e-18 ≠ 0`，该点余量仅 7e-18，
故「具体见证 uCert」路线的严格化不可行；见 `evidence/g2-cover/residual_check.out.txt`。） -/

/-- 一般 θ 读数：`θ_8 = π − a_0`（任意 `u`）。 -/
theorem thetaOf_eight (u : Fin 12 → ℝ) : thetaOf (angleVec u) 8 = Real.pi - angleVec u 0 := by
  simp only [thetaOf, angleVec]
  simp
  ring_nf

/-- 一般 θ 读数：`θ_0 = a_0 − π`（任意 `u`）。 -/
theorem thetaOf_zero (u : Fin 12 → ℝ) : thetaOf (angleVec u) 0 = angleVec u 0 - Real.pi := by
  simp only [thetaOf, angleVec]
  simp
  ring_nf

/-- `a_8 = a_0`（回文）。 -/
theorem angleVec_eight_eq_zero (u : Fin 12 → ℝ) : angleVec u 8 = angleVec u 0 := by
  simp [angleVec]

/-- `ρ_8 = ρ_0`（同一角值）。 -/
theorem rhoK_eight_eq_zero (u : Fin 12 → ℝ) : rhoK u 8 = rhoK u 0 := by
  simp only [rhoK, angleVec_eight_eq_zero]

/-- `θ_8 + a_8 = π` ⇒ `arcEnd u 8 = (−1, 0)`（任意 `u`）。 -/
theorem arcEnd_eight (u : Fin 12 → ℝ) : arcEnd u 8 = (!₂[(-1 : ℝ), 0] : Point) := by
  rw [arcEnd_eq_circleMap, thetaOf_eight, angleVec_eight_eq_zero]
  have h : Real.pi - angleVec u 0 + angleVec u 0 = Real.pi := by ring
  rw [h]
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp [circleMap, Real.cos_pi, Real.sin_pi]

theorem arcEnd_eight_coord0 (u : Fin 12 → ℝ) : (arcEnd u 8).ofLp 0 = -1 := by
  rw [arcEnd_coord0, thetaOf_eight, angleVec_eight_eq_zero]
  have h : Real.pi - angleVec u 0 + angleVec u 0 = Real.pi := by ring
  rw [h, Real.cos_pi]

theorem arcEnd_eight_coord1 (u : Fin 12 → ℝ) : (arcEnd u 8).ofLp 1 = 0 := by
  rw [arcEnd_coord1, thetaOf_eight, angleVec_eight_eq_zero]
  have h : Real.pi - angleVec u 0 + angleVec u 0 = Real.pi := by ring
  rw [h, Real.sin_pi]

theorem ringCenter_eight_add_zero_coord0 (u : Fin 12 → ℝ) :
    (ringCenter u 8).ofLp 0 + (ringCenter u 0).ofLp 0
      = -(2 * rhoK u 0 * Real.cos (angleVec u 0)) := by
  rw [ringCenter_coord0, ringCenter_coord0, thetaOf_eight, thetaOf_zero, rhoK_eight_eq_zero,
    Real.cos_pi_sub, Real.cos_sub, Real.cos_pi, Real.sin_pi]
  ring

theorem ringCenter_eight_add_zero_coord1 (u : Fin 12 → ℝ) :
    (ringCenter u 8).ofLp 1 + (ringCenter u 0).ofLp 1 = 0 := by
  rw [ringCenter_coord1, ringCenter_coord1, thetaOf_eight, thetaOf_zero, rhoK_eight_eq_zero,
    Real.sin_pi_sub, Real.sin_sub, Real.cos_pi, Real.sin_pi]
  ring

theorem fin_eight_add_one : (8 + 1 : Fin 9) = 0 := by decide

theorem pinch_pair_coord0 (L : ℝ) : (!₂[-L, 0] : Point).ofLp 0 = -L := rfl
theorem pinch_pair_coord1 (L : ℝ) : (!₂[-L, 0] : Point).ofLp 1 = 0 := rfl
theorem neg_pair_coord0 (r : ℝ) : (!₂[(-r), 0] : Point).ofLp 0 = -r := rfl
theorem neg_pair_coord1 (r : ℝ) : (!₂[(-r), 0] : Point).ofLp 1 = 0 := rfl

/-- **源残差的 pinch 形态（任意 `u`）**：`U_8 = (−(ρ_0²−R²), 0)`。 -/
theorem Uvec_eight_eq (u : Fin 12 → ℝ) (hs : Real.sin (angleVec u 0) ^ 2 ≤ (u 6) ^ 2) :
    Uvec u 8 = (!₂[-(rhoK u 0 ^ 2 - (u 6) ^ 2), 0] : Point) := by
  have hroot := radial_root_relation (a := angleVec u 0) (R := u 6) hs
  refine PiLp.ext (fun i => ?_)
  fin_cases i
  · show (Uvec u 8).ofLp 0 = (!₂[-(rhoK u 0 ^ 2 - (u 6) ^ 2), 0] : Point).ofLp 0
    rw [pinch_pair_coord0, Uvec_coord0, fin_eight_add_one,
      ringCenter_eight_add_zero_coord0, arcEnd_eight_coord0, rhoK_eq u 0]
    linarith
  · show (Uvec u 8).ofLp 1 = (!₂[-(rhoK u 0 ^ 2 - (u 6) ^ 2), 0] : Point).ofLp 1
    rw [pinch_pair_coord1, Uvec_coord1, fin_eight_add_one,
      ringCenter_eight_add_zero_coord1, arcEnd_eight_coord1]
    ring

/-- 负 x 轴上的点到 `C_8` 的距离平方（`θ_8 = π−a_0`、`ρ_8 = ρ_0`）。 -/
theorem dist_neg_axis_ringCenter_eight_sq (u : Fin 12 → ℝ) (r : ℝ) :
    dist (!₂[(-r), 0] : Point) (ringCenter u 8) ^ 2
      = r ^ 2 - 2 * r * (rhoK u 0 * Real.cos (angleVec u 0)) + rhoK u 0 ^ 2 := by
  rw [dist_point_eq_sqrt, neg_pair_coord0, neg_pair_coord1, ringCenter_coord0,
    ringCenter_coord1, thetaOf_eight, rhoK_eight_eq_zero, Real.cos_pi_sub, Real.sin_pi_sub]
  have hxy : (-r - rhoK u 0 * -Real.cos (angleVec u 0)) ^ 2
      + ((0 : ℝ) - rhoK u 0 * Real.sin (angleVec u 0)) ^ 2
      = r ^ 2 - 2 * r * (rhoK u 0 * Real.cos (angleVec u 0)) + rhoK u 0 ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (angleVec u 0)]
  have hnn : 0 ≤ (-r - rhoK u 0 * -Real.cos (angleVec u 0)) ^ 2
      + ((0 : ℝ) - rhoK u 0 * Real.sin (angleVec u 0)) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnn' : 0 ≤ r ^ 2 - 2 * r * (rhoK u 0 * Real.cos (angleVec u 0)) + rhoK u 0 ^ 2 := by
    rw [← hxy]; exact hnn
  rw [hxy, Real.sq_sqrt hnn']

/-- `dist² ≤ R²`（`0 ≤ dist`、`0 ≤ R`）⟹ `dist ≤ R`（避免 `nlinarith` 直接处理平方根式）。 -/
theorem le_of_sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by nlinarith

/-- `dist x C_8² − R²` 的因式分解：紧性的代数核心（环盘 0/8 的射线区间恰是 `[ρ²−R², 1]`）。 -/
theorem dist_neg_axis_ringCenter_eight_sq_sub (u : Fin 12 → ℝ)
    (hs : Real.sin (angleVec u 0) ^ 2 ≤ (u 6) ^ 2) (r : ℝ) :
    dist (!₂[(-r), 0] : Point) (ringCenter u 8) ^ 2 - (u 6) ^ 2
      = (r - 1) * (r - (rhoK u 0 ^ 2 - (u 6) ^ 2)) := by
  have hroot := radial_root_relation (a := angleVec u 0) (R := u 6) hs
  rw [dist_neg_axis_ringCenter_eight_sq, rhoK_eq u 0]
  set c := Real.cos (angleVec u 0)
  set s := Real.sqrt ((u 6) ^ 2 - Real.sin (angleVec u 0) ^ 2)
  have hc : (c - s) ^ 2 - 2 * (c - s) * c + 1 - (u 6) ^ 2 = 0 := by linarith
  calc r ^ 2 - 2 * r * ((c - s) * c) + (c - s) ^ 2 - (u 6) ^ 2
      = r * ((c - s) ^ 2 - 2 * (c - s) * c + 1 - (u 6) ^ 2)
        + (r - 1) * (r - ((c - s) ^ 2 - (u 6) ^ 2)) := by ring
    _ = (r - 1) * (r - ((c - s) ^ 2 - (u 6) ^ 2)) := by rw [hc]; ring

/-- **零余量方向闭合（统一形式）**：`residual u 3 = 0` 时，负 x 轴上每一点
（`0 ≤ r ≤ 1`）都被 hub1 盘**或**环盘 0/8 覆盖，两段**恰好相接**，无需任何数值余量。 -/
theorem neg_axis_covered_of_residual (u : Fin 12 → ℝ)
    (hs : Real.sin (angleVec u 0) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) (hy1 : u 5 ≤ 0)
    (hRy : 0 ≤ u 6 + u 5) (h3 : residual u 3 = 0) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    dist (!₂[(-r), 0] : Point) (hub1 u) ≤ u 6
      ∨ dist (!₂[(-r), 0] : Point) (ringCenter u 8) ≤ u 6 := by
  have hU := Uvec_eight_eq u hs
  have hhubsm : hub1 u = u 5 • (!₂[(1 : ℝ), 0] : Point) := by
    rw [hub1, smul_cons_zero, mul_one]
  have hd3 : dist (Uvec u 8) (hub1 u) = u 6 := by
    have hc := residual_comp_3 u
    rw [hc] at h3
    linarith
  have habs : |(-(rhoK u 0 ^ 2 - (u 6) ^ 2)) - u 5| = u 6 := by
    rw [hU, hhubsm] at hd3
    rwa [dist_cons_smul_cons] at hd3
  have hLle : rhoK u 0 ^ 2 - (u 6) ^ 2 ≤ u 6 - u 5 := by
    rcases (abs_eq hR).mp habs with h | h <;> linarith
  by_cases hr : r ≤ u 6 - u 5
  · left
    have h1 : dist (!₂[(-r), 0] : Point) (hub1 u) = |(-r) - u 5| := by
      rw [hhubsm, dist_cons_smul_cons]
    rw [h1, abs_le]
    constructor <;> linarith
  · right
    rw [not_le] at hr
    have hfac := dist_neg_axis_ringCenter_eight_sq_sub u hs r
    have hprod : (r - 1) * (r - (rhoK u 0 ^ 2 - (u 6) ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have h2 : dist (!₂[(-r), 0] : Point) (ringCenter u 8) ^ 2 ≤ (u 6) ^ 2 := by
      linarith [hfac, hprod]
    exact le_of_sq_le_sq_of_nonneg (dist_nonneg) hR h2

theorem hqS_real : (qS : ℝ) = (qA0 : ℝ) + (qA1 : ℝ) + (qA2 : ℝ) + (qA3 : ℝ) := by
  rw [qS_eq]; push_cast; ring

theorem thetaOf_uCert_eight : thetaOf (angleVec uCert) 8 = Real.pi - (qA0 : ℝ) := by
  rw [angleVec_uCert_eq]
  simp only [thetaOf]
  simp
  rw [hqS_real]; ring

theorem thetaOf_uCert_zero : thetaOf (angleVec uCert) 0 = (qA0 : ℝ) - Real.pi := by
  rw [angleVec_uCert_eq]
  simp only [thetaOf]
  simp
  rw [hqS_real]; ring

theorem angleVec_uCert_eight : angleVec uCert 8 = (qA0 : ℝ) := by
  rw [angleVec_uCert_eq]; simp

theorem angleVec_uCert_zero : angleVec uCert 0 = (qA0 : ℝ) := by
  rw [angleVec_uCert_eq]; simp

/-- `(-1,0) = circleMap (-π) = circleMap π`。 -/
theorem circleMap_neg_pi : circleMap (-Real.pi) = (!₂[(-1 : ℝ), 0] : Point) := by
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp [circleMap, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]

theorem circleMap_pi : circleMap Real.pi = (!₂[(-1 : ℝ), 0] : Point) := by
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp [circleMap, Real.cos_pi, Real.sin_pi]

/-- 弧的左端点 `s_0 = -π`（`θ_0 - a_0 = -π`）。 -/
theorem arcLo_zero_eq : thetaOf (angleVec uCert) 0 - angleVec uCert 0 = -Real.pi := by
  rw [thetaOf_uCert_zero, angleVec_uCert_zero]; ring

/-- 弧的右端点 `t_8 = π`（`θ_8 + a_8 = π`）。 -/
theorem arcHi_eight_eq : thetaOf (angleVec uCert) 8 + angleVec uCert 8 = Real.pi := by
  rw [thetaOf_uCert_eight, angleVec_uCert_eight]; ring

/-- **核心紧性读数（`(-1,0)` 处）**：`(-1,0) ∈ D` 到 `C_8` 与 `C_0` 的距离都**恰为 `qR`**。 -/
theorem dist_neg_one_zero_ringCenter_eight :
    dist (!₂[(-1 : ℝ), 0] : Point) (ringCenter uCert 8) = (qR : ℝ) := by
  rw [← circleMap_pi, ← arcHi_eight_eq]
  exact dist_arcEnd_centersOfRoot_cert 8

theorem dist_neg_one_zero_ringCenter_zero :
    dist (!₂[(-1 : ℝ), 0] : Point) (ringCenter uCert 0) = (qR : ℝ) := by
  rw [← circleMap_neg_pi, ← arcLo_zero_eq]
  exact dist_arcLo_centersOfRoot_cert 0

/-! ## F. 圆周层：`S¹` 被 9 个环盘覆盖（弧链拼接 + `cos` 单调性）

关键结构事实：九个弧 `[θ_k - a_k, θ_k + a_k]` **恰好首尾相接**（`t_k = s_{k+1}` 由
`thetaOf` 的递推给出；两端 `s_0 = -π`、`t_8 = π` 由 `a4 = π - 2(a0+a1+a2+a3)` 给出），
故 `[-π, π]` 无缝隙可钻。下面把这段话变成 kernel 证明：
`arcLo`/`arcHi` 是十个端点的**显式**读数，`arcEndpoints` 把它们与 `thetaOf` 对齐，
`arc_chain_cover` 做九次二分会枝。 -/

/-- 九个弧的**左端点** `θ_k - a_k`。 -/
def arcLo : Fin 9 → ℝ :=
  ![-Real.pi,
    -Real.pi + 2 * (qA0 : ℝ),
    -Real.pi + 2 * (qA0 : ℝ) + 2 * (qA1 : ℝ),
    -Real.pi + 2 * (qA0 : ℝ) + 2 * (qA1 : ℝ) + 2 * (qA2 : ℝ),
    2 * (qS : ℝ) - Real.pi,
    Real.pi - 2 * (qS : ℝ),
    Real.pi - 2 * (qS : ℝ) + 2 * (qA3 : ℝ),
    Real.pi - 2 * (qS : ℝ) + 2 * (qA3 : ℝ) + 2 * (qA2 : ℝ),
    Real.pi - 2 * (qS : ℝ) + 2 * (qA3 : ℝ) + 2 * (qA2 : ℝ) + 2 * (qA1 : ℝ)]

/-- 九个弧的**右端点** `θ_k + a_k`（= 下一个弧的左端点，除 `k = 8` 处为 `π`）。 -/
def arcHi : Fin 9 → ℝ :=
  ![-Real.pi + 2 * (qA0 : ℝ),
    -Real.pi + 2 * (qA0 : ℝ) + 2 * (qA1 : ℝ),
    -Real.pi + 2 * (qA0 : ℝ) + 2 * (qA1 : ℝ) + 2 * (qA2 : ℝ),
    2 * (qS : ℝ) - Real.pi,
    Real.pi - 2 * (qS : ℝ),
    Real.pi - 2 * (qS : ℝ) + 2 * (qA3 : ℝ),
    Real.pi - 2 * (qS : ℝ) + 2 * (qA3 : ℝ) + 2 * (qA2 : ℝ),
    Real.pi - 2 * (qS : ℝ) + 2 * (qA3 : ℝ) + 2 * (qA2 : ℝ) + 2 * (qA1 : ℝ),
    Real.pi]

/-- **端点对齐**：`thetaOf` 给出的 `θ_k ± a_k` 就是显式读数 `arcLo k`/`arcHi k`。 -/
theorem arcEndpoints (k : Fin 9) :
    thetaOf (angleVec uCert) k - angleVec uCert k = arcLo k ∧
      thetaOf (angleVec uCert) k + angleVec uCert k = arcHi k := by
  rw [angleVec_uCert_eq]
  fin_cases k <;>
    (constructor <;>
      · simp only [thetaOf]
        simp [arcLo, arcHi, hqS_real]
        try ring)

/-- **弧链无缝隙**：任何 `φ ∈ [-π, π]` 落在某个弧 `[θ_k - a_k, θ_k + a_k]` 内。 -/
theorem arc_chain_cover {φ : ℝ} (hlo : -Real.pi ≤ φ) (hhi : φ ≤ Real.pi) :
    ∃ k : Fin 9, arcLo k ≤ φ ∧ φ ≤ arcHi k := by
  by_cases h0 : φ ≤ arcHi 0
  · exact ⟨0, by simp [arcLo]; linarith [Real.pi_pos], h0⟩
  · rw [not_le] at h0
    by_cases h1 : φ ≤ arcHi 1
    · exact ⟨1, by simp [arcLo, arcHi] at *; linarith, h1⟩
    · rw [not_le] at h1
      by_cases h2 : φ ≤ arcHi 2
      · exact ⟨2, by simp [arcLo, arcHi] at *; linarith, h2⟩
      · rw [not_le] at h2
        by_cases h3 : φ ≤ arcHi 3
        · exact ⟨3, by simp [arcLo, arcHi] at *; linarith, h3⟩
        · rw [not_le] at h3
          by_cases h4 : φ ≤ arcHi 4
          · exact ⟨4, by simp [arcLo, arcHi] at *; linarith, h4⟩
          · rw [not_le] at h4
            by_cases h5 : φ ≤ arcHi 5
            · exact ⟨5, by simp [arcLo, arcHi] at *; linarith, h5⟩
            · rw [not_le] at h5
              by_cases h6 : φ ≤ arcHi 6
              · exact ⟨6, by simp [arcLo, arcHi] at *; linarith, h6⟩
              · rw [not_le] at h6
                by_cases h7 : φ ≤ arcHi 7
                · exact ⟨7, by simp [arcLo, arcHi] at *; linarith, h7⟩
                · rw [not_le] at h7
                  exact ⟨8, by simp [arcLo, arcHi] at *; linarith, hhi⟩

/-- **盘覆盖条件的内积形态**：`‖x‖ = 1` 且 `cos a_k ≤ ⟪x, û_k⟫` ⟹ `dist x (C_k) ≤ u 6`。 -/
theorem dist_le_radius_of_inner (u : Fin 12 → ℝ) (k : Fin 9) (x : Point) (hx : ‖x‖ = 1)
    (hs : Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) (hρ : 0 ≤ rhoK u k)
    (hip : Real.cos (angleVec u k) ≤ inner ℝ x (circleMap (thetaOf (angleVec u) k))) :
    dist x (ringCenter u k) ≤ u 6 := by
  have hroot := radial_root_relation (a := angleVec u k) (R := u 6) hs
  have hnorm2 : ‖ringCenter u k‖ ^ 2 = rhoK u k ^ 2 := by
    rw [ringCenter_eq_smul, norm_smul, circleMap_norm, mul_one, Real.norm_eq_abs, sq_abs]
  have hinner : inner ℝ x (ringCenter u k)
      = rhoK u k * inner ℝ x (circleMap (thetaOf (angleVec u) k)) := by
    rw [ringCenter_eq_smul, real_inner_smul_right]
  have hkey : 1 + ‖ringCenter u k‖ ^ 2 - (u 6) ^ 2 ≤ 2 * inner ℝ x (ringCenter u k) := by
    rw [hnorm2, hinner]
    have h2 := mul_le_mul_of_nonneg_left hip hρ
    simp only [rhoK] at h2 ⊢
    linarith [hroot, h2]
  exact (mem_sphere_closedBall_iff hR hx).mpr hkey

/-- **圆周覆盖（kernel-proved，无条件）**：`S¹` 上每一点都被 9 个环盘（半径 `qR`）覆盖。 -/
theorem circle_covered (x : Point) (hx : ‖x‖ = 1) :
    ∃ k : Fin 9, dist x (ringCenter uCert k) ≤ (qR : ℝ) := by
  have hmem := circleAngle_mem_Ioc x
  obtain ⟨k, hklo, hkhi⟩ := arc_chain_cover (le_of_lt hmem.1) hmem.2
  refine ⟨k, dist_le_radius_of_inner uCert k x hx (sin_sq_angleVec_le k)
    (by rw [uCert_six]; exact_mod_cast qR_pos.le) (rhoK_nonneg_cert k) ?_⟩
  rw [← circleMap_circleAngle x hx, inner_circleMap]
  have hangle := angleVec_uCert_mem k
  have hep := arcEndpoints k
  have habs : |circleAngle x - thetaOf (angleVec uCert) k| ≤ angleVec uCert k := by
    rw [abs_le]
    exact ⟨by linarith [hklo, hep.1], by linarith [hkhi, hep.2]⟩
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hangle.2 habs
  rwa [Real.cos_abs] at h

/-! ## 可信基础 -/

#print axioms N11Formalization.covers_inner_lower
#print axioms N11Formalization.outer_covered_of_ray
#print axioms N11Formalization.covers_of_inner_and_outer
#print axioms N11Formalization.covers_cert_of_outer
#print axioms N11Formalization.sin_le_sub_cube_add_fifth
#print axioms N11Formalization.sin_sq_angleVec_le
#print axioms N11Formalization.dist_arcEnd_ringCenter
#print axioms N11Formalization.dist_arcLo_ringCenter
#print axioms N11Formalization.dist_neg_one_zero_ringCenter_eight
#print axioms N11Formalization.dist_neg_one_zero_ringCenter_zero
#print axioms N11Formalization.arc_chain_cover
#print axioms N11Formalization.circle_covered
#print axioms N11Formalization.thetaOf_eight
#print axioms N11Formalization.arcEnd_eight
#print axioms N11Formalization.Uvec_eight_eq
#print axioms N11Formalization.dist_neg_axis_ringCenter_eight_sq_sub
#print axioms N11Formalization.neg_axis_covered_of_residual

end N11Formalization
