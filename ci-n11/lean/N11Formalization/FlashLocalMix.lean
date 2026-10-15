import Mathlib
import N11Formalization.FlashLocalChart

/-!
# FlashLocal — 120 局部叶承重链 · 第二环：**PSD 交叉界** + 二次展开 + 叶级消费者

对应源 `team-current/lead/ADAPTIVE-STRESS-FINITE-REMAINDER.md` 第 31–34 行：

```
31. Quadratic term:
32. <delta,Lambda_alpha delta> >= <delta,Lambda0 delta> - bq<delta,Lambda0 delta>
33. >= <v,Lambda0 v> - d q^3 - bd q^3.
34. The first loss uses cross term 2<v,Lambda0 w> and discards nonnegative <w,Lambda0 w>;
    the second uses Lambda0 <= dI and ||delta|| <= q.
```

本件付清其中**唯一一条纯算子论引理**：`Lambda0 <= d I` 与半正定 ⇒
`|⟨v, Lambda0 w⟩| <= d ||v|| ||w||`（mathlib **没有**现成半正定 Cauchy–Schwarz）。
再合成第 33 行的 `-d q^3`（**注意** `q^3` 由 `2·d·||v||·||w||` 与 `||v||=q, ||w||<=q^2/2` 联合给出，
**不是** `q^2` 的推论；`||w||` 由第一环 `FlashLocalChart.anchorRemainder_frob_le` 供给）。

## 载体口径（**重要更正**，Lead 2026-09-30 指出）

`Fin 9 → Point` 的**默认 Pi 范数是 sup 范数，不是 Frobenius 内积**，故
**不得**直接把它当内积空间实例化。正确的 Frobenius 载体是
`PiLp 2 (fun _ : Fin 9 => Point)`（= `WithLp 2 (Fin 9 → Point)`）；
`PiLp.norm_sq_eq_of_L2` 给出 `‖x‖^2 = ∑ i, ‖x i‖^2`，即**明文 isometry 等式**
`anchorFrobCarrier`（见 §3）。本件的主定理对任意实内积空间 `F` 陈述，
**实例化时必须取 `F := PiLp 2 (fun _ : Fin 9 => Point)`**，不得取 `Fin 9 → Point`。

**scope**：主定理对任意实内积空间成立（无条件）；`hub`（= `T ≤ d·1` 的二次型口径）是
**具名前件**（Lead 已付 Λ 比较与 `≤ dI`），不是结论。不含 `H0` 语义、不含 45/51 图数据。
-/

namespace N11Formalization.FlashLocal

noncomputable section

/-! ## 0. API 探针（打印到日志作证据） -/

#check @ContinuousLinearMap.IsPositive
#check @ContinuousLinearMap.IsPositive.inner_nonneg_left
#check @ContinuousLinearMap.IsPositive.isSymmetric
#check @discrim_le_zero
#check @discrim
#check @real_inner_comm
#check @inner_self_eq_norm_sq
#check @PiLp.norm_sq_eq_of_L2

/-! ## 1. 实标量内积线性（消 `conj`，供展开用） -/

theorem realInner_smul_left' {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (t : ℝ) (x y : F) : inner ℝ (t • x) y = t * inner ℝ x y := by
  rw [inner_smul_left]
  simp

theorem realInner_smul_right' {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (t : ℝ) (x y : F) : inner ℝ x (t • y) = t * inner ℝ x y := by
  rw [inner_smul_right]

/-! ## 2. 主定理：半正定 + `≤ d·1` ⇒ 交叉界 -/

/-- **PSD 交叉界**（源 L33 的 `-d q^3` 的唯一来源）。

`T` 对称半正定（mathlib `T.IsPositive`）、`T ≤ d·1`（二次型口径 `hub`）⇒
`|⟨v, T w⟩| ≤ d‖v‖‖w‖`。证明 = 半正定形式在 `v + t w` 上的非负性（判别式）
+ `⟨Tv,v⟩ ≤ d‖v‖²`、`⟨Tw,w⟩ ≤ d‖w‖²`；**不用**任何正定性/可逆性/特征值/有限维。 -/
theorem abs_inner_apply_le_of_psd_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : F →L[ℝ] F) (d : ℝ) (hd : 0 ≤ d) (hT : T.IsPositive)
    (hub : ∀ v : F, inner ℝ (T v) v ≤ d * ‖v‖ ^ 2) (v w : F) :
    |inner ℝ v (T w)| ≤ d * ‖v‖ * ‖w‖ := by
  have hsym : ∀ x y : F, inner ℝ (T x) y = inner ℝ x (T y) := fun x y => hT.isSymmetric x y
  have hswap : ∀ x y : F, inner ℝ (T y) x = inner ℝ (T x) y := by
    intro x y
    rw [← real_inner_comm (T y) x, ← hsym x y]
  set A : ℝ := inner ℝ (T v) v with hAset
  set B : ℝ := inner ℝ (T v) w with hBset
  set C : ℝ := inner ℝ (T w) w with hCset
  have hA0 : 0 ≤ A := by rw [hAset]; exact hT.inner_nonneg_left v
  have hC0 : 0 ≤ C := by rw [hCset]; exact hT.inner_nonneg_left w
  have hAle : A ≤ d * ‖v‖ ^ 2 := by rw [hAset]; exact hub v
  have hCle : C ≤ d * ‖w‖ ^ 2 := by rw [hCset]; exact hub w
  have hexp : ∀ t : ℝ, inner ℝ (T (v + t • w)) (v + t • w) = A + 2 * t * B + t ^ 2 * C := by
    intro t
    simp only [hAset, hBset, hCset, map_add, map_smul, inner_add_left, inner_add_right,
      realInner_smul_left', realInner_smul_right', hswap v w]
    ring
  have hquad : ∀ t : ℝ, 0 ≤ C * (t * t) + (2 * B) * t + A := by
    intro t
    have h := hT.inner_nonneg_left (v + t • w)
    rw [hexp t] at h
    nlinarith [h]
  have hdisc : discrim C (2 * B) A ≤ 0 := discrim_le_zero hquad
  have hBC : B ^ 2 ≤ A * C := by
    have h := hdisc
    rw [show discrim C (2 * B) A = (2 * B) ^ 2 - 4 * C * A from by
      simp only [discrim]] at h
    nlinarith [h]
  have hprod : A * C ≤ (d * ‖v‖ ^ 2) * (d * ‖w‖ ^ 2) :=
    mul_le_mul hAle hCle hC0 (by positivity)
  have hsq : B ^ 2 ≤ (d * ‖v‖ * ‖w‖) ^ 2 := by nlinarith [hBC, hprod]
  have hvB : inner ℝ v (T w) = B := ((hsym v w).symm).trans hBset.symm
  calc |inner ℝ v (T w)| = |B| := by rw [hvB]
    _ ≤ d * ‖v‖ * ‖w‖ := abs_le_of_sq_le_sq hsq (by positivity)

/-- **Loewner 形态**（源 "`Lambda0 <= d I`" 的字面写法）：`T ≤ d • 1` ⇒ 同一交叉界。 -/
theorem cross_bound_of_loewner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : F →L[ℝ] F) (d : ℝ) (hd : 0 ≤ d) (hT : T.IsPositive)
    (hle : T ≤ d • (1 : F →L[ℝ] F)) (v w : F) :
    |inner ℝ v (T w)| ≤ d * ‖v‖ * ‖w‖ := by
  refine abs_inner_apply_le_of_psd_le T d hd hT (fun x => ?_) v w
  have hpos : (d • (1 : F →L[ℝ] F) - T).IsPositive :=
    (ContinuousLinearMap.le_def T (d • (1 : F →L[ℝ] F))).mp hle
  have hx : 0 ≤ inner ℝ ((d • (1 : F →L[ℝ] F) - T) x) x := hpos.inner_nonneg_left x
  have hval : inner ℝ ((d • (1 : F →L[ℝ] F) - T) x) x = d * ‖x‖ ^ 2 - inner ℝ (T x) x := by
    simp [inner_sub_left, realInner_smul_left']
  rw [hval] at hx
  linarith

/-! ## 3. 二次展开（源 L31–34 那一行） -/

/-- **二次项展开下界**（源 L33）：`‖v‖ = q`、`‖w‖ ≤ q^2/2`、`Λ0 ≤ d·1`、`Λ0` 半正定 ⇒
`⟨v,Λ0 v⟩ - d q^3 ≤ ⟨v+w, Λ0 (v+w)⟩`。
证明：展开 `= ⟨v,Tv⟩ + 2⟨v,Tw⟩ + ⟨w,Tw⟩`，丢非负 `⟨w,Tw⟩`，再用第 2 节交叉界。
`q^3` 由 `2·d·‖v‖·‖w‖` 与 `‖w‖ ≤ q^2/2` 联合给出（`‖w‖` 由第一环供给）。 -/
theorem quadratic_expansion_lower {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : F →L[ℝ] F) (d q : ℝ) (hd : 0 ≤ d) (hq : 0 ≤ q) (hT : T.IsPositive)
    (hub : ∀ v : F, inner ℝ (T v) v ≤ d * ‖v‖ ^ 2)
    (v w : F) (hv : ‖v‖ = q) (hw : ‖w‖ ≤ q ^ 2 / 2) :
    inner ℝ v (T v) - d * q ^ 3 ≤ inner ℝ (v + w) (T (v + w)) := by
  have hsym : ∀ x y : F, inner ℝ (T x) y = inner ℝ x (T y) := fun x y => hT.isSymmetric x y
  have hswap : ∀ x y : F, inner ℝ (T y) x = inner ℝ (T x) y := by
    intro x y
    rw [← real_inner_comm (T y) x, ← hsym x y]
  have hexp : inner ℝ (T (v + w)) (v + w)
      = inner ℝ (T v) v + 2 * inner ℝ (T v) w + inner ℝ (T w) w := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right]
    rw [hswap v w]
    ring
  have hC : 0 ≤ inner ℝ (T w) w := hT.inner_nonneg_left w
  have hb := abs_inner_apply_le_of_psd_le T d hd hT hub v w
  have hbq : |inner ℝ (T v) w| ≤ d * q ^ 3 / 2 := by
    rw [← hsym v w, hv] at hb
    have hmul : d * q * ‖w‖ ≤ d * q * (q ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have he : d * q * (q ^ 2 / 2) = d * q ^ 3 / 2 := by ring
    linarith
  have hneg : -(inner ℝ (T v) w) ≤ |inner ℝ (T v) w| := neg_le_abs _
  have hlow : -(d * q ^ 3) ≤ 2 * inner ℝ (T v) w := by nlinarith [hneg, hbq]
  have : -(d * q ^ 3) ≤ 2 * inner ℝ (T v) w + inner ℝ (T w) w := by linarith
  rw [← real_inner_comm v (T v), real_inner_comm (T (v + w)) (v + w), hexp]
  linarith

/-- Loewner 版本的二次展开。 -/
theorem quadratic_expansion_lower_of_loewner {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (T : F →L[ℝ] F) (d q : ℝ) (hd : 0 ≤ d) (hq : 0 ≤ q) (hT : T.IsPositive)
    (hle : T ≤ d • (1 : F →L[ℝ] F))
    (v w : F) (hv : ‖v‖ = q) (hw : ‖w‖ ≤ q ^ 2 / 2) :
    inner ℝ v (T v) - d * q ^ 3 ≤ inner ℝ (v + w) (T (v + w)) := by
  refine quadratic_expansion_lower T d q hd hq hT (fun x => ?_) v w hv hw
  have hpos : (d • (1 : F →L[ℝ] F) - T).IsPositive :=
    (ContinuousLinearMap.le_def T (d • (1 : F →L[ℝ] F))).mp hle
  have hx : 0 ≤ inner ℝ ((d • (1 : F →L[ℝ] F) - T) x) x := hpos.inner_nonneg_left x
  have hval : inner ℝ ((d • (1 : F →L[ℝ] F) - T) x) x = d * ‖x‖ ^ 2 - inner ℝ (T x) x := by
    simp [inner_sub_left, realInner_smul_left']
  rw [hval] at hx
  linarith

/-! ## 4. Frobenius 载体（**明文 isometry**，纠正 Pi sup 范数）

`Fin 9 → Point` 的默认范数是 sup；第一环的 Frobenius 量 `∑ i, ‖w i‖^2` 属于
`PiLp 2 (fun _ : Fin 9 => Point)`。`anchorFrobCarrier` 给出两者的**范数等式**。 -/

/-- 9 锚族的 Frobenius 载体：`PiLp 2` 的范数平方 = 逐锚平方和。 -/
theorem piLpTwo_norm_sq {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] (x : PiLp 2 β) :
    ‖x‖ ^ 2 = ∑ i, ‖x.ofLp i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 β x

/-- **chart Frobenius → `PiLp 2` 的 isometry 等式**（本件对 Lead 口径更正的核心一句）。 -/
theorem anchorFrobCarrier (w : Fin 9 → Point) :
    ‖((WithLp.equiv 2 (Fin 9 → Point)).symm) w‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 := by
  rw [piLpTwo_norm_sq]
  rfl

/-! ## 5. 叶级消费者：`V2 >= R^2 + q^2/100000`（源 120 局部叶的目标形状）

`V2 : (Fin 9 → Point) → ℝ` —— **Point 值**的 oracle（不是 `Fin 9 → ℝ`）。
前件 `hEV` = 弱对偶 `E <= V2`（由根内 `dirichlet_le_oracle` / `cosine_energy_le_oracle` 实例化）；
`hE` = 能量沿图的二次增长（下一件付清）。结论不假设自身。 -/

theorem localLeaf_lower_bound {V2 E : (Fin 9 → Point) → ℝ} {R mu c rho : ℝ} {θ : Fin 9 → ℝ}
    (hrho : 0 ≤ rho) (hc0 : 0 ≤ c)
    (hEV : ∀ x : Fin 9 → ℝ, E (fun i => circleMap (θ i + x i))
        ≤ V2 (fun i => circleMap (θ i + x i)))
    (hE : ∀ x : Fin 9 → ℝ, (∑ i, x i ^ 2) ≤ rho ^ 2 →
        R ^ 2 + (mu / 2 - c * Real.sqrt (∑ i, x i ^ 2)) * (∑ i, x i ^ 2)
          ≤ E (fun i => circleMap (θ i + x i)))
    (hc : c * rho ≤ mu / 4) :
    ∀ x : Fin 9 → ℝ, (∑ i, x i ^ 2) ≤ rho ^ 2 →
      R ^ 2 + (mu / 4) * (∑ i, x i ^ 2) ≤ V2 (fun i => circleMap (θ i + x i)) := by
  intro x hx
  have hsnn : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hrs : Real.sqrt (∑ i, x i ^ 2) ≤ rho := by
    calc Real.sqrt (∑ i, x i ^ 2) ≤ Real.sqrt (rho ^ 2) := Real.sqrt_le_sqrt hx
      _ = |rho| := Real.sqrt_sq_eq_abs _
      _ = rho := abs_of_nonneg hrho
  have hcr : c * Real.sqrt (∑ i, x i ^ 2) ≤ mu / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hrs hc0) hc
  have hquad : (mu / 4) * (∑ i, x i ^ 2)
      ≤ (mu / 2 - c * Real.sqrt (∑ i, x i ^ 2)) * (∑ i, x i ^ 2) := by
    nlinarith [hcr, hsnn]
  calc R ^ 2 + (mu / 4) * (∑ i, x i ^ 2)
      ≤ R ^ 2 + (mu / 2 - c * Real.sqrt (∑ i, x i ^ 2)) * (∑ i, x i ^ 2) := by linarith
    _ ≤ E (fun i => circleMap (θ i + x i)) := hE x hx
    _ ≤ V2 (fun i => circleMap (θ i + x i)) := hEV x

/-- **数值实例（源常数 `mu = 1/600`）**：`mu/4 = 1/2400 > 1/100000` ⇒
结论恰好是 `V2 >= R^2 + ||x||^2/100000`（`ResumeGlobalLeafSem.hL` 的槽位形状）。 -/
theorem localLeaf_hundred_thousandth {V2 E : (Fin 9 → Point) → ℝ} {R c rho : ℝ}
    {θ : Fin 9 → ℝ}
    (hrho : 0 ≤ rho) (hc0 : 0 ≤ c)
    (hEV : ∀ x : Fin 9 → ℝ, E (fun i => circleMap (θ i + x i))
        ≤ V2 (fun i => circleMap (θ i + x i)))
    (hE : ∀ x : Fin 9 → ℝ, (∑ i, x i ^ 2) ≤ rho ^ 2 →
        R ^ 2 + ((1 : ℝ) / 600 / 2 - c * Real.sqrt (∑ i, x i ^ 2)) * (∑ i, x i ^ 2)
          ≤ E (fun i => circleMap (θ i + x i)))
    (hc : c * rho ≤ (1 : ℝ) / 600 / 4) :
    ∀ x : Fin 9 → ℝ, (∑ i, x i ^ 2) ≤ rho ^ 2 →
      R ^ 2 + (∑ i, x i ^ 2) / 100000 ≤ V2 (fun i => circleMap (θ i + x i)) := by
  intro x hx
  have hsnn : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hgen := localLeaf_lower_bound (V2 := V2) (E := E) (R := R) (mu := 1 / 600)
    (c := c) (rho := rho) (θ := θ) hrho hc0 hEV hE hc x hx
  have hsplit : (1 : ℝ) / 600 / 4 = 1 / 2400 := by norm_num
  rw [hsplit] at hgen
  have : (∑ i, x i ^ 2) / 100000 ≤ (1 / 2400 : ℝ) * (∑ i, x i ^ 2) := by nlinarith [hsnn]
  linarith

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.abs_inner_apply_le_of_psd_le
#print axioms N11Formalization.FlashLocal.cross_bound_of_loewner
#print axioms N11Formalization.FlashLocal.quadratic_expansion_lower
#print axioms N11Formalization.FlashLocal.quadratic_expansion_lower_of_loewner
#print axioms N11Formalization.FlashLocal.anchorFrobCarrier
#print axioms N11Formalization.FlashLocal.localLeaf_lower_bound
#print axioms N11Formalization.FlashLocal.localLeaf_hundred_thousandth
