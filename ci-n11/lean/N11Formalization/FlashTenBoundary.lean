import N11Formalization.Assembly.BoundaryCount

/-!
# C450（十边界盘排除）的数学接口

**本文件是接口件，不是 C450 的证明。** 它做三件事：

1. 把源定理 C450（`research-2026/solo-20260922/M10-038-EXCLUSION.md`：十个触圆盘
   共同覆盖 `∂D` + 一个 hub，十一盘覆盖 `D` ⟹ `r > 19/50`）变成与
   `Assembly/BoundaryCount.lean::card_boundaryIdx_eq_nine_or_ten` **对接的精确类型**；
2. 把其中**可证的几何/组合步骤 kernel 证出**（半径单调性、hub 偏移界 `‖c hub‖ ≤ 7/50`、
   以及"10 个触圆盘 = 唯一非触圆盘之外的全部"这一装配桥）；
3. 把剩下**唯一未付**的数学内容固定成一个 `Prop`（`C450Atom`），并证明**更弱**的
   specialization（`C450AtomOffset`，多一条已被 kernel 证的 `‖c hub‖ ≤ 7/50`）就足够
   —— 即这条共享前提已从原子中**去掉**（`c450_of_c450_offset`）。

## 反漂移口径（与源文逐条对照）

* **半径**：原子只谈 `R = 19/50`。源文先"反设 `r ≤ R`，把全部半径扩大到 `R`"；本文件用
  `Covers.mono`（已在 `Definitions.lean`）与 `MeetsCircle.mono` 把这一步**证掉**，
  故最终定理 `not_card_boundaryIdx_eq_ten` 的前提里**没有** `0 ≤ r`、也**不要求** `r` 严格。
* **十个"边界盘"** 用 `∀ i, i ≠ hub` 的索引形式：允许中心重合/冗余/相切/外根，
  **不需要互异性**前提（源文的容量论证按重数求和不依赖互异）。
* **hub 允许自己触圆**（源文不要求它不触圆）；被用的前提只有"10 个指定盘独自覆盖 `∂D`"。
* 源文的"另一个盘 `B(h,r)`"= 本文件的 `c hub`。

## 已证 vs 未付

| 项 | 状态 |
|---|---|
| `MeetsCircle.mono` | **kernel-proved** |
| `hub_offset_le`：`‖c hub‖ ≤ 7/50`（源文 §1 的几何归约） | **kernel-proved** |
| `C450AtomOffset` / `C450Atom` | **未付**（= 源文 §2–§4：两圆加权容量的解析归约 + 36 段精确有理 dual 的连续算术证书） |
| `c450_of_c450_offset`（前提更弱） | **kernel-proved** |
| `not_card_boundaryIdx_eq_ten` | **kernel-proved**（给定上述未付件） |
| `card_boundaryIdx_eq_nine_of_c450`（消费方形状） | **kernel-proved** |
-/

namespace N11Formalization

section
open Classical

/-- **触圆的半径单调性**：半径放大后仍然触圆。（源文"把全部半径扩大到 R"这一步的一半。） -/
theorem MeetsCircle.mono {c : Fin 11 → Point} {r r' : ℝ} {i : Fin 11}
    (h : MeetsCircle c r i) (hrr' : r ≤ r') : MeetsCircle c r' i := by
  obtain ⟨x, hx, hd⟩ := h
  exact ⟨x, hx, le_trans hd hrr'⟩

/-- **hub 偏移界（源文 §1 的几何归约，kernel-proved）**。

设 `R = 19/50`。若除 `hub` 之外的十个盘都触单位圆、且十一盘覆盖单位闭盘 `D`，
则 hub 中心满足 `‖c hub‖ ≤ 3R - 1 = 7/50`。

证明（源文 §1）：`‖x‖ < 1 - 2R` 的点不被任何触圆盘覆盖（触圆盘中心范数 `≥ 1-R`，
故 `dist x (c i) ≥ (1-R) - ‖x‖ > R`），故必须由 hub 覆盖；取 `x = (1-2R-ε) • (-u)`，
`u = ‖c hub‖⁻¹ • c hub`，得 `‖c hub‖ + (1-2R) - ε ≤ R`，令 `ε → 0`。

**这是从 C450 原子中去掉的一条共享前提。** -/
theorem hub_offset_le {c : Fin 11 → Point} {hub : Fin 11}
    (htouch : ∀ i : Fin 11, i ≠ hub → MeetsCircle c (19 / 50) i)
    (hcov : ∀ x : Point, ‖x‖ ≤ 1 → ∃ i : Fin 11, dist x (c i) ≤ 19 / 50) :
    ‖c hub‖ ≤ 7 / 50 := by
  by_cases h0 : c hub = 0
  · rw [h0, norm_zero]; norm_num
  have hnorm : 0 < ‖c hub‖ := norm_pos_iff.mpr h0
  set u : Point := ‖c hub‖⁻¹ • c hub with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hnorm,
      inv_mul_cancel₀ (ne_of_gt hnorm)]
  have hchub : c hub = ‖c hub‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ (ne_of_gt hnorm), one_smul]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set ε' : ℝ := min ε (3 / 25) with hε'def
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'3 : ε' ≤ 3 / 25 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  -- 测点 x = (6/25 - ε') • (-u)，其中 6/25 = 1 - 2R
  set x : Point := (6 / 25 - ε') • (-u) with hxdef
  have hxnorm : ‖x‖ = 6 / 25 - ε' := by
    rw [hxdef, norm_smul, norm_neg, hu1, mul_one, Real.norm_eq_abs, abs_of_pos]
    linarith
  have hx1 : ‖x‖ ≤ 1 := by rw [hxnorm]; linarith
  obtain ⟨i, hi⟩ := hcov x hx1
  have hidx : i = hub := by
    by_contra hne
    have hR : (1 : ℝ) - 19 / 50 ≤ ‖c i‖ := one_sub_le_norm_of_meetsCircle (htouch i hne)
    have hlow : ‖c i‖ - ‖x‖ ≤ ‖x - c i‖ := by
      calc ‖c i‖ - ‖x‖ ≤ |‖c i‖ - ‖x‖| := le_abs_self _
        _ ≤ ‖c i - x‖ := abs_norm_sub_norm_le (c i) x
        _ = ‖x - c i‖ := norm_sub_rev _ _
    rw [hxnorm] at hlow
    have hdist' : dist x (c i) = ‖x - c i‖ := dist_eq_norm x (c i)
    rw [hdist'] at hi
    linarith
  rw [hidx] at hi
  have hstep : x - c hub = -((6 / 25 - ε' + ‖c hub‖) • u) := by
    conv_lhs => rw [hxdef, hchub]
    rw [smul_neg, sub_eq_add_neg, ← neg_add, ← add_smul]
  have hdist : dist x (c hub) = ‖c hub‖ + (6 / 25 - ε') := by
    rw [dist_eq_norm, hstep, norm_neg, norm_smul, hu1, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    ring
  rw [hdist] at hi
  linarith

/-! ## 未付原子（精确类型）

源文 C450 的量词域，逐条对照：

* `c : Fin 11 → Point`：**任意** 11 个中心（可重合、可在盘外、无对称/接触图/一般位置假设）；
* `hub`：源文"另一个盘 `B(h,r)`"的下标；其余 10 个是"指定的十个边界盘"；
* 第一条假设 = 十一盘覆盖单位闭盘 `D`（源前提"若所有十一盘覆盖D"）；
* 第二条假设 = 十个指定盘**均接触** `∂D`（源"均接触"）；
* 第三条假设 = 十个指定盘**共同覆盖** `∂D`（源"共同覆盖∂D"，即 hub 不参与）；
* 结论 `False` = 与"半径 `≤ 19/50`"矛盾（源文结论 `r > 19/50`）。

**注意半径位置**：原子只在 `R = 19/50` 处陈述。源文"反设 `r ≤ R` 后把半径扩大到 `R`"这一步
已由 `Covers.mono` + `MeetsCircle.mono` 在 `not_card_boundaryIdx_eq_ten` 里证掉，
故原子**不**需要对所有 `r ≤ R` 的量化，也**不**需要 `0 ≤ r`。 -/
def C450Atom : Prop :=
  ∀ (c : Fin 11 → Point) (hub : Fin 11),
    (∀ x : Point, ‖x‖ ≤ 1 → ∃ i : Fin 11, dist x (c i) ≤ 19 / 50) →
    (∀ i : Fin 11, i ≠ hub → MeetsCircle c (19 / 50) i) →
    (∀ x : Point, ‖x‖ = 1 → ∃ i : Fin 11, i ≠ hub ∧ dist x (c i) ≤ 19 / 50) →
    False

/-- **更弱的 specialization**：多一条已被 kernel 证的 `‖c hub‖ ≤ 7/50`（`hub_offset_le`）。

源文 §1 先用几何归约得到这条偏移界，再对 `e ∈ [0,7/50]` 做有限连续证书。
本定义把该归约**从原子中剥离**：未付的只剩 §2–§4（两圆加权容量的解析归约 +
36 段精确有理 dual 的连续算术证书）。 -/
def C450AtomOffset : Prop :=
  ∀ (c : Fin 11 → Point) (hub : Fin 11),
    ‖c hub‖ ≤ 7 / 50 →
    (∀ x : Point, ‖x‖ ≤ 1 → ∃ i : Fin 11, dist x (c i) ≤ 19 / 50) →
    (∀ i : Fin 11, i ≠ hub → MeetsCircle c (19 / 50) i) →
    (∀ x : Point, ‖x‖ = 1 → ∃ i : Fin 11, i ≠ hub ∧ dist x (c i) ≤ 19 / 50) →
    False

/-- **前提消去**：`C450Atom` 只需 `C450AtomOffset`（偏移界由 `hub_offset_le` 供给）。 -/
theorem c450_of_c450_offset (h : C450AtomOffset) : C450Atom := by
  intro c hub hcov htouch harc
  exact h c hub (hub_offset_le htouch hcov) hcov htouch harc

/-! ## 装配桥（与 `BoundaryCount` 对接，全部 kernel-proved） -/

/-- **10 个触圆盘排除**：给定 C450 原子，任意覆盖 `D` 的 11 等半径盘在 `r ≤ 19/50` 处
不可能恰有 10 个触圆盘。

注意前提里**没有** `0 ≤ r`（`r ≥ 0` 由 `Covers.nonneg` 自动），也**不要求** `r < 19/50` 严格，
也**不要求**中心互异或任何对称性：这正是"任意 10 边界 cover"的桥。

证明路线：`card = 10` ⟹ 恰有一个盘不触圆（其余 10 个都触圆）；不触圆的盘覆盖不了 `∂D`
的任何点 ⟹ 那 10 个触圆盘独自覆盖 `∂D`；再把全部半径由 `r` 单调放大到 `19/50`，
把 C450 原子用在 `c` 与 `hub := 那个不触圆的下标` 上。 -/
theorem not_card_boundaryIdx_eq_ten (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr : r ≤ 19 / 50) (hc : Covers c r) : Fintype.card (BoundaryIdx c r) ≠ 10 := by
  intro hcard
  -- 把 subtype 基数换成 `Finset.filter` 基数（古典可判定）
  have hf : (Finset.univ.filter (fun i : Fin 11 => MeetsCircle c r i)).card = 10 := by
    rw [← Fintype.card_subtype]
    exact hcard
  have hnot : (Finset.univ.filter (fun i : Fin 11 => ¬ MeetsCircle c r i)).card = 1 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 11))) (fun i : Fin 11 => MeetsCircle c r i)
    rw [hf, Finset.card_univ, Fintype.card_fin] at h
    omega
  obtain ⟨hub, hhub⟩ := Finset.card_eq_one.mp hnot
  have hhubmem : hub ∈ Finset.univ.filter (fun i : Fin 11 => ¬ MeetsCircle c r i) := by
    rw [hhub]; simp
  have hhub_not : ¬ MeetsCircle c r hub := by simpa using hhubmem
  -- 其余 10 个都触圆
  have hother : ∀ i : Fin 11, i ≠ hub → MeetsCircle c r i := by
    intro i hi
    by_contra hni
    have hmem : i ∈ Finset.univ.filter (fun j : Fin 11 => ¬ MeetsCircle c r j) := by
      simp [hni]
    rw [hhub] at hmem
    simp at hmem
    exact hi hmem
  refine h450 c hub ?_ ?_ ?_
  · -- 十一盘覆盖 D（半径放大到 19/50）
    intro x hx
    obtain ⟨i, hi⟩ := hc x hx
    exact ⟨i, le_trans hi hr⟩
  · -- 十个指定盘均触圆
    intro i hi
    exact MeetsCircle.mono (hother i hi) hr
  · -- 十个指定盘共同覆盖 ∂D（不触圆的盘不覆盖 ∂D 的任何点）
    intro x hx
    obtain ⟨i, hi⟩ := hc x (le_of_eq hx)
    have hm : MeetsCircle c r i := ⟨x, hx, hi⟩
    have hne : i ≠ hub := fun h => hhub_not (h ▸ hm)
    exact ⟨i, hne, le_trans hi hr⟩

/-- **消费方形状**：给定 C450 原子，`BoundaryCount` 的 9-or-10 夹逼升级为**恰 9**。
这是九环（arc-to-fan / 9+2）分支的入口类型。 -/
theorem card_boundaryIdx_eq_nine_of_c450 (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 19 / 50) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) = 9 := by
  rcases card_boundaryIdx_eq_nine_or_ten hr0 hr hc with h | h
  · exact h
  · exact absurd h (not_card_boundaryIdx_eq_ten h450 hr.le hc)

end
end N11Formalization
