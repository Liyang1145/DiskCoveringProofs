import N11Formalization.Reduction

/-!
# 达到性：中心可局部化；`sInf` 无条件被达到（GUIDE §4.7 的 min/inf 义务）

GUIDE §4.7 要求在使用 `sInf`/"取最优解"之前付清 min/inf 义务。本文件给出**无条件**答案：

1. `Covers.localize`：覆盖的**中心可整体搬进紧集** `B(0, 1+r)` —— 去掉"中心无界"这一构型类。
2. `exists_minimizing_sequence` / `exists_covers_sInf`：极小化序列的中心在紧集中取子列
   ⇒ **下确界被达到**。
3. `sInf_mem_feasibleRadii` / `strongInterface_sInf` / `feasibleRadii_eq_Ici` / `feasibleRadii_closed`。

**结构收益（已按 stmt-audit 的对抗审计更正，勿再夸大）**：
GUIDE 账本中「存在**某个**达到构型」这一义务整体由**紧致性一般定理**替代 —— 即
`∃ c, Covers c (sInf feasibleRadii)` 无条件成立。但**这不等于** C892 被替代：
源命题要求 `Rstar = sInf feasibleRadii`（同一个 `Rstar`），而 `sInf ≤ Rstar` 恰恰需要一个
**在 `Rstar` 处的**覆盖构型；被替代的只是"存在某个最优构型"，"最优值是多少"仍需 C923+C921+C922。

**真实等级**：本文件全部 `kernel-proved`，无条件，零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Filter Topology

/-- **中心局部化**：若 `c` 以半径 `r` 覆盖 `D`，则存在中心全在闭球 `B(0, 1+r)` 内的等价覆盖。

做法：盘 `B(c i, r)` 若与 `D` 相交，则 `‖c i‖ ≤ 1 + r`（三角不等式）；
若不相交，则它在 `D` 上不起作用，直接换成原点。中心在 `D` 外且半径很大的病态情形由此消失。 -/
theorem Covers.localize {c : Fin 11 → Point} {r : ℝ} (h : Covers c r) :
    ∃ c' : Fin 11 → Point, (∀ i, ‖c' i‖ ≤ 1 + r) ∧ Covers c' r := by
  classical
  have hr : 0 ≤ r := h.nonneg
  have key : ∀ i : Fin 11, ∃ y : Point, ‖y‖ ≤ 1 + r ∧
      ∀ x : Point, x ∈ unitDisk → dist x (c i) ≤ r → dist x y ≤ r := by
    intro i
    by_cases hi : ∃ x : Point, x ∈ unitDisk ∧ dist x (c i) ≤ r
    · obtain ⟨x, hx, hd⟩ := hi
      refine ⟨c i, ?_, fun x' hx' hd' => hd'⟩
      have hxn : ‖x‖ ≤ 1 := mem_unitDisk.mp hx
      have hd' : ‖x - c i‖ ≤ r := by simpa [dist_eq_norm] using hd
      have heq : x + (c i - x) = c i := by abel
      calc ‖c i‖ = ‖x + (c i - x)‖ := by rw [heq]
        _ ≤ ‖x‖ + ‖c i - x‖ := norm_add_le _ _
        _ = ‖x‖ + ‖x - c i‖ := by rw [norm_sub_rev]
        _ ≤ 1 + r := by linarith
    · refine ⟨0, by simp only [norm_zero]; linarith, fun x' hx' hd' => absurd ⟨x', hx', hd'⟩ hi⟩
  choose c' hc' using key
  exact ⟨c', fun i => (hc' i).1, fun x hx => let ⟨i, hi⟩ := h x hx; ⟨i, (hc' i).2 x hx hi⟩⟩

/-- **极小化序列**：存在 `r n ∈ feasibleRadii` 满足 `r n < sInf + 1/(n+1)`，且 `r n → sInf`。 -/
theorem exists_minimizing_sequence :
    ∃ r : ℕ → ℝ, (∀ n, r n ∈ feasibleRadii) ∧
      (∀ n, r n < sInf feasibleRadii + 1 / ((n : ℝ) + 1)) ∧
      Tendsto r atTop (𝓝 (sInf feasibleRadii)) := by
  classical
  have hε : ∀ n : ℕ, ∃ r ∈ feasibleRadii, r < sInf feasibleRadii + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine (csInf_lt_iff feasibleRadii_bddBelow feasibleRadii_nonempty).mp ?_
    linarith
  choose r hr_mem hr_lt using hε
  have hr_ge : ∀ n, sInf feasibleRadii ≤ r n := fun n =>
    csInf_le feasibleRadii_bddBelow (hr_mem n)
  have hT : Tendsto (fun n : ℕ => sInf feasibleRadii + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 (sInf feasibleRadii)) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := sInf feasibleRadii)).add h0
  exact ⟨r, hr_mem, hr_lt,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT hr_ge
      (fun n => le_of_lt (hr_lt n))⟩

/-- **下确界被达到**：存在 11 个半径 `sInf feasibleRadii` 的闭盘覆盖 `D`。

证明：沿极小化序列用 `Covers.localize` 把中心压进紧球 `B(0, sInf+2)`，取收敛子列，
再用「有限个 `i` 的 eventually 交集」把子列的覆盖见证常数化（避免二次子列抽取）。 -/
theorem exists_covers_sInf : ∃ c : Fin 11 → Point, Covers c (sInf feasibleRadii) := by
  classical
  obtain ⟨r, hr_mem, hr_lt, hr_tend⟩ := exists_minimizing_sequence
  have hr_le : ∀ n, r n < sInf feasibleRadii + 1 := by
    intro n
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith [hr_lt n]
  -- 把中心压进紧球
  have hcl : ∀ n : ℕ, ∃ c : Fin 11 → Point,
      (∀ i, c i ∈ Metric.closedBall (0 : Point) (sInf feasibleRadii + 2)) ∧ Covers c (r n) := by
    intro n
    obtain ⟨c, hb, hc⟩ := (hr_mem n).2.choose_spec.localize
    refine ⟨c, fun i => ?_, hc⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have := hb i
    linarith [hr_le n]
  choose c hcK hccov using hcl
  -- 紧致性 + 子列
  have hK : IsCompact (Metric.closedBall (0 : Point) (sInf feasibleRadii + 2)) :=
    isCompact_closedBall _ _
  have hpi : IsCompact (Set.univ.pi fun _ : Fin 11 =>
      Metric.closedBall (0 : Point) (sInf feasibleRadii + 2)) :=
    isCompact_univ_pi fun _ => hK
  have hmem : ∀ n, c n ∈ Set.univ.pi (fun _ : Fin 11 =>
      Metric.closedBall (0 : Point) (sInf feasibleRadii + 2)) :=
    fun n => Set.mem_univ_pi.mpr (hcK n)
  obtain ⟨cstar, -, φ, hφ_mono, hφ_tend⟩ := IsCompact.tendsto_subseq hpi hmem
  have hrφ : Tendsto (fun k => r (φ k)) atTop (𝓝 (sInf feasibleRadii)) :=
    hr_tend.comp hφ_mono.tendsto_atTop
  refine ⟨cstar, fun x hx => ?_⟩
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  -- 每个 i 上，最终 r(φ k) < dist x (c(φ k) i)；有限交 + 覆盖见证 ⇒ 矛盾
  have hev1 : ∀ᶠ k in atTop, ∀ i : Fin 11, r (φ k) < dist x ((c ∘ φ) k i) := by
    rw [eventually_all]
    intro i
    have h1 : Tendsto (fun k => ((c ∘ φ) k) i) atTop (𝓝 (cstar i)) :=
      (tendsto_pi_nhds.mp hφ_tend) i
    have h2 : Tendsto (fun k => dist x (((c ∘ φ) k) i)) atTop (𝓝 (dist x (cstar i))) :=
      (tendsto_const_nhds (x := x)).dist h1
    exact hrφ.eventually_lt h2 (hcon i)
  have hev2 : ∀ᶠ k in atTop, ∃ i : Fin 11, dist x ((c ∘ φ) k i) ≤ r (φ k) :=
    Filter.Eventually.of_forall fun k => hccov (φ k) x hx
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  obtain ⟨i, hi⟩ := hk2
  exact absurd hi (not_le.mpr (hk1 i))

/-- **`sInf` 属于可行集合**（下确界被达到的等价形式）。 -/
theorem sInf_mem_feasibleRadii : sInf feasibleRadii ∈ feasibleRadii :=
  ⟨sInf_feasibleRadii_nonneg, exists_covers_sInf⟩

/-- **无条件强接口**：`sInf feasibleRadii` 给出达到 + 下界，两侧同一个值。 -/
theorem strongInterface_sInf : StrongInterface (sInf feasibleRadii) :=
  strongInterface_of_sInf_mem sInf_mem_feasibleRadii

/-- **可行集合恰是闭半直线** `[sInf, ∞)`（区间性 + 达到性）。 -/
theorem feasibleRadii_eq_Ici : feasibleRadii = Set.Ici (sInf feasibleRadii) := by
  ext r
  constructor
  · intro hr
    exact csInf_le feasibleRadii_bddBelow hr
  · intro hr
    exact feasibleRadii_upward sInf_mem_feasibleRadii hr

/-- **可行集合闭**。 -/
theorem feasibleRadii_closed : IsClosed feasibleRadii := by
  rw [feasibleRadii_eq_Ici]
  exact isClosed_Ici

/-- 交叉读数：闭性 + `IsClosed.csInf_mem` 给出同一结论（作为独立表述的一致性检查）。 -/
theorem sInf_mem_feasibleRadii' : sInf feasibleRadii ∈ feasibleRadii :=
  feasibleRadii_closed.csInf_mem feasibleRadii_nonempty feasibleRadii_bddBelow

end N11Formalization
