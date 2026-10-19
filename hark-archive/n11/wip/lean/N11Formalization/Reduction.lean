import N11Formalization.Definitions

/-!
# n=11 全局最优性 —— 强接口 ↔ `IsLeast` ↔ `sInf` 的等价（GUIDE §2）

GUIDE §2 要求：先证强接口

  `(∃ c, Covers c Rstar) ∧ (∀ r c, 0 ≤ r → Covers c r → Rstar ≤ r)`

再证它与可行半径集合的 `IsLeast` / `sInf = Rstar` 等价；使用 `sInf` 前必须证明集合
非空且下有界。本文件把这层"管道"全部 kernel-proved，且**不含任何未证假设**。

注意：等价是**双向**的，因此两条路线的强度相同，不存在"弱化后偷偷绕开"的余地。
-/

namespace N11Formalization

/-- GUIDE §2 的强接口（达到 + 下界，**同一个** `R`）。 -/
def StrongInterface (R : ℝ) : Prop :=
  (∃ c : Fin 11 → Point, Covers c R) ∧
    (∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → R ≤ r)

theorem StrongInterface.attains {R : ℝ} (h : StrongInterface R) :
    ∃ c : Fin 11 → Point, Covers c R := h.1

theorem StrongInterface.bounds {R : ℝ} (h : StrongInterface R) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → R ≤ r := h.2

theorem StrongInterface.nonneg {R : ℝ} (h : StrongInterface R) : 0 ≤ R :=
  h.1.choose_spec.nonneg

theorem StrongInterface.mem {R : ℝ} (h : StrongInterface R) : R ∈ feasibleRadii :=
  ⟨h.nonneg, h.attains⟩

/-- **主等价**：强接口 ↔ 可行半径集合的最小元。 -/
theorem isLeast_iff_strongInterface (R : ℝ) :
    IsLeast feasibleRadii R ↔ StrongInterface R := by
  constructor
  · intro h
    refine ⟨h.1.2, fun r c hr hc => ?_⟩
    exact h.2 ⟨hr, c, hc⟩
  · intro h
    refine ⟨h.mem, fun r hr => ?_⟩
    exact h.2 r hr.2.choose hr.1 hr.2.choose_spec

/-- `sInf` 推论（只用已证的非空/下有界，不用条件完备格的默认值）。 -/
theorem sInf_feasibleRadii_eq {R : ℝ} (h : IsLeast feasibleRadii R) :
    sInf feasibleRadii = R :=
  h.csInf_eq

/-- 反向：若下确界本身可行（达到），则它就是最小元。 -/
theorem isLeast_sInf_of_mem (hmem : sInf feasibleRadii ∈ feasibleRadii) :
    IsLeast feasibleRadii (sInf feasibleRadii) :=
  ⟨hmem, fun _ hr => csInf_le feasibleRadii_bddBelow hr⟩

theorem strongInterface_of_sInf_mem (hmem : sInf feasibleRadii ∈ feasibleRadii) :
    StrongInterface (sInf feasibleRadii) :=
  (isLeast_iff_strongInterface _).mp (isLeast_sInf_of_mem hmem)

/-- 下确界的一般下界性质（需要非空性；`feasibleRadii_nonempty` 已证）。 -/
theorem le_sInf_feasibleRadii {a : ℝ} (h : ∀ r ∈ feasibleRadii, a ≤ r) :
    a ≤ sInf feasibleRadii :=
  le_csInf feasibleRadii_nonempty h

/-- **"更小半径不可能"的完整形式**：若强接口成立，则任何 `r < R` 都**根本不能**覆盖 `D`
（`r < 0` 或 `r ≥ 0` 都覆盖，无需分情况由使用者处理）。 -/
theorem no_cover_below {R : ℝ} (h : StrongInterface R) {r : ℝ} (hr : r < R) :
    ¬ ∃ c : Fin 11 → Point, Covers c r := by
  rintro ⟨c, hc⟩
  by_cases h0 : 0 ≤ r
  · exact absurd (h.2 r c h0 hc) (not_le.mpr hr)
  · have hr0 : r < 0 := not_le.mp h0
    obtain ⟨i, hi⟩ := hc 0 zero_mem_unitDisk
    exact absurd (le_trans dist_nonneg hi) (not_le.mpr hr0)

/-- 可行半径集合是向上封闭的（区间性）。 -/
theorem feasibleRadii_upward {r r' : ℝ} (hr : r ∈ feasibleRadii) (hrr' : r ≤ r') :
    r' ∈ feasibleRadii :=
  ⟨le_trans hr.1 hrr', ⟨hr.2.choose, hr.2.choose_spec.mono hrr'⟩⟩

/-- 可行集合的下确界在几何上不可能为负。 -/
theorem sInf_feasibleRadii_nonneg : 0 ≤ sInf feasibleRadii :=
  le_csInf feasibleRadii_nonempty fun _ hr => hr.1

end N11Formalization
