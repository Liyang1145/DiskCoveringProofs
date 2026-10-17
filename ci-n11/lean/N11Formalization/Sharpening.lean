import N11Formalization.Attainment
import N11Formalization.Statement

/-!
# 锐化口径与**反漂移**：主命题 ⟺ 两条标量不等式

`Statement.lean` 里的 `N11MainStatement R := IsLeast feasibleRadii R ∧ sInf feasibleRadii = R`
的两个合取项在已证 `非空 + 下有界 + 达到` 的前提下**并不独立**，下游若只读 `.2` 当"达到性"会被误导。
本文件给出锐化等价，并显式标出**空形式**，防止把 `sInf` 形式误当源命题。

（独立复核：`Audit/InterfaceSharpening.lean` 由 stmt-audit 独立转写并 kernel 复证同一锐化。）
-/

namespace N11Formalization

/-- **锐化**：强接口 ⟺ `R` 恰是可行半径集合的下确界。 -/
theorem strongInterface_iff_eq_sInf (R : ℝ) : StrongInterface R ↔ R = sInf feasibleRadii := by
  constructor
  · intro h
    refine le_antisymm ?_ ?_
    · exact le_csInf feasibleRadii_nonempty
        fun b hb => h.bounds b hb.2.choose hb.1 hb.2.choose_spec
    · exact csInf_le feasibleRadii_bddBelow h.mem
  · intro h
    rw [h]
    exact strongInterface_sInf

/-- **锐化**：主命题 ⟺ `R = sInf feasibleRadii`。 -/
theorem n11MainStatement_iff_eq_sInf (R : ℝ) :
    N11MainStatement R ↔ R = sInf feasibleRadii := by
  constructor
  · intro h
    exact (strongInterface_iff_eq_sInf R).mp ((isLeast_iff_strongInterface R).mp h.1)
  · intro h
    rw [h]
    exact ⟨(isLeast_iff_strongInterface _).mpr strongInterface_sInf, rfl⟩

/-- **主命题的承重形式**：两条标量不等式 `sInf ≤ R`（达到侧）与 `R ≤ sInf`（下界侧）。

    这与 `Source-MAP.md` 的账本口径一致：
    * `sInf ≤ Rstar`  ⟸ C892（在 `Rstar` 处的覆盖构型）；
    * `Rstar ≤ sInf`  ⟸ C923 + C921 + C922。
    两侧都必须用**同一个** `Rstar`。 -/
theorem n11MainStatement_iff_two_bounds (R : ℝ) :
    N11MainStatement R ↔ (sInf feasibleRadii ≤ R ∧ R ≤ sInf feasibleRadii) := by
  rw [n11MainStatement_iff_eq_sInf]
  constructor
  · intro h
    subst h
    exact ⟨le_rfl, le_rfl⟩
  · intro h
    exact le_antisymm h.2 h.1

/-- **反漂移警告（重要）**：`N11MainStatement (sInf feasibleRadii)` **无条件为真**，
且其陈述里**不含任何源常数**（既不含 `Rstar` 也不含任何证书数据）。

因此任何形如「`r_D(11) = sInf feasibleRadii`」的表述**不是**源命题，不能充当进度；
源命题必须把 `sInf feasibleRadii` 钉到**同一个 `Rstar`**（见 `n11MainStatement_iff_two_bounds`
的两条不等式，其中右侧常数由 C891 的根规格给出）。 -/
theorem n11MainStatement_at_sInf_is_free : N11MainStatement (sInf feasibleRadii) :=
  ⟨isLeast_sInf_of_mem sInf_mem_feasibleRadii, rfl⟩

/-- 与上式配套：`sInf feasibleRadii = R` 也是无条件的等价形式，同样**不含源常数**。 -/
theorem sInf_feasibleRadii_is_free : StrongInterface (sInf feasibleRadii) :=
  strongInterface_sInf

end N11Formalization
