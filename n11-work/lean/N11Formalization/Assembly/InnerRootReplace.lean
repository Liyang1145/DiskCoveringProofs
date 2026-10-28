import N11Formalization.Assembly.BoundaryCount
import N11Formalization.Geometry

/-!
# 装配：内根替换保覆盖（UNRESTRICTED-PROOF-ASSEMBLY §1）

源文 §1：

> For each boundary disk replace its outer radial root by the inner root of the SAME actual arc
> and SAME r. … Thus coverage and actual arcs are preserved.

本文件把 cap-arc 的 `Geometry/DiskToArc.innerRoot_replacement_of_disk` 接到本团队的 `Covers` 口径，
使内根替换成为**承重装配步**（不只是单点几何引理）。

**精确前提**（不凑）：
* `0 < r < 1`（半径合法）；
* 被替换的盘其中心在**外径向根**上：`‖c i‖ = outerRoot (capHalfWidth (c i) r) r`。
  这是源文"outer radial root"的字面内容；若某盘中心已在内根上，则它已经是内根盘、无需替换
  （本文件让调用方用 `hkeep` 保持其不变）。
* 被替换的盘必须**触圆**（`MeetsCircle`）：否则 `capHalfWidth` 不再描述该盘在 S¹ 上的弧
  （cap 为空时 `θ = 0`、外根盘与 S¹ 外切，两者 cap 不同）。

**真实等级**：kernel-proved，无条件（除上述显式前提）。
-/

namespace N11Formalization

/-- **单盘内根替换**：若盘心在**外径向根**上，则把盘心移到同弧同 `r` 的**内径向根**上
不缩小该盘在 `D` 上的覆盖。 -/
theorem dist_innerRoot_le_of_dist_le {c x : Point} {r : ℝ}
    (hc : c ≠ 0) (hr0 : 0 < r) (hr1 : r < 1)
    (houter : ‖c‖ = outerRoot (capHalfWidth c r) r)
    (hmeet : ∃ y : Point, ‖y‖ = 1 ∧ dist y c ≤ r)
    (hx : ‖x‖ ≤ 1) (h : dist x c ≤ r) :
    dist x (innerRoot (capHalfWidth c r) r • centerDir c) ≤ r := by
  have heq : c = outerRoot (capHalfWidth c r) r • centerDir c :=
    calc c = ‖c‖ • centerDir c := self_eq_norm_smul_centerDir hc
      _ = outerRoot (capHalfWidth c r) r • centerDir c := by rw [houter]
  rw [heq] at h
  exact innerRoot_replacement_of_disk hc hr0 hr1 hmeet hx h

/-- **覆盖级内根替换**：把每个触圆盘（盘心在外径向根上）换成同弧同 `r` 的内根盘，
非触圆盘保持不变，则 `D` 的覆盖保持。 -/
theorem covers_of_innerRoot_replace {c c' : Fin 11 → Point} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hc : Covers c r)
    (hchange : ∀ i, MeetsCircle c r i →
      c' i = innerRoot (capHalfWidth (c i) r) r • centerDir (c i))
    (hkeep : ∀ i, ¬ MeetsCircle c r i → c' i = c i)
    (houter : ∀ i, MeetsCircle c r i → ‖c i‖ = outerRoot (capHalfWidth (c i) r) r) :
    Covers c' r := by
  intro x hx
  obtain ⟨i, hi⟩ := hc x hx
  by_cases hmi : MeetsCircle c r i
  · refine ⟨i, ?_⟩
    rw [hchange i hmi]
    have hne : c i ≠ 0 := by
      intro hz
      have h1 := one_sub_le_norm_of_meetsCircle hmi
      rw [hz, norm_zero] at h1
      linarith
    exact dist_innerRoot_le_of_dist_le hne hr0 hr1 (houter i hmi) hmi (mem_unitDisk.mp hx) hi
  · exact ⟨i, by rw [hkeep i hmi]; exact hi⟩

end N11Formalization
