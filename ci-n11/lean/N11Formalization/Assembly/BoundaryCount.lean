import N11Formalization.Geometry
import N11Formalization.Definitions

/-!
# 装配：`Covers` ⇒ 至少 9 个盘触到单位圆周（UNRESTRICTED-PROOF-ASSEMBLY §1 的接口）

源文 §1 的关键一步：

> Each boundary disk meets S¹ in one arc of width ≤ 2 asin(r). Since 8 asin(R0) < π,
> at least nine boundary disks are necessary.

本文件把这句从「弧宽计数」（`Geometry/ArcCovering.lean`，cap-arc 交付）**接到**本团队固定的
覆盖对象 `Covers`（`Definitions.lean`）上，并把「boundary disk」做成明确对象（盘与 S¹ 相交）。

接口翻译：`Geometry` 侧计数定理吃 `hcov : ∀ x, ‖x‖ = 1 → ∃ i, dist x (c i) ≤ r`（圆周覆盖），
本团队的 `Covers c r` 吃 `x ∈ unitDisk`（即 `‖x‖ ≤ 1`，闭盘覆盖）。本文件只做这一步翻译，
**不**重新证任何几何事实。
-/

namespace N11Formalization

/-- 「第 `i` 个盘触到单位圆周」：盘 `B(c i, r)` 与 `S¹` 相交。

这是一个**不可判定**的谓词（`∃` 遍历无穷型），故不能用 `Finset.filter`；
下表用子类型 `BoundaryIdx` 承载它。 -/
def MeetsCircle (c : Fin 11 → Point) (r : ℝ) (i : Fin 11) : Prop :=
  ∃ x : Point, ‖x‖ = 1 ∧ dist x (c i) ≤ r

/-- 触到单位圆周的那些盘的下标（子类型形式）。用 `abbrev` 保持透明，便于 `Fintype.card` 的实例统一。 -/
abbrev BoundaryIdx (c : Fin 11 → Point) (r : ℝ) : Type := {i : Fin 11 // MeetsCircle c r i}

instance boundaryIdxFinite (c : Fin 11 → Point) (r : ℝ) : Finite (BoundaryIdx c r) :=
  Finite.of_injective (fun i : BoundaryIdx c r => i.1) fun _ _ h => Subtype.ext h

noncomputable instance boundaryIdxFintype (c : Fin 11 → Point) (r : ℝ) :
    Fintype (BoundaryIdx c r) :=
  Fintype.ofFinite _

/-- **至少 9 个盘触到单位圆周**（源文 §1 的 "at least nine boundary disks"）。

证明：`S¹ ⊆ D`，故 `Covers c r` 限制到 `S¹` 仍是覆盖；只保留触圆的那些盘得到子族
（覆盖 `S¹` 的每个盘都触圆），于是由 `Geometry` 的弧宽计数定理得子族基数 `≥ 9`。 -/
theorem nine_le_card_boundary {c : Fin 11 → Point} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 19 / 50) (hc : Covers c r) :
    9 ≤ Fintype.card (BoundaryIdx c r) := by
  have hcov : ∀ x : Point, ‖x‖ = 1 → ∃ i : BoundaryIdx c r, dist x (c i.1) ≤ r := by
    intro x hx
    obtain ⟨i, hi⟩ := hc x (le_of_eq hx)
    exact ⟨⟨i, x, hx, hi⟩, hi⟩
  exact nine_le_card_of_covers_circle_of_lt_R0 (fun i : BoundaryIdx c r => c i.1) hr0 hr hcov

/-- 几何侧「8 个盘不能覆盖闭单位盘」在 `Covers` 口径下的直接读数。 -/
theorem not_eight_covers {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 19 / 50) :
    ¬ ∃ c : Fin 8 → Point, ∀ x : Point, x ∈ unitDisk → ∃ i : Fin 8, dist x (c i) ≤ r := by
  rintro ⟨c, hc⟩
  exact not_eight_ball_covers_disk_of_lt_R0 c hr0 hr (fun x hx => hc x hx)

/-! ## §1 的另一半：**至多 10 个触圆盘**

源文 §1："Boundary centers have norm >=1-r>r and cannot cover the origin, so there are at most ten."
即：触圆的盘其中心范数 `≥ 1-r`；当 `r < 1/2` 时 `1-r > r`，故触圆盘覆盖不到原点；
而原点必须被某个盘覆盖 ⇒ 触圆盘**至多 10 个**。 -/

/-- 触圆的盘：中心范数 `≥ 1 - r`（反三角不等式）。 -/
theorem one_sub_le_norm_of_meetsCircle {c : Fin 11 → Point} {r : ℝ} {i : Fin 11}
    (h : MeetsCircle c r i) : 1 - r ≤ ‖c i‖ := by
  obtain ⟨x, hx, hd⟩ := h
  have h1 : ‖x‖ - ‖c i‖ ≤ ‖x - c i‖ := le_trans (le_abs_self _) (abs_norm_sub_norm_le x (c i))
  have h2 : ‖x - c i‖ = dist x (c i) := dist_eq_norm x (c i)
  rw [h2] at h1
  rw [hx] at h1
  linarith

/-- `r < 1/2` 时，中心在 `B(0,r)` 内的盘覆盖原点，故不可能触圆。 -/
theorem not_meetsCircle_of_norm_le {c : Fin 11 → Point} {r : ℝ} (hr : r < 1 / 2) {i : Fin 11}
    (h : ‖c i‖ ≤ r) : ¬ MeetsCircle c r i := by
  intro hm
  have := one_sub_le_norm_of_meetsCircle hm
  linarith

/-- **至多 10 个盘触圆**。 -/
theorem card_boundaryIdx_le_ten {c : Fin 11 → Point} {r : ℝ} (hr : r < 1 / 2)
    (hc : Covers c r) : Fintype.card (BoundaryIdx c r) ≤ 10 := by
  obtain ⟨i₀, hi₀⟩ := hc 0 zero_mem_unitDisk
  have hnot : ¬ MeetsCircle c r i₀ := by
    refine not_meetsCircle_of_norm_le hr ?_
    have h : dist (0 : Point) (c i₀) = ‖c i₀‖ := dist_zero_left (c i₀)
    rw [h] at hi₀
    exact hi₀
  have hlt : Fintype.card (BoundaryIdx c r) < Fintype.card (Fin 11) :=
    Fintype.card_subtype_lt (p := fun i : Fin 11 => MeetsCircle c r i) hnot
  rw [Fintype.card_fin] at hlt
  omega

/-- **§1 边界盘计数夹逼**：`r < R0 = 19/50` 且 11 盘覆盖 `D` ⇒ 触圆盘数恰为 **9 或 10**。

这是把源文 §1 的「至少 9」与「至多 10」合起来的接口；下一步排除 10 正是 C450 的职责。 -/
theorem card_boundaryIdx_eq_nine_or_ten {c : Fin 11 → Point} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 19 / 50) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) = 9 ∨ Fintype.card (BoundaryIdx c r) = 10 := by
  have h9 : 9 ≤ Fintype.card (BoundaryIdx c r) := nine_le_card_boundary hr0 hr hc
  have h10 : Fintype.card (BoundaryIdx c r) ≤ 10 := card_boundaryIdx_le_ten (by linarith) hc
  omega

end N11Formalization
