import Mathlib

/-!
# n=11 全局最优性 —— 基础定义（GUIDE §2 的数学接口）

本文件只**固定对象**，不含任何证明难点；难点（C891 根、C892 达到、C923 归约、C921 全域下界）
在其它模块中，且当前**尚未**形式化。

约定：
* `Point` 用 `EuclideanSpace ℝ (Fin 2)`，故 `‖·‖`/`dist` 是欧氏范数/欧氏距离。
* 盘是**闭**盘（`≤`），目标盘是**闭**单位盘（`‖x‖ ≤ 1`）。
* 中心函数是 `Fin 11 → Point`：正好 11 个，允许重合/冗余/任意位置。
-/

namespace N11Formalization

/-- 平面点：`ℝ²` 配欧氏结构。 -/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

/-- 单位闭圆盘 `D = {x : ‖x‖ ≤ 1}`。 -/
def unitDisk : Set Point := {x | ‖x‖ ≤ 1}

/-- 11 个半径 `r` 的**闭**盘以中心 `c` 覆盖 `D`。

中心完全任意：允许重合、允许在 `D` 外、允许冗余；不设对称性、接触图、一般位置、
或"边界盘个数"的任何限制——这些若需要，属于**证明**，不属于定义。 -/
def Covers (c : Fin 11 → Point) (r : ℝ) : Prop :=
  ∀ x : Point, x ∈ unitDisk → ∃ i : Fin 11, dist x (c i) ≤ r

/-- 可行半径集合：`{r : ℝ | 0 ≤ r ∧ ∃ c, Covers c r}`。 -/
def feasibleRadii : Set ℝ := {r | 0 ≤ r ∧ ∃ c : Fin 11 → Point, Covers c r}

@[simp] theorem mem_unitDisk {x : Point} : x ∈ unitDisk ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem zero_mem_unitDisk : (0 : Point) ∈ unitDisk := by
  simp [unitDisk]

theorem unitDisk_nonempty : (unitDisk : Set Point).Nonempty := ⟨0, zero_mem_unitDisk⟩

/-- 覆盖对半径单调（半径放大仍然是覆盖）。 -/
theorem Covers.mono {c : Fin 11 → Point} {r r' : ℝ} (h : Covers c r) (hrr' : r ≤ r') :
    Covers c r' :=
  fun x hx => let ⟨i, hi⟩ := h x hx; ⟨i, le_trans hi hrr'⟩

/-- 任何半径 `r` 的覆盖都强制 `0 ≤ r`（因为 `0 ∈ D`）。 -/
theorem Covers.nonneg {c : Fin 11 → Point} {r : ℝ} (h : Covers c r) : 0 ≤ r := by
  obtain ⟨i, hi⟩ := h 0 zero_mem_unitDisk
  exact le_trans dist_nonneg hi

/-- `r = 2` 用 11 个同中心的盘即可覆盖 `D`：故可行集合非空。 -/
theorem feasibleRadii_nonempty : feasibleRadii.Nonempty := by
  refine ⟨2, by norm_num, fun _ => 0, ?_⟩
  intro x hx
  refine ⟨0, ?_⟩
  rw [dist_zero_right]
  exact le_trans (mem_unitDisk.mp hx) (by norm_num)

/-- 可行集合下有界（下界 `0`）。这是使用 `sInf` 前必须付清的义务之一。 -/
theorem feasibleRadii_bddBelow : BddBelow feasibleRadii :=
  ⟨0, fun _ hr => hr.1⟩

/-- 可行集合的下界恰好是 GUIDE §2 所称的"强接口"第二支。 -/
theorem feasibleRadii_lowerBounds (R : ℝ) :
    R ∈ lowerBounds feasibleRadii ↔
      ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → R ≤ r := by
  constructor
  · intro h r c hr hc
    exact h ⟨hr, ⟨c, hc⟩⟩
  · intro h r hr
    exact h r hr.2.choose hr.1 hr.2.choose_spec

end N11Formalization
