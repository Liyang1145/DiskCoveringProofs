import N11Formalization.TowerBC_N_anyx_layer1

/-!
# hess-seam / 球级两条**廉价桥**：`Q7` 盒实例化 ＋ `first7` 投影 1-Lipschitz

**用途**：把点级收口（`mem_hessEntry_uncond`/`mem_Jt_at_center_uncond`，件 `HessSeamHL7`）接到**球级**
（落根的 `HessSeam.HHBall : ∀ x ∈ closedBall u0 rhoCertR, …`），并为 `tower-bc` 的**6 族盒版二阶叶**
（按裁定**选 2** = `Fin 7` 量词 ＋ z 空间求值）提供**盒实例**。

* **桥 1**：`Q7 i := ⟨cCert i − ρ, cCert i + ρ⟩`（`u0` 处半径 `rhoCertR` 的 7 维盒）＋ 球↔盒双向引理
  ＋ 与 `TowerBC.pad12Box Q7`（前 7 槽照抄、后 5 槽单点 `[0,0]`）的**对接**（一行，用它自己的
  `pad12Box_mem_pad12` ✓）。
* **桥 2**：`first7` 是 **1-Lipschitz 投影** ⇒ `x ∈ closedBall cCertR ρ ⇒ first7 x ∈ closedBall u0 ρ`
  （`u0 := first7 cCertR` ✓）。逐坐标用 `dist_pi_le_iff` ＋ `dist x cCertR ≤ ρ` ✓ —— **无新增非退化前提** ✓。

**不收**：`z ↦ pad12 z` 的**反向**提升（`z ∈ ball u0 ρ ⇒ pad12 z ∈ ball cCertR ρ`）**是假命题** ✗
（`pad12 z` 的 7..11 位恒 0，而 `cCertR` 那几位非零、两心距 ~0.1 ≫ ρ ✓ —— `tower-bc` 已实测 ✓）。
口径：无 `sorry`/公理/`native_decide`；`decide`/`omega` 只碰 `Fin`/`ℕ` 索引。
-/

noncomputable section

namespace N11Formalization

namespace HessSeam

open RatInterval

/-- `u0` 处半径 `rhoCertR` 的 **7 维盒**（端点 = 精确 `ℚ`；`u0 i = (cCert i : ℝ)` ✓）。 -/
def Q7 : Fin 7 → RatInterval :=
  fun i => ⟨cCert (up7 i) - rhoCert, cCert (up7 i) + rhoCert⟩

theorem u0_apply (i : Fin 7) : u0 i = ((cCert (up7 i) : ℚ) : ℝ) := rfl

theorem cCertR_apply (j : Fin 12) : cCertR j = ((cCert j : ℚ) : ℝ) := rfl

/-- `Q7` 下端的 ℝ 读数（**显式 cast 等式**：`linarith` 把 `↑rhoCert` 与 `rhoCertR` 当**两个原子** ✗，
故必须先 `rw` 成同一符号 ✓）。 -/
theorem Q7_lo_eq (i : Fin 7) : (((Q7 i).lo : ℚ) : ℝ) = u0 i - rhoCertR := by
  rw [Q7, Rat.cast_sub, ← u0_apply i]
  rfl

theorem Q7_hi_eq (i : Fin 7) : (((Q7 i).hi : ℚ) : ℝ) = u0 i + rhoCertR := by
  rw [Q7, Rat.cast_add, ← u0_apply i]
  rfl

/-- **桥 1（球 → 盒）**：`HHBall` 的 `Fin 7` 球 ⇒ `Q7` 的逐槽包含性。 -/
theorem mem_Q7_of_mem_closedBall {z : Fin 7 → ℝ} (hz : z ∈ Metric.closedBall u0 rhoCertR) :
    ∀ i : Fin 7, (Q7 i).Mem (z i) := by
  intro i
  have hz' : dist z u0 ≤ rhoCertR := Metric.mem_closedBall.mp hz
  have hi : dist (z i) (u0 i) ≤ rhoCertR := (dist_pi_le_iff rhoCertR_pos.le).mp hz' i
  rw [Real.dist_eq] at hi
  have habs := abs_le.mp hi
  refine mem_iff.mpr ⟨?_, ?_⟩
  · rw [Q7_lo_eq i]
    linarith [habs.1]
  · rw [Q7_hi_eq i]
    linarith [habs.2]

/-- **桥 1（盒 → 球）**（反向，供内部证明用）。 -/
theorem mem_closedBall_of_mem_Q7 {z : Fin 7 → ℝ} (hz : ∀ i : Fin 7, (Q7 i).Mem (z i)) :
    z ∈ Metric.closedBall u0 rhoCertR := by
  rw [Metric.mem_closedBall, dist_pi_le_iff rhoCertR_pos.le]
  intro i
  have hi := mem_iff.mp (hz i)
  rw [Q7_lo_eq i] at hi
  rw [Q7_hi_eq i] at hi
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- **桥 1（对接）**：`Q7` 的球包含性 ⇒ `TowerBC.pad12Box Q7` 逐槽包含 `pad12 z`
（后 5 槽是单点 `[0,0]`，正合 `pad12 z` 的 7..11 位 ✓）。 -/
theorem mem_pad12Box_Q7_of_mem_closedBall {z : Fin 7 → ℝ}
    (hz : z ∈ Metric.closedBall u0 rhoCertR) :
    ∀ i : Fin 12, (TowerBC.pad12Box Q7 i).Mem (pad12 z i) :=
  TowerBC.pad12Box_mem_pad12 (mem_Q7_of_mem_closedBall hz)

/-- **桥 2（`first7` 投影 1-Lipschitz）**：`x ∈ closedBall cCertR ρ ⇒ first7 x ∈ closedBall u0 ρ`。 -/
theorem mem_closedBall_first7 {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall cCertR rhoCertR) :
    first7 x ∈ Metric.closedBall u0 rhoCertR := by
  have hx' : dist x cCertR ≤ rhoCertR := Metric.mem_closedBall.mp hx
  rw [Metric.mem_closedBall, dist_pi_le_iff rhoCertR_pos.le]
  intro i
  have hi : dist (x (up7 i)) (cCertR (up7 i)) ≤ rhoCertR :=
    (dist_pi_le_iff rhoCertR_pos.le).mp hx' (up7 i)
  rw [show dist (first7 x i) (u0 i) = dist (x (up7 i)) (cCertR (up7 i)) from rfl]
  exact hi

/-! ## 球级第二层：`Apt`/`Bpt` 搬运 ＋ **7 维球 → 12 维球** 的提升 `lift12`

`lift12 z` = `pad12 z` 的前 7 位取自 `z`、**后 5 位取自 `certCR`** ⇒
`first7 (lift12 z) = z` ✓ 且 `lift12 z ∈ closedBall certCR rhoCertR` ✓（后 5 位与 `certCR` 逐坐标相等 ⇒ 距离贡献 0 ✓）。
**用途**：`F1/BallD35Hrad` 的球级行（`DxIvBox_mem`/`dUxIvBox_mem`/后来的 `d2xIvBox_mem`）都吃 **12 维球** ✓，
而 `HHBall` 的球是 **7 维** ✗ ⇒ 必须经 `lift12` ＋ `Apt/Bpt_transport`（几何只读 0..6 位 ✓）搭桥 ✓。
⚠ 反向（`z ↦ pad12 z` 进 `certCR` 球）**假** ✗（7..11 位归零 vs `certCR` 非零 ✓）。 -/

/-- `Apt` 的搬运（几何只读 0..6 位）—— 由根内 `Transport` 的叶族组合 ✓。 -/
theorem Apt_transport (k : Fin 5) (x : Fin 12 → ℝ) :
    Apt k (pad12 (first7 x)) = Apt k x := by
  fin_cases k
  · exact Uvec_transport x 1
  · exact Uvec_transport x 2
  · exact Uvec_transport x 3
  · exact Uvec_transport x 8
  · exact wPoint_transport x

/-- `Bpt` 的搬运 ✓。 -/
theorem Bpt_transport (k : Fin 5) (x : Fin 12 → ℝ) :
    Bpt k (pad12 (first7 x)) = Bpt k x := by
  fin_cases k
  · exact hub1_transport x
  · exact hub0_transport x
  · exact hub0_transport x
  · exact hub1_transport x
  · exact ringCenter_transport x 6

/-- **7 维球 → 12 维球的提升**：前 7 位取 `z`、后 5 位取 `certCR`。 -/
def lift12 (z : Fin 7 → ℝ) : Fin 12 → ℝ :=
  fun j => if h : j.1 < 7 then z ⟨j.1, h⟩ else cCertR j

theorem first7_lift12 (z : Fin 7 → ℝ) : first7 (lift12 z) = z := by
  funext i
  simp only [lift12, first7, dif_pos i.isLt]

/-- `lift12` 保持 `first7` 侧的坐标：`lift12 z (up7 i) = z i` ✓。 -/
theorem lift12_up7 (z : Fin 7 → ℝ) (i : Fin 7) : lift12 z (up7 i) = z i := by
  have h := congrFun (first7_lift12 z) i
  simp only [first7] at h
  exact h

/-- **`lift12 z` 落在 12 维证书球内**（后 5 位与 `certCR` 逐坐标相等 ⇒ 该部分距离 0 ✓）。 -/
theorem lift12_mem_ball {z : Fin 7 → ℝ} (hz : z ∈ Metric.closedBall u0 rhoCertR) :
    lift12 z ∈ Metric.closedBall cCertR rhoCertR := by
  have hz' : dist z u0 ≤ rhoCertR := Metric.mem_closedBall.mp hz
  rw [Metric.mem_closedBall, dist_pi_le_iff rhoCertR_pos.le]
  intro j
  by_cases h : j.1 < 7
  · have hj : dist (z ⟨j.1, h⟩) (u0 ⟨j.1, h⟩) ≤ rhoCertR :=
      (dist_pi_le_iff rhoCertR_pos.le).mp hz' ⟨j.1, h⟩
    rw [lift12, dif_pos h]
    rw [show cCertR j = u0 ⟨j.1, h⟩ from rfl]
    exact hj
  · rw [lift12, dif_neg h]
    simp only [dist_self]
    exact rhoCertR_pos.le

end HessSeam

end N11Formalization
