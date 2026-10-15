import N11Formalization.NondegProof
import N11Formalization.HessSeamBall
import N11Formalization.F1.BallD35Hrad
import N11Formalization.TowerBC_N_anyx_layer1

/-!
# `q7-transfer` · `Q7WkBoxTransfer.lean` —— **落根候选**（R266 T1）

## 这件做什么

把 star-class 的 5 条 ℚ 正性/有效性义务
`0 < (wkBoxQ Q7 6).lo`、`0 < (wkBoxQ Q7 (resSlot k)).lo`、`0 < (wkBoxQ Q7 (resSlot k + 1)).lo`、
`0 < (WpIvBoxQ Q7).lo`、`(WpIvBoxQ Q7).Valid`
**一次转移**到 `ndBox` 侧现成的无条件件（`wkBox_pos` / `WpIvBox_pos` / `WpIvBox_valid`），
并补上消费者要的 `hz : ∀ i : Fin 7, (Q7 i).Mem (first7 x i)`。

## 转移为何成立（转义：**不是**文档自述，是可复核的算术）

`Q7 i = ⟨cCert (up7 i) − ρ, cCert (up7 i) + ρ⟩`（`HessSeamBall.lean` L30），
证书盒 `ndBox i = ⟨boxLoCert i, boxHiCert i⟩`（`NondegProof.lean` L76），
`ρ = rhoCert = 4835703278458517 / 2 ^ 82`（`BoxRstar.lean` L83）。
`certC == cCert`（逐位有理相等）、`boxLoCert == certC − ρ`、`boxHiCert == certC + ρ`
三条**精确有理恒等式**已由**盘外整数运算独立复核**（`arithm_check.py`，本目录）⇒ 槽 `0..6` 上 `Q7 i = ndBox i` 为真。

## 形状纪律（照锥内先例 `Transport.lean` L23–36）

* 槽级等式一律写成**数词条**，每条自证；左边 = `⟨cCert (up7 k) ∓ ρ⟩` 的**展开形**，
  右边 = **消费者真正会读到的那个项**（`ndBox (up7 k)`；`up7 k` 与 `(k : Fin 12)` **defeq**，
  `by simpa` 桥过去 ⇒ 下游 `rw` 的 RHS 与消费者字面形**相同**）。
* **唯一一套**：每条槽只有一条叶；`up7` 形与 `(k : Fin 12)` 形是**同一条的两个投影**，
  不并存成两组同义叶（避免"两份必漂移"）。
* **禁忌遵守**：**没有** `pad12Box Q7 = ndBox` 的 12 槽 `funext` 版 —— 那条**为假**
  （槽 7..11：`pad12Box Q7` 给 `⟨0,0⟩`、`ndBox` 给出证书尺度盒；实测量：`ndBox 7..11` 下端
  `−550469530967087572768405/2^82` 等，**均非 0**）。本件只量化到槽 `0..6`。
* **`decide` 递减**：卡上点名的 `fin_cases i <;> decide` 路线是**失败模式**（DEAD.md B1：`ℚ` 上
  `Decidable` 不归约）⇒ 本件全部改用 `simp only [Q7, ndBox, up7, certC, boxLoCert, boxHiCert, rhoCert]`
  ＋ `norm_num`（数值全在 ℚ 字面量层，`norm_num` 正是为此设的）。
  `decide` 版**只作负对照**（`NEGCONTROL-decide.lean`），其红**不登记为数学结论**。

## 等级口径

kernel-proved，无条件；`sorry`/`admit`/自定义 `axiom`/`native_decide`/`Lean.ofReduceBool` = 0；
无 `#check`/`#print`/`#eval`（公理画像用**另置打印副本** `axioprint.lean`）。
公理画像预期 ⊆ `{propext, Classical.choice, Quot.sound}`（门后实测，见 `axioprint.txt`）。
-/

noncomputable section

namespace N11Formalization.Q7Transfer

open N11Formalization
open N11Formalization.RatInterval
open N11Formalization.HessSeam

/-! ## 0. `hz` 供给（卡 §1.T1.4）

`hx : x ∈ closedBall certCR rhoCertR` ⇒ `first7 x ∈ closedBall u0 rhoCertR`（`first7` 是 1-Lipschitz 投影）
⇒ 逐槽 `(Q7 i).Mem (first7 x i)`。两条都**已定名**、均在本件 import 图内（`HessSeamBall.lean` L80 / L48）。
**无新增假设**（只吃 `hx`）。 -/

theorem hz_of_mem_closedBall {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    ∀ i : Fin 7, (Q7 i).Mem (first7 x i) :=
  mem_Q7_of_mem_closedBall (mem_closedBall_first7 hx)

/-! ## 1. 槽级叶：`Q7` → `ndBox`（只到槽 6 = `pad12` 的量化范围）

**写法取自锥内既有先例** `BoxRstar.boxLo_boxHi_center_radius`（L151–154）：
`fin_cases` **先**落到数词槽、**再**拆合取、每个叶子单独 `norm_num`
（件头 L149 自述「把 12 个坐标一次性塞给 `simp`/`norm_num` 会在数组元素内部乱转，实测不通」——
本件 v1/v2/v3 三次探针独立复现了同一读数：`![…] 4` 在目标里**不归约**，`decide` 亦红于
`instDecidableEqRat`（= `DEAD.md` B1））。⚠ `cCert`（`ResidualInterval` 版）与
`certC`（`BoxRstar` 版）逐位相同但**是两份定义** ⇒ `rhoCert`/数组两项**都要**进 `norm_num` 的 simp 集。

叶的 RHS 一律写 `boxLoCert (up7 k)` / `boxHiCert (up7 k)` / `ndBox (up7 k)`：这就是
`wkBoxQ Q7 6` / `WpIvBoxQ Q7` 内 `Q7` 出现的**同一个形**，下游 `rw` 的 RHS 与消费者**字面同形**。 -/

/-- **槽级端点对应（主叶）**：`Q7 k` 的两端就是证书盒在槽 `up7 k` 的两端。 -/
theorem Q7_bounds (k : Fin 7) :
    (Q7 k).lo = boxLoCert (up7 k) ∧ (Q7 k).hi = boxHiCert (up7 k) := by
  fin_cases k <;>
    refine ⟨?_, ?_⟩ <;>
    norm_num [Q7, up7, cCert, boxLoCert, boxHiCert, rhoCert]

/-- **主转移叶**：`Q7 k = ndBox (up7 k)`。 -/
theorem Q7_eq_ndBox (k : Fin 7) : Q7 k = ndBox (up7 k) := by
  obtain ⟨h1, h2⟩ := Q7_bounds k
  show (⟨(Q7 k).lo, (Q7 k).hi⟩ : RatInterval) = ndBox (up7 k)
  rw [h1, h2]
  rfl

/-- 三条数词槽叶（`Q7_eq_ndBox` 的**字面量**实例；`#1`/`#2b`/`#2c` 直接引用即可）。
写法：先 `show` 成 `up7` 形（`ndBox (up7 4)`），再 `exact`（elab 侧 defeq 接住）。
⚠ **不要**写 `rw [Q7_eq_ndBox (4 : Fin 7)]`：`rw` 是语法匹配，目标里的字面量索引
与 `up7 4` 只 **defeq 同形** ⇒ `rw` 报 "Did not find an occurrence"（本件 29 次读数）。 -/
theorem Q7_eq_ndBox_4 : Q7 (4 : Fin 7) = ndBox (4 : Fin 12) := by
  show Q7 (4 : Fin 7) = ndBox (up7 (4 : Fin 7))
  exact Q7_eq_ndBox (4 : Fin 7)
theorem Q7_eq_ndBox_5 : Q7 (5 : Fin 7) = ndBox (5 : Fin 12) := by
  show Q7 (5 : Fin 7) = ndBox (up7 (5 : Fin 7))
  exact Q7_eq_ndBox (5 : Fin 7)
theorem Q7_eq_ndBox_6 : Q7 (6 : Fin 7) = ndBox (6 : Fin 12) := by
  show Q7 (6 : Fin 7) = ndBox (up7 (6 : Fin 7))
  exact Q7_eq_ndBox (6 : Fin 7)

/-- `pad12Box Q7` 侧的槽叶（`ndAngleBox` 分支读 `Q 0..3` 时的**形**）。
写法：`rw [pad12Box]` 展开 `dif_pos` 分支，然后**直接** `exact Q7_eq_ndBox (k : Fin 7)`
（elab 侧 defeq 会把 `Q7 ⟨↑0, ⋯⟩` 与 `Q7 (0 : Fin 7)`、`ndBox (up7 0)` 与 `ndBox 0` 接上；
**不要**插 `show`/`rw` —— 它们走语法匹配，实测报 "Did not find an occurrence"）。 -/
theorem pad12Box_Q7_eq_ndBox_0 : TowerBC.pad12Box Q7 (0 : Fin 12) = ndBox (0 : Fin 12) := by
  rw [TowerBC.pad12Box, dif_pos (by norm_num : ((0 : Fin 12) : ℕ) < 7)]
  exact Q7_eq_ndBox (0 : Fin 7)
theorem pad12Box_Q7_eq_ndBox_1 : TowerBC.pad12Box Q7 (1 : Fin 12) = ndBox (1 : Fin 12) := by
  rw [TowerBC.pad12Box, dif_pos (by norm_num : ((1 : Fin 12) : ℕ) < 7)]
  exact Q7_eq_ndBox (1 : Fin 7)
theorem pad12Box_Q7_eq_ndBox_2 : TowerBC.pad12Box Q7 (2 : Fin 12) = ndBox (2 : Fin 12) := by
  rw [TowerBC.pad12Box, dif_pos (by norm_num : ((2 : Fin 12) : ℕ) < 7)]
  exact Q7_eq_ndBox (2 : Fin 7)
theorem pad12Box_Q7_eq_ndBox_3 : TowerBC.pad12Box Q7 (3 : Fin 12) = ndBox (3 : Fin 12) := by
  rw [TowerBC.pad12Box, dif_pos (by norm_num : ((3 : Fin 12) : ℕ) < 7)]
  exact Q7_eq_ndBox (3 : Fin 7)

/-! ## 2. `wkBoxQ` 侧（`ndAngleBox` 只读槽 `0..6`，在叶上重写，**不进 `sub/mul` 树内部**） -/

/-- `ndAngleBox ∘ pad12Box` 在槽 `0..6` 上与 `ndAngleBox ndBox` 逐 `j` 相同
（`j = 4` 那条经 `Q 0..3`，故用槽 `0..3` 的叶）。
每个分支先 `show` 把 `Fin 9` 索引写成**字面量**（否则 `ndAngleBox` 的模式匹配不展开），
再由四条 `pad12Box_Q7_eq_ndBox_*` 叶把 `if (i:ℕ)<7 then Q7 … else ⟨0,0⟩` 判掉。 -/
theorem ndAngleBox_pad12Box_Q7 (j : Fin 9) :
    ndAngleBox (TowerBC.pad12Box Q7) j = ndAngleBox ndBox j := by
  fin_cases j
  · exact pad12Box_Q7_eq_ndBox_0
  · exact pad12Box_Q7_eq_ndBox_1
  · exact pad12Box_Q7_eq_ndBox_2
  · exact pad12Box_Q7_eq_ndBox_3
  · show piI.sub ((ofRat 2).mul ((((TowerBC.pad12Box Q7 0).add (TowerBC.pad12Box Q7 1)).add
      (TowerBC.pad12Box Q7 2)).add (TowerBC.pad12Box Q7 3)))
      = piI.sub ((ofRat 2).mul ((((ndBox 0).add (ndBox 1)).add (ndBox 2)).add (ndBox 3)))
    rw [pad12Box_Q7_eq_ndBox_0, pad12Box_Q7_eq_ndBox_1, pad12Box_Q7_eq_ndBox_2,
      pad12Box_Q7_eq_ndBox_3]
  · exact pad12Box_Q7_eq_ndBox_3
  · exact pad12Box_Q7_eq_ndBox_2
  · exact pad12Box_Q7_eq_ndBox_1
  · exact pad12Box_Q7_eq_ndBox_0

/-- **`wkBoxQ Q7 j = wkBox j`**（`j : Fin 9` 全域）。 -/
theorem wkBoxQ_Q7 (j : Fin 9) : TowerBC.wkBoxQ Q7 j = wkBox j := by
  rw [TowerBC.wkBoxQ, wkBox, ndAngleBox_pad12Box_Q7, Q7_eq_ndBox_6]

/-- star-class #1/#2a/#2d 一条清完（`j` 分别取 `6`、`resSlot k`、`(resSlot k) + 1`）。 -/
theorem Q7_wkBoxQ_pos (j : Fin 9) : (0 : ℚ) < (TowerBC.wkBoxQ Q7 j).lo := by
  rw [wkBoxQ_Q7]
  exact wkBox_pos j

/-! ## 3. `WpIvBoxQ` 侧（读槽 `{4,5,6}`；实参顺序相反 ⇒ 区间乘交换） -/

/-- 区间乘交换律。**故意不叫** `RatInterval.mul_comm`（避免在 `Q7Transfer` namespace 里造
`…Q7Transfer.RatInterval.*` 假全名，也避免与 mathlib `mul_comm` 解析纠缠）。
⚠ `⟨…⟩` 必须带 `RatInterval` 类型注记（否则 `Expected type could not be determined`）。 -/
theorem ivMulComm (A B : RatInterval) : A.mul B = B.mul A := by
  show (⟨min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi)),
         max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi))⟩ : RatInterval) =
       (⟨min (min (B.lo * A.lo) (B.lo * A.hi)) (min (B.hi * A.lo) (B.hi * A.hi)),
         max (max (B.lo * A.lo) (B.lo * A.hi)) (max (B.hi * A.lo) (B.hi * A.hi))⟩ : RatInterval)
  simp only [mul_comm, min_comm, min_left_comm, max_comm, max_left_comm]

/-- **`WpIvBoxQ Q7 = WpIvBox`** ⇒ star-class #2b/#2c 一条清完。 -/
theorem WpIvBoxQ_Q7 : TowerBC.WpIvBoxQ Q7 = WpIvBox := by
  rw [TowerBC.WpIvBoxQ, WpIvBox, Q7_eq_ndBox_6, Q7_eq_ndBox_5, Q7_eq_ndBox_4]
  rw [ivMulComm]

theorem Q7_WpIvBoxQ_pos : (0 : ℚ) < (TowerBC.WpIvBoxQ Q7).lo := by
  rw [WpIvBoxQ_Q7]
  exact WpIvBox_pos

theorem Q7_WpIvBoxQ_valid : Valid (TowerBC.WpIvBoxQ Q7) := by
  rw [WpIvBoxQ_Q7]
  exact WpIvBox_valid

/-! ## 4. 反侧试验要用的两根两行叶（锥内**没有**该形：盒不含 0 ⇒ 盒里的值非零）

供"某格 `0 ∉ (d2xIv k i j)` ⇒ 该格值 `≠ 0`"这一**单侧否证器**用。
落根归位/定名由 Lead 定（本件只出形）。 -/

theorem ne_zero_of_mem_pos_box {I : RatInterval} {v : ℝ}
    (h : (0 : ℚ) < I.lo) (hI : I.Mem v) : v ≠ 0 := by
  have hlo : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast h
  exact ne_of_gt (lt_of_lt_of_le hlo (RatInterval.mem_lo_le (I := I) (x := v) hI))

theorem ne_zero_of_mem_neg_box {I : RatInterval} {v : ℝ}
    (h : (I.hi : ℚ) < 0) (hI : I.Mem v) : v ≠ 0 := by
  have hhi : (I.hi : ℝ) < 0 := by exact_mod_cast h
  exact ne_of_lt (lt_of_le_of_lt (RatInterval.mem_le_hi (I := I) (x := v) hI) hhi)

end N11Formalization.Q7Transfer
