import N11Formalization.HJAssembly
import N11Formalization.D2Supply

/-!
# `HJBoxInstant` —— 承重接口链的收官实例化(R266,Lead)

把 `HJAssembly.hJ_of_hcore_and_d2` 的两个洞用 `D2Supply` 的球形式供给件**直接填上**
(`d2xIv`/`d2yIv` := 盒表 `TowerBC.d2xIvBox/d2yIvBox Q7C`),得到**机器证据的 `hJ`**:

`hx → (PremiseBundle 七条 + Q7Transfer 正性/hz) → HgapKernel.coreClosed → HCore.hcore
   → HHAssembly.hH_of_core → D2Supply.d2xIvBox_mem_ball/d2yIvBox_mem_ball
   → HJAssembly.hJ_of_hcore_and_d2 ⇒ hJ_box`

**接口选择(如实标注)**:本件的 `Jt` 是 `Jt'' (HessOfBox d2xBox d2yBox)`——即 **盒表**形态。
`nd_via_hyp` 对 `Jt` 全称量化 ⇒ 本件给的 `hJ` 对它直接可用;`hsum`/`hsumR` 对这张表的实例
属乙路线(49 格阶梯生成器 + `krawczykMat` 单调性引理 + K 重声明,见 T5 报告/C1386),不在本件。
数值表 `d2xIv` 的桥(`hBridgeX/Y`)**不在本件**——它是显式假设(见 `D2Supply`),若走数值表须另付。

公理画像:逐条 `#print axioms` 于另置副本。
-/

noncomputable section

namespace N11Formalization.HJBoxInstant

open N11Formalization

/-- 盒表(x 侧):`TowerBC.d2xIvBox Q7C`,作为消费链的 `d2xIv`。 -/
def d2xBox : Fin 5 → Fin 7 → Fin 7 → RatInterval :=
  fun k i j => TowerBC.d2xIvBox D2Supply.Q7C k i j

/-- 盒表(y 侧)。 -/
def d2yBox : Fin 5 → Fin 7 → Fin 7 → RatInterval :=
  fun k i j => TowerBC.d2yIvBox D2Supply.Q7C k i j

/-- 球形式 `hd2x`(盒表)。 -/
theorem hd2x_box : ∀ (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ},
    x ∈ Metric.closedBall certCR rhoCertR →
      (d2xBox k i j).Mem (secondPartial (DeltaX k) (first7 x) i j) := by
  intro k i j x hx
  exact D2Supply.d2xIvBox_mem_ball k i j hx

/-- 球形式 `hd2y`(盒表)。 -/
theorem hd2y_box : ∀ (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ},
    x ∈ Metric.closedBall certCR rhoCertR →
      (d2yBox k i j).Mem (secondPartial (DeltaY k) (first7 x) i j) := by
  intro k i j x hx
  exact D2Supply.d2yIvBox_mem_ball k i j hx

/-- ★ 承重接口链的机器 `hJ`(盒表形态):两个洞已填,`hgap` 时代的条件链到这里全部闭合。 -/
theorem hJ_box : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
    (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox d2xBox d2yBox) k j).Mem
      ((fderiv ℝ TCSystem x) (Pi.single j 1) k) := by
  intro x hx k j
  exact HJAssembly.hJ_of_hcore_and_d2 hd2x_box hd2y_box x hx k j

end N11Formalization.HJBoxInstant
