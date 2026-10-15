/-
# DBMTreeChartConsumer — 从已装配的全树接口到 chart9 / chart8 的**无条件** terminal cover

作用域：源 DBM 树的**连续 chart → 终端 cell 覆盖**（N = 5011, width 64, scale 4096）。
本文件只做一件事：把 `DBMTreeWindowAssembly` 的 `terminal_cover_root`（其 `hv : ∀ n, Valid data n`
已由 79 条冻结窗证书装配掉，**不再有任何整树有效性假设**）与已接受 consumer `DBMTreeConsumer` 的
root-cell 成员关系（`root_cell_chart9` / `root_cell_chart8` / `root_cell_of_InChart8` /
`cell_of_FlashLeafP`）接起来，得到四种入口的**无条件** `∃ l, (data l).terminal = true ∧ Cell l t`。

## 前提（Lead 的集成动作；两个模块尚未在项目树内）

* `N11Formalization.DBMTreeWindowAssembly` 必须存在并导出
  `all_vw : ∀ b : Fin 79, ValidAtWindow data 64 b.val`、
  `all_valid : ∀ n : Fin 5011, Valid data n`、
  `terminal_cover_root (t : Fin 10 → ℝ) (ht : Cell (matrix data 4096 0) t) : ∃ l, (data l).terminal = true ∧ Cell (matrix data 4096 l) t`。
  这来自本成员冻结件 `gen/DBMTreeWindowBridgeComplete.lean`（inline 形态，SHA 7A02BA54…，正在 Complete-1 job 71
  中从该 SHA 直接 `-File` 运行）或 `gen/module_variant/` 形态（**二选一**：inline 与 module_variant 都会声明
  `N11Formalization.DBMTreeWindowAssembler`，同一 import 图不得并存）。
* `N11Formalization.DBMTreeConsumer` 必须存在（已接受件 `evidence/team-flash-20260930/tree-consumer/DBMTreeConsumer.lean`，
  SHA 1CFE08CB0FBE6F11DFD63FA73E2508D76EE3256BD60E0C98FADA7514EEBEB758，尚未根集成）。

## 本文件不证明 / 不声称

* 不证明任何窗口证书：79 条冻结 `windowBBB` 的 `decide +kernel` 由 Lead 负载（batch63 已全核）。
* 不给**具体终端 id**：本文件只到 `∃ l`。把 `l` 钉到终端 4863（`terminal_4863_is_terminal` + 外部 walk）
  再与 leaf284 的 energy/oracle 消费者相连，是另一条义务；leaf284 的语句消费的是「某个具体 cell 的隶属」，
  不是一个 `∃`，二者的接口不在本文件。
* 不是任意 `Covers` 归约、不是半径/能量界、不是整树 leaf 语义。
* **本文件未编译（unbuilt）**：它 import 的两个模块尚不存在于项目树内。按 Lead 校准规则，本文件不构成
  任何整文件核验；当前可用的整文件 exit0 证据只有 `gen/DBMTreeWindowAssemblerSelfTest2.lean`（F72AEE2D…）
  与 `RealProbe`（433D8326…）。
-/
import N11Formalization.DBMTreeWindowAssembly
import N11Formalization.DBMTreeConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option Elab.async false

namespace N11Formalization.DBMTreeChartConsumer

open N11Formalization.DBMTreeKernel
open N11Formalization.DBMSourceTree

/-- 装配后的全树有效性（无任何假设）：本文件全部结论的公共前提，直接用 `DBMTreeWindowAssembly.all_valid`。 -/
theorem all_valid : ∀ n : Fin 5011, Valid data n :=
  N11Formalization.DBMTreeWindowAssembly.all_valid

/-- 消去 `hv` 后的终端覆盖：只余 root cell 隶属这一显式假设。 -/
theorem root_cover (t : Fin 10 → ℝ) (ht : FlashLeafSplit.Cell (matrix data 4096 (0 : Fin 5011)) t) :
    ∃ l : Fin 5011, (data l).terminal = true ∧ FlashLeafSplit.Cell (matrix data 4096 l) t :=
  N11Formalization.DBMTreeWindowAssembly.terminal_cover_root t ht

/-- **chart9**（`y ≥ 0`、`Σ y = 1`，`t = tlift y`）：无条件。 -/
theorem chart9_terminal_cover (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1) :
    ∃ l : Fin 5011, (data l).terminal = true ∧
      FlashLeafSplit.Cell (matrix data 4096 l) (FlashLeafSplit.tlift y) :=
  root_cover _ (N11Formalization.DBMTreeConsumer.root_cell_chart9 y hy0 hy1)

/-- **chart8**（生成元自由坐标 `Chart8 z`，`t = tlift (lift8 z)`）：无条件。 -/
theorem chart8_terminal_cover (z : Fin 8 → ℝ) (hz : N11Formalization.FlashLeaf.Chart8 z) :
    ∃ l : Fin 5011, (data l).terminal = true ∧
      FlashLeafSplit.Cell (matrix data 4096 l)
        (FlashLeafSplit.tlift (N11Formalization.FlashLeaf.lift8 z)) :=
  root_cover _ (N11Formalization.DBMTreeConsumer.root_cell_chart8 z hz)

/-- **InChart8**（`ResumeGlobal` 框架下的另一份 chart，与 `Chart8` 经已接受的 `chart8_iff_inChart8` 同）：无条件。 -/
theorem inChart8_terminal_cover (z : Fin 8 → ℝ) (hz : N11Formalization.ResumeGlobal.InChart8 z) :
    ∃ l : Fin 5011, (data l).terminal = true ∧
      FlashLeafSplit.Cell (matrix data 4096 l)
        (FlashLeafSplit.tlift (N11Formalization.ResumeGlobal.extend z)) :=
  root_cover _ (N11Formalization.DBMTreeConsumer.root_cell_of_InChart8 z hz)

/-- 骨架谓词入口 `FlashLeaf.P t`（skeleton 消费者可直接进入真实树）：无条件。 -/
theorem flashLeafP_terminal_cover {t : Fin 10 → ℝ} (ht : N11Formalization.FlashLeaf.P t) :
    ∃ l : Fin 5011, (data l).terminal = true ∧ FlashLeafSplit.Cell (matrix data 4096 l) t :=
  root_cover t (N11Formalization.DBMTreeConsumer.cell_of_FlashLeafP ht)

/-! ### 控制 -/

/-- 正控：均匀 chart `y ≡ 1/9`（`Σy = 1`，故属真实 chart）给出终端覆盖。 -/
theorem uniform_chart9_terminal_cover :
    ∃ l : Fin 5011, (data l).terminal = true ∧
      FlashLeafSplit.Cell (matrix data 4096 l)
        (FlashLeafSplit.tlift (fun _ : Fin 9 => (1 : ℝ) / 9)) :=
  chart9_terminal_cover _ (fun _ => by norm_num) (by simp)

/-- 负控（入口非空性）：零 lift（`Σy = 0 ≠ 1`）**不在**真实 root cell，故本文件入口对该 `t` 不可用
（`Σy = 1` 与 pin 行 `(9,0) = -4096` 是承重的；见已接受 `root_cell_rejects_zero_lift`）。 -/
theorem zero_lift_not_in_root :
    ¬ FlashLeafSplit.Cell (matrix data 4096 (0 : Fin 5011))
      (FlashLeafSplit.tlift (fun _ : Fin 9 => 0)) :=
  N11Formalization.DBMTreeConsumer.root_cell_rejects_zero_lift

end N11Formalization.DBMTreeChartConsumer

#check @N11Formalization.DBMTreeChartConsumer.all_valid
#check @N11Formalization.DBMTreeChartConsumer.root_cover
#check @N11Formalization.DBMTreeChartConsumer.chart9_terminal_cover
#check @N11Formalization.DBMTreeChartConsumer.chart8_terminal_cover
#check @N11Formalization.DBMTreeChartConsumer.inChart8_terminal_cover
#check @N11Formalization.DBMTreeChartConsumer.flashLeafP_terminal_cover
#check @N11Formalization.DBMTreeChartConsumer.uniform_chart9_terminal_cover
#check @N11Formalization.DBMTreeChartConsumer.zero_lift_not_in_root
#print axioms N11Formalization.DBMTreeChartConsumer.all_valid
#print axioms N11Formalization.DBMTreeChartConsumer.chart9_terminal_cover
#print axioms N11Formalization.DBMTreeChartConsumer.chart8_terminal_cover
#print axioms N11Formalization.DBMTreeChartConsumer.inChart8_terminal_cover
#print axioms N11Formalization.DBMTreeChartConsumer.flashLeafP_terminal_cover
#print axioms N11Formalization.DBMTreeChartConsumer.uniform_chart9_terminal_cover
#print axioms N11Formalization.DBMTreeChartConsumer.zero_lift_not_in_root
