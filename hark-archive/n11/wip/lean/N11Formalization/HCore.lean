import N11Formalization.HgapKernel
import N11Formalization.PremiseBundle

/-!
# R257 (Lead) `HCore` —— 把 `coreClosed` 与七条 `pb_*` 接成 `hH` 要的那个恒等式假设

**这条件存在的理由**：`HHAssembly.hH_of_core`（已落根）的第一个参数形状是
`∀ k i j {x} (hx : x ∈ closedBall certCR rhoCertR), hessEntryAt (first7 x) i j k = distHessRealBox (pad12 (first7 x)) k i j`。
本件把它**证成定理**（喂 `HgapKernel.coreClosed` + `PremiseBundle` 七条件，**零新前提**）⇒
`hH` 的剩余义务只剩 `hd2x/hd2y`（star-class），不再包含恒等式侧。

**证据链**（全部实测，非转述）：
- `HgapKernel.coreClosed`（`880D4FBD5E070CF5`）：Lead 独占串行 `lake env lean` exit 0 / 0 字节（`R257-hgapgate-A.txt` 21:58:15），
  六条画像标准三元组（`R257-hgapax-A.txt` 21:59:47）⇒ claim **C1379**。
- `PremiseBundle.*`（`57EF3F254638BCD5`）：claim **C1377**，8/8 标准三元组。
- 本件的**等价探针**（同一语句、同一证明项，仅命名空间不同 + 带 `#check`/`#print`）已由 Lead 跑过：
  `evidence/lead/scratch/R257-HCore.lean` ⇒ **exit 0 / stderr 0 字节**，且打印出的 `hcore_of_ball` 类型与
  `hH_of_core` 第一参数**逐字相同**（`R257-hcore-A.txt` 22:07:28）⇒ claim **C1380**。

**不做的事**：不引入 `sorry`/`admit`/自定义 `axiom`/`native_decide`；不放宽任何端点；不把 `hd2x/hd2y` 冒充已证
（它们仍是 `hH_of_core` 的显式假设，见 `STATUS.md` R257 追加段的「49 格剩余义务」三部分）。
-/

noncomputable section

namespace N11Formalization.Lead.HCore

open N11Formalization
open N11Formalization.HessSeam
open N11Formalization.Lead.HessBoxMem

/-- **`hcore` 的球上实例化**：`coreClosed` 喂上 `PremiseBundle` 供给的七条前提。
形状与 `HHAssembly.hH_of_core` 的第一参数逐字相同（探针实测过）。 -/
theorem hcore (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    hessEntryAt (first7 x) i j k = distHessRealBox (pad12 (first7 x)) k i j :=
  HgapKernel.coreClosed k i j (first7 x)
    (PremiseBundle.pb_hadj hx) (PremiseBundle.pb_hd hx) (PremiseBundle.pb_hWa k hx)
    (PremiseBundle.pb_hWb k hx) (PremiseBundle.pb_hW6 hx) (PremiseBundle.pb_hWp hx)
    (PremiseBundle.pb_hpos k hx)

end N11Formalization.Lead.HCore
