import N11Formalization.HessBoxMem
import N11Formalization.F1.BallD35C14
import N11Formalization.F1.BallD35C9

/-!
# `transport-hh` · 义务 (1)：`distHessRealBox` 的 transport ＋ (3) `hH` 的条件式装配

**任务书**：`evidence/lead/R257-TEAM-BRIEF.md` §3 I-3（第一条）＋ §7（真名表）＋ §9（Lead 对本件的裁决）。
**判据**：`lake env lean <本件>` **exit 0 且输出 0 字节**（本件不含 `#check`/`#print`；
公理画像在同目录 `HessBoxTransportAxioms.lean`——**同文＋尾部 `#print axioms` 的副本**——里取，
**只在 ERROR=0 时读**）。

## 事实依据：`distHessRealBox` 的每个原子都只读参数 `x : Fin 12 → ℝ` 的前 7 槽

`Lead.HessBoxMem.distHessRealBox`（`HessBoxMem.lean` L26–37）只出现五类原子：

| 原子 | 定义位置 | 只读的槽 | 搬运件（**根内已有，按名引用，不重述**） |
|---|---|---|---|
| `Apt k x` / `Bpt k x` | `ResidualDerivD.lean` L281 / L288 | `Uvec`/`wPoint`/`hub0`/`hub1`/`ringCenter 6` ⇒ 0..6 | `Apt_transport`/`Bpt_transport`（`F1/BallD35C12.lean` L82/L91） |
| `dUxReal k i x` | `F1/BallD35Hrad.lean` L359 | `dUvec0Real`/`coord`/`ring0Real` ⇒ 0..6 | `dUxReal_transport`（`F1/BallD35C14.lean` L85） |
| `dUyReal k i x` | `F1/BallD35Hrad.lean` L366 | 同上 ＋ `WpReal x`（槽 4/5/6） | `dUyReal_transport`（`F1/BallD35C14.lean` L94；`k = 4` 支吃 `WpReal` + `pad12_first7_4/5/6`，先例 L101/L118） |
| `secondPartial (DeltaX k) (first7 x) i j` / `DeltaY` | `D2Leaves.lean` L1271/L1275；`ResidualDerivJTHess.lean` L80 | 只吃 `first7 x` | `first7_pad12`（`F1/BallD35C9.lean` L68） |

⇒ 义务 (1) 是**纯拼装**：一条 `simp only` 表，不新引任何数学。

## 本件的三条定理

1. `distHessRealBox_transport` —— I-3 第一条，**无条件**（不吃 `hx`）。
2. `hessEntryAt_eq_distHessRealBox_of_core` —— 把 I-1 `coreClosed` 的结论形（右端
   `distHessRealBox (pad12 u)`）搬到 I-3 的消费方形（右端 `distHessRealBox x`）。
3. `hH_of_core` —— `BallJtLam` 要的球级 `hH`，**新增假设只有 `hcore`（球形式）＋ `mem_hessIvBox`
   本来就要的两条 `d2` 喂料**。⇒ 成员 1（`coreClosed`）／成员 2（`d2`）一落地，Lead 一行实例化。

## ★ 为什么 `hcore` 必须是**球形式**而不是全域（Lead 裁决①，后来者会踩第二次）

全域形状 `∀ k i j (u : Fin 7 → ℝ), hessEntryAt u i j k = distHessRealBox (pad12 u) k i j`
**假设过强、实际不可满足**：I-1 的 `coreClosed` 只在**七条前提**（`hadj`、`hd`、
`0 < Wfun (resSlot k) u`、`0 < Wfun ((resSlot k)+1) u`、`0 < Wfun 6 u`、`0 < Wpf u`、
`0 < SRad k u`）之下给出恒等式；这些前提**只由 I-2 在 `u = first7 x`、`x ∈ closedBall certCR rhoCertR`
上供给**（球外没有任何件给它们；且 `SRad k u = 0` 时 `√` 不可微 ⇒ 全域版本**原则上不成立**）。
⇒ 本件把 `hcore` 绑成
`∀ k i j {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR),
   hessEntryAt (first7 x) i j k = distHessRealBox (pad12 (first7 x)) k i j`
——**正好**是 `coreClosed k i j (first7 x) (pb_* hx)` 能一行实例化的形状（结论一字未动）。
这与本工程「不得用改命题换绿灯」同族，只是方向相反：**假设侧也不可写得比可实现的更强**。

## 口径（如实）

* **不**碰 `hgap` 标量核（`hgap-kernel` 的域）。
* **不**新造盒表：`hessIvBox`（`HessIvBox.lean` L25）／`radIvBox_pos`·`twoRadSqrtIvBox_pos`
  （`F1/BallD35Hrad.lean` L524/L147，**无条件** ⇒ `mem_hessIvBox` 的 `hrad`/`h2rad` 不是本件假设）
  全部**按名引用**。
* **不改命题强度换绿灯**。简报 I-3 把盒二阶表写成裸名 `d2xIvBox`；根内真名是
  `N11Formalization.TowerBC.d2xIvBox (Q : Fin 7 → RatInterval) (k i j)`
  （`TowerBC_N_anyx_layer1.lean` L1304），**多一个 `Q` 参数**，且 `…_mem` 还吃
  `hz : ∀ i, (Q i).Mem (z i)` 与一簇 star-假设（`D2IvBoxMem.lean` L432/L478）。
  ⇒ 本件把 `hH_of_core` 的 `d2` 侧**如实**参数化为
  `d2xIv d2yIv : Fin 5 → Fin 7 → Fin 7 → RatInterval`（**不**冒充无条件）。
  `Q` 的选取与 star-假设的解除 = 成员 2（I-2）的产出；逐条完整类型见 `HJ-CONSUMER-AUDIT.md` §4。
* **无** `sorry`/`admit`/自定义 `axiom`/`native_decide`。
-/

noncomputable section

namespace N11Formalization.HHAssembly

open N11Formalization
open N11Formalization.RatInterval
open N11Formalization.HessSeam
open N11Formalization.Lead.HessBox
open N11Formalization.Lead.HessBoxMem

/-! ## 1. I-3 第一条：`distHessRealBox` 只读前 7 槽 -/

/-- **`distHessRealBox` 的 transport**（简报 §3 I-3 第一条）。 -/
theorem distHessRealBox_transport (x : Fin 12 → ℝ) (k : Fin 5) (i j : Fin 7) :
    distHessRealBox (pad12 (first7 x)) k i j = distHessRealBox x k i j := by
  simp only [distHessRealBox, Apt_transport k x, Bpt_transport k x,
    dUxReal_transport k i x, dUxReal_transport k j x, dUyReal_transport k i x,
    dUyReal_transport k j x, first7_pad12]

/-! ## 2. `coreClosed` 形态 → 消费方形态（`hcore` 是**球形式**，见件头 ★） -/

/-- I-1 `coreClosed` 的结论形（右端 `distHessRealBox (pad12 (first7 x))`）⇒ I-3 的
`hessEntryAt_eq_distHessRealBox_of_ball`（右端 `distHessRealBox x`）。
`hx` 在**结论侧**不进入证明（transport 无条件），但**必须**出现在 `hcore` 的绑定里，
否则假设不可实现（件头 ★）。 -/
theorem hessEntryAt_eq_distHessRealBox_of_core
    (hcore : ∀ (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
        (_hx : x ∈ Metric.closedBall certCR rhoCertR),
        hessEntryAt (first7 x) i j k = distHessRealBox (pad12 (first7 x)) k i j)
    (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    hessEntryAt (first7 x) i j k = distHessRealBox x k i j :=
  (hcore k i j hx).trans (distHessRealBox_transport x k i j)

/-! ## 3. I-3 第三条：`hH` 的条件式装配（成员任务 (3)） -/

/-- **`hH`，条件于球形式的 `coreClosed` 恒等式 `hcore`**。
结论**逐字**是简报 I-3 的 `hH`；`hd2x`/`hd2y` **逐字**是 `mem_hessIvBox`
（`HessBoxMem.lean` L40–46）的两个 `d2` 参数形状 ⇒ 由 `TowerBC.d2xIvBox_mem`/`d2yIvBox_mem`
在成员 2 的 star-假设落地后直接给出。`hrad`/`h2rad` 由根内无条件件供给 ✓。

**消费方索引对应**（`HJ-CONSUMER-AUDIT.md` §3）：`BallJtLam` 的
`Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval` 要按 `Hess := HessOfBox d2xIv d2yIv` 实例化，
而 `HessOfBox d2xIv d2yIv i j mm = hessIvBox d2xIv d2yIv mm i j`（`HessIvBox.lean` L41–43）
⇒ **`Hess` 的第三指标 `mm : Fin 5` 就是本件的 `k`**（顺序是 `i j mm ↔ k i j` 的反写）。

**正门（Lead 一行）**：`hH_of_core (coreClosed 形态的 hcore) hx hd2x hd2y k i j`。 -/
theorem hH_of_core {d2xIv d2yIv : Fin 5 → Fin 7 → Fin 7 → RatInterval}
    (hcore : ∀ (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
        (_hx : x ∈ Metric.closedBall certCR rhoCertR),
        hessEntryAt (first7 x) i j k = distHessRealBox (pad12 (first7 x)) k i j)
    {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (hd2x : ∀ (k : Fin 5) (i j : Fin 7),
      (d2xIv k i j).Mem (secondPartial (DeltaX k) (first7 x) i j))
    (hd2y : ∀ (k : Fin 5) (i j : Fin 7),
      (d2yIv k i j).Mem (secondPartial (DeltaY k) (first7 x) i j))
    (k : Fin 5) (i j : Fin 7) :
    (hessIvBox d2xIv d2yIv k i j).Mem (hessEntryAt (first7 x) i j k) := by
  have hrad : 0 < (radIvBox k).lo := radIvBox_pos k
  have h2rad : 0 < (twoRadSqrtIvBox k).lo := twoRadSqrtIvBox_pos k hrad
  have hmem := mem_hessIvBox d2xIv d2yIv hx k hrad h2rad hd2x hd2y i j
  rwa [hcore k i j hx, distHessRealBox_transport x k i j]

end N11Formalization.HHAssembly
