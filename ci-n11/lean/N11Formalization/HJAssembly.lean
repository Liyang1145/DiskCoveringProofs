import N11Formalization.BoxRstar
import N11Formalization.HHAssembly
import N11Formalization.HCore
import N11Formalization.HessSeamBall
import N11Formalization.NondegProof
import N11Formalization.BallJtLam
import N11Formalization.EtaUsage

/-!
# `hj-assembly` · **端到端装配定理**（两个显式洞 `hd2x`/`hd2y`）

**结论**（= `BoxRstar.c891RootSpec_of_krawczyk` L375–376 / `EtaUsage.nd_via_hyp` L43–44 的 `hJ` 槽，
**逐字**）：

```
hJ_of_hcore_and_d2 (hd2x) (hd2y) :
  ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
    (Jt'' (HessOfBox d2xIv d2yIv) k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k)
```

**链**（每一步都指向根内已落根件；**无新数学**）：

```
NondegProof.nd_hnd*  (L433/443/457/469/481/493/502，七条**无条件**球式)
        │
Lead.HCore.hcore   （内核：HgapKernel.coreClosed ＋ PremiseBundle 七条 pb_*）
        │
HHAssembly.hH_of_core hcore hx hd2x hd2y k i j  ->  (hessIvBox d2xIv d2yIv k i j).Mem (hessEntryAt (first7 x) i j k)
        │   （索引翻转：`HessOfBox i j mm = hessIvBox … mm i j`，`rfl` 级 —— `HJ-CONSUMER-AUDIT.md` §3）
        ▼
Lead.JtBall2.mem_Jt''_ball (HessOfBox d2xIv d2yIv) nd_hndRho … nd_hndWp hH x hx
        │
        ▼
      hJ
```

**两个显式洞（不装已证）**：`hd2x`/`hd2y` ＝ `TowerBC.d2xIvBox_mem`/`d2yIvBox_mem`
在 `Q := HessSeam.Q7`、`z := first7 x`、`x ∈ closedBall certCR rhoCertR` 处的实例化。
本件**不证明**它们（属 `starclass` 卡）。**本件也不认领 `hsum`/`hsumR`**（绑在消费者的 `Jt` 上，见 `HJ-ROUTE-A-AUDIT.md` §2）。

**口径**：无 `sorry`/`admit`/自定义 `axiom`/`native_decide`；本件**不打印**
（判据 = stdout/stderr 0 字节）。公理画像见同目录 `hj_assembly_axioms.lean`。
-/

noncomputable section

namespace N11Formalization.HJAssembly

open N11Formalization

/-- **端到端装配**：`hcore`（恒等式侧）＋ 七条 `hnd*`（无条件）＋ 两个显式洞 ⇒ `hJ`。

`hd2x`/`hd2y` 的形状**逐字**是 `TowerBC.d2xIvBox_mem`/`d2yIvBox_mem` 的结论
（`D2IvBoxMem.lean` L456 / L502），在 `Q := HessSeam.Q7`、`z := first7 x` 处的实例化。 -/
theorem hJ_of_hcore_and_d2
    {d2xIv d2yIv : Fin 5 → Fin 7 → Fin 7 → RatInterval}
    (hd2x : ∀ (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
        (_hx : x ∈ Metric.closedBall certCR rhoCertR),
        (d2xIv k i j).Mem (secondPartial (DeltaX k) (first7 x) i j))
    (hd2y : ∀ (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
        (_hx : x ∈ Metric.closedBall certCR rhoCertR),
        (d2yIv k i j).Mem (secondPartial (DeltaY k) (first7 x) i j)) :
    ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (N11Formalization.Lead.JtBall2.Jt''
        (N11Formalization.Lead.HessBox.HessOfBox d2xIv d2yIv) k j).Mem
        ((fderiv ℝ TCSystem x) (Pi.single j 1) k) := by
  -- `hH`：`HessOfBox i j mm = hessIvBox mm i j`（定义级翻转，`rfl`）＋ `hH_of_core` 一次应用
  refine N11Formalization.Lead.JtBall2.mem_Jt''_ball
    (N11Formalization.Lead.HessBox.HessOfBox d2xIv d2yIv)
    N11Formalization.nd_hndRho N11Formalization.nd_hndW
    N11Formalization.nd_hndU1 N11Formalization.nd_hndU2 N11Formalization.nd_hndU3
    N11Formalization.nd_hndU8 N11Formalization.nd_hndWp ?_
  intro x hx i j mm
  exact N11Formalization.HHAssembly.hH_of_core N11Formalization.Lead.HCore.hcore hx
    (fun k i j => hd2x k i j hx) (fun k i j => hd2y k i j hx) mm i j

/-- **接消费点的形状核对**（零 `show`、零新数学）：把本件结论接到 `EtaUsage.nd_via_hyp`
的 `hJ` 绑定形（`Jt` 为**具名变量**，相等性由 `hJt` 显式给出）。
⇒ 「`hH ⇒ hJ` 一整段」在**已落根件之间没有隐藏 cast/形状缝**。 -/
theorem hJ_fit_consumer
    {d2xIv d2yIv : Fin 5 → Fin 7 → Fin 7 → RatInterval}
    (hd2x : ∀ (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
        (_hx : x ∈ Metric.closedBall certCR rhoCertR),
        (d2xIv k i j).Mem (secondPartial (DeltaX k) (first7 x) i j))
    (hd2y : ∀ (k : Fin 5) (i j : Fin 7) {x : Fin 12 → ℝ}
        (_hx : x ∈ Metric.closedBall certCR rhoCertR),
        (d2yIv k i j).Mem (secondPartial (DeltaY k) (first7 x) i j))
    {Jt : Fin 12 → Fin 12 → RatInterval}
    (hJt : Jt = N11Formalization.Lead.JtBall2.Jt''
      (N11Formalization.Lead.HessBox.HessOfBox d2xIv d2yIv)) :
    ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k) := by
  rw [hJt]
  exact hJ_of_hcore_and_d2 hd2x hd2y

end N11Formalization.HJAssembly

