import N11Formalization.BallJtAsm
import N11Formalization.HessSeamSmooth

/-!
# Lead：**球级 `hJ` 装配（消掉 `hadj` ⇒ 以消费点的 `hnd*` 为参数）**

本件只做**一件事**：把 `BallJtAsm.mem_Jt'_ball_cond` 的参数 `hadj`（**不透明假设** ✗）
  换成 `HessSeamSmooth.differentiableAt_fderiv_residualFun_ball` 给出的**球上 `hadj`** ✓。

**关键形状配对（我逐条核过 ✓）**：
* `HessSeamSmooth.differentiableAt_fderiv_residualFun_ball (hndRho) (hndW) (hndU1) (hndU2) (hndU3) (hndU8) (hndWp)`
  的 **7 个前提**与消费点 `BoxRstar` **L366–373** 的 `hnd*` **逐字同形** ✓
  ⇒ 故本件把 7 条**原样传递**即可 ✓（**不复制、不改形** ✓）。
* 结论形状 = `mem_Jt'_ball_cond` 要的 `hadj` ✓（`∀ x ∈ closedBall certCR rhoCertR, DifferentiableAt ℝ (fun y => fderiv ℝ residualFun y) (first7 x)` ✓）。

⇒ 于是本件的定理**只差** 49 格 KKT×z 的包络 `hKKTz` ✓ ⇒ **与消费点 `hJ` 同形的无条件装配**（在 49 格到位后一行实例化 ✓）。

⚠ 按 DEAD §59：`hadj` 曾是"簿记"切分；本件**把这条簿记消掉** ✓ ⇒ `mem_Jt'_ball_cond` 仍是通用版（保留 ✓），本件是**接消费点**的版本 ✓。
判据：**exit=0 且输出 0 行**。
-/

namespace N11Formalization.Lead.JtBall

open N11Formalization
open N11Formalization.HessSeam

/-- **球级 `hJ` 装配（以消费点的 `hnd*` ＋ 49 格包络 `hKKTz` 为参数）** ✓。 -/
theorem mem_Jt'_ball (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval)
    (hndRho : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ j : Fin 9,
      (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hndW : ∀ x ∈ Metric.closedBall certCR rhoCertR, (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hndU1 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 1 ≠ hub1 x)
    (hndU2 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 2 ≠ hub0 x)
    (hndU3 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 3 ≠ hub0 x)
    (hndU8 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 8 ≠ hub1 x)
    (hndWp : ∀ x ∈ Metric.closedBall certCR rhoCertR, wPoint x ≠ ringCenter x 6)
    (hKKTz : ∀ x : Fin 12 → ℝ, x ∈ Metric.closedBall certCR rhoCertR → ∀ i j : Fin 7,
      (RatInterval.neg (RatInterval.dot lamRat (Hess i j))).Mem
        ((fderiv ℝ TCSystem x (Pi.single (up7 j) (1 : ℝ))) (kkt12 i)))
    (x : Fin 12 → ℝ) (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    ∀ r c : Fin 12, (Jt' Hess r c).Mem ((fderiv ℝ TCSystem x (Pi.single c 1)) r) :=
  mem_Jt'_ball_cond Hess
    (fun x hx => differentiableAt_fderiv_residualFun_ball hndRho hndW hndU1 hndU2 hndU3 hndU8 hndWp x hx)
    hKKTz x hx

end N11Formalization.Lead.JtBall
