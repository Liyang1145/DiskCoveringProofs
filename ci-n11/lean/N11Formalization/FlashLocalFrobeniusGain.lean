import N11Formalization.FlashLocalFrobeniusActual
import N11Formalization.ResumePinnedCoercivity

/-!
# FlashLocal — 120 局部叶承重链 · 第十四环：**实际有限证书接口收尾**（gain）

把三件已核件接成实际局部增益：

1. `FlashLocalFrobeniusActual.directional_lower_actual_frobenius`（= Actual + Frobenius 证书桥）
   —— 给 `Hdir/2 + 1468 p² − (179/5000)q³ − (2/25)q⁴/3 − 1468(99/200·2/25 + 429/50000)pq² ≤ V2 − R*²`；
2. `ResumePinnedCoercivity.pinned_coercivity`（Lead，pinned-coercivity-1 exit0）—— 8×8 矩阵证书
   ⇒ `μ Σx² ≤ Σ H0 x x + 2t Σ(Gᵀx)²`（`p.succAbove` 限制，**不**把 canonical6 与 source raw8 静默同一）；
3. `ResumeCoercivityCertificate.directional_to_local_gain`（Lead）—— 两条合成得 `q²/100000 ≤ V2 − R*²`。

**常数**（源 `certify_relative_stress_ball.py` 的区间证书 `aq/cq/bq/dq`，按 Lead 指定写死）：
`τ = 1468`（`2·t0`, `t0 = 734`）、`μ = 9/5000`、`d = 2/25`、`B = 99/200`、`A = 429/50000`、
`Ccross = 179/5000`、`q ≤ 729/50000`。

**pin/顺序（Lead 明示，不得省略）**：`p.succAbove` 的顺序**不是** source raw 顺序；
`actualAugmented`/`actualGram` 只是把 *证书矩阵* 写在 `pidx.succAbove` 顺序里，
`C8` 及 `hcSym/hcDom` 必须由源数据经 raw8→canon6 的**同时置换**（C/H/G 一起）供给。
本件不声称该置换已对齐，也不声称 `hcSym/hcDom` 的数值。

**仍未付**：`hrow/hNcol/hNbal/hs/ha/hl/hU/hdiag/hresp/hpin/hsym/hpsd/hρ/hfluxα/hgate`
与 `hCfrob/hFsq`（源区间证书）、`hcSym/hcDom`（8×8 证书）、`hr`（球半径）、`hU`（盒内）；
以及源 α/H/Λ/constants 与 μ-coercivity 的**数值实例化**身份。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset
open N11Formalization.ResumeNetwork N11Formalization.ResumeDirichlet
  N11Formalization.ResumeDirichletShift N11Formalization.ResumeStressComparison
  N11Formalization.ResumeAdaptiveRoot N11Formalization.ResumeAnchorFlux
  N11Formalization.ResumeAdaptiveRows N11Formalization.ResumeAdaptiveBalance
  N11Formalization.ResumeResponseBound
  N11Formalization.ResumeFluxTaylor N11Formalization.ResumeFluxRemainder
  N11Formalization.ResumeAdaptiveShift
  N11Formalization.ResumeCoercivityCertificate N11Formalization.ResumePinnedCoercivity

/-- 源证书的 8×8 augmented 矩阵（`M = H_restricted + 2t G_restricted G_restrictedᵀ − μI`），
写在 `pidx.succAbove` 顺序里。**注意**：该顺序不是 source raw 顺序；raw8→canon6 的置换
须由证书供给方对 C/H/G 同时施加，本定义不做静默识别。 -/
abbrev actualAugmented (pidx : Fin 9) (Λα : Fin 9 → Fin 9 → ℝ) (ρ : Fin 9 → ℝ) (θ : Fin 9 → ℝ)
    (N : Edge → Fin 4 → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  augmented
    (fun i j => H0mat Λα ρ (fun k => circleTangent (θ k)) (pidx.succAbove i) (pidx.succAbove j))
    (fun i a => Gmat anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N
      (pidx.succAbove i) a)
    734 (9 / 5000)

/-- 证书矩阵的同余 `Cᵀ M C`（`C` 由源数据供给，顺序与 `actualAugmented` 一致）。 -/
abbrev actualGram (pidx : Fin 9) (Λα : Fin 9 → Fin 9 → ℝ) (ρ : Fin 9 → ℝ) (θ : Fin 9 → ℝ)
    (N : Edge → Fin 4 → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point)
    (C8 : Matrix (Fin 8) (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  C8.transpose * actualAugmented pidx Λα ρ θ N U C Z * C8

/-- **实际 pinned coercivity 消费**：把 Lead 的 `pinned_coercivity` 用于实际
`H0mat`/`Gmat`（`G` 不是裸矩阵：`GtX` 就是 `Σ_i Gmat i a x_i`，故 `hp2` 直接接上），
配 `t = 734`、`μ = 9/5000`，给 `(9/5000)q² ≤ Σ H0 x x + 1468 p²`。 -/
theorem pinned_coercivity_actual (pidx : Fin 9) (Λα : Fin 9 → Fin 9 → ℝ) (ρ θ : Fin 9 → ℝ)
    (N : Edge → Fin 4 → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point)
    {η q p : ℝ} (C8 : Matrix (Fin 8) (Fin 8) ℝ) (hη : 0 < η)
    (hs : ∀ i j, actualGram pidx Λα ρ θ N U C Z C8 i j = actualGram pidx Λα ρ θ N U C Z C8 j i)
    (hd : ∀ i, η + ∑ j, |actualGram pidx Λα ρ θ N U C Z C8 i j| ≤
      actualGram pidx Λα ρ θ N U C Z C8 i i + |actualGram pidx Λα ρ θ N U C Z C8 i i|)
    (x : Fin 9 → ℝ) (hpin : x pidx = 0)
    (hq2 : q ^ 2 = ∑ i, x i ^ 2)
    (hp2 : p ^ 2 = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N x a) ^ 2) :
    (9 / 5000 : ℝ) * q ^ 2 ≤
      (∑ i, ∑ j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j * x i * x j) + 1468 * p ^ 2 := by
  have hc := pinned_coercivity pidx (H0mat Λα ρ (fun k => circleTangent (θ k)))
    (Gmat anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N)
    734 (9 / 5000) η C8 hη hs hd x hpin
  have hG : (∑ a, (∑ i, Gmat anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N i a * x i) ^ 2)
      = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
          (fun k => circleTangent (θ k)) N x a) ^ 2 := rfl
  rw [hG, ← hp2, ← hq2] at hc
  linarith [hc]

/-- **实际局部增益（Frobenius 有限证书版，常数写死）**：
在上述证书与源数据前件下，`q²/100000 ≤ V2(U + disp θ x) − R*²`。
这是把"Frobenius 证书 + pinned coercivity + 标量余量"三件合成的**条件**结论；
其前件中 `hCfrob/hFsq/hcSym/hcDom` 是源区间证书的有限数字义务（未付），
`hrow/…/hfluxα` 是源身份（未付）。 -/
theorem local_gain_actual_frobenius
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (θ x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ} (pidx : Fin 9) {Λα : Fin 9 → Fin 9 → ℝ}
    {Rstar q p η : ℝ} (C8 : Matrix (Fin 8) (Fin 8) ℝ)
    (hα : ∀ e, 0 ≤ α e)
    (hgate : 1468 * (99 / 200) * p < 1)
    (hrow : ∀ e, Real.sqrt (∑ a, (N e a) ^ 2) ≤ (99 / 200) * α e)
    (hNcol : ∀ a, ∑ e, N e a = 0)
    (hNbal : ∀ a v, ∑ e, (N e a * incidence e v) • edgeVector U C Z e = 0)
    (hs : ∑ e, α e = 1)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = Rstar ^ 2)
    (hU : ∀ i, ‖(U + disp θ x) i‖ ≤ 1)
    (hdiag : ∀ j, anchorWeight α j ≤ 2 / 25)
    (hq0 : 0 ≤ q) (hr : q ≤ 729 / 50000) (hq2 : q ^ 2 = ∑ i, x i ^ 2)
    (hresp : ∀ W : Fin 9 → Point, Eform Λα W W = dirichletEnergy α W)
    (hpin : x pidx = 0) (hsym : ∀ i j, Λα i j = Λα j i)
    (hpsd : ∀ W : Fin 9 → Point, 0 ≤ Eform Λα W W)
    (hCfrob : ∑ i, ∑ j, (if i = pidx ∨ j = pidx then 0 else Cmat Λα θ i j) ^ 2
        ≤ (179 / 5000 : ℝ) ^ 2)
    (hFsq : ∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2 ≤ (429 / 50000 : ℝ) ^ 2)
    (hρ : ∀ i, 0 ≤ ρ i) (hfluxα : ∀ i, flux α U C Z i = ρ i • circleMap (θ i))
    (hp0 : 0 ≤ p)
    (hp2 : p ^ 2 = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N x a) ^ 2)
    (hη : 0 < η)
    (hcSym : ∀ i j, actualGram pidx Λα ρ θ N U C Z C8 i j
        = actualGram pidx Λα ρ θ N U C Z C8 j i)
    (hcDom : ∀ i, η + ∑ j, |actualGram pidx Λα ρ θ N U C Z C8 i j| ≤
      actualGram pidx Λα ρ θ N U C Z C8 i i
        + |actualGram pidx Λα ρ θ N U C Z C8 i i|) :
    q ^ 2 / 100000 ≤ V2 (U + disp θ x) - Rstar ^ 2 := by
  have hdir := directional_lower_actual_frobenius (α := α) (U := U) (C := C) (Z := Z)
    θ x ρ (N := N) (τ := 1468) (d := 2 / 25) (A := 429 / 50000) (B := 99 / 200)
    (Ccross := 179 / 5000) (Rstar := Rstar) (q := q) (p := p) pidx (Λα := Λα)
    hα (by norm_num) (by norm_num) hp0 (by norm_num) hgate hrow hNcol hNbal hs ha hl hU
    hdiag hq0 hq2 hresp hpin hsym hpsd (by norm_num) hCfrob hFsq hρ hfluxα
    (by norm_num) hp2
  have hc := pinned_coercivity_actual pidx Λα ρ θ N U C Z C8 hη hcSym hcDom x hpin hq2 hp2
  have hdir' : (∑ i, ∑ j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j * x i * x j) / 2
      + 1468 * p ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4
      - 1468 * ((99 / 200) * (2 / 25) + 429 / 50000) * p * q ^ 2
      ≤ V2 (U + disp θ x) - Rstar ^ 2 := by
    linarith [hdir]
  exact directional_to_local_gain (V2 (U + disp θ x) - Rstar ^ 2)
    (∑ i, ∑ j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j * x i * x j) q p
    hq0 hr hc hdir'

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.pinned_coercivity_actual
#print axioms N11Formalization.FlashLocal.local_gain_actual_frobenius
