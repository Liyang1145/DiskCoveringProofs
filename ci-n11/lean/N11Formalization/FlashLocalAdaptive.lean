import Mathlib
import N11Formalization.FlashLocalMix

/-!
# FlashLocal — 120 局部叶承重链 · 第四环：**adaptive cross identity**（源 L26–29 的恒等式）

源 `team-current/lead/ADAPTIVE-STRESS-FINITE-REMAINDER.md` 第 26–29 行：

```
26. Adaptive linear term:
27. 2<Mx,delta>=2<Mx,v>+2<Mx,w>
28. >=tau x^T GG^T x - m q^3.
   Here T_je=2 s_je (X_v-X_w)·J U0_j for an edge incident to anchor j, and zero otherwise;
   s_je is its signed incidence. Flux change (Mx)_j=sum_e s_je(Qx)_e(X_v-X_w), with no factor2.
29. Direct summation therefore gives 2<Mx,v>=tau x^T G G^T x.
   This is an algebraic identity, not a residual containing zero.
```

**exact 定义绑定（源 `team-current/lead/interval_network_envelope.py` L47–54，逐行读得）**：

```python
B=zeros(41,45); T=zeros(9,45)
for j,(v,w) in enumerate(edges):
    d = sub(X[v], X[w])                          # 边向量 d_e = X_v - X_w
    for node,sgn in [(v,1),(w,-1)]:
        if node>=9:  ... B[...] += sgn*d[k]      # 自由节点：几何平衡
        else:        T[node,j] += 2*sgn*dot(d,(-U[node][1], U[node][0]))   # 锚点：T
B[40,j]=1                                        # 全 1 行（sum N = 0）
```

⇒ `T_je = 2 * s_je * ⟪d_e, tangent_j⟫`，`tangent_j = (-U_j.y, U_j.x)`（本工程 `circleTangent`），
`s_je = +1`（锚点=第一端点）/ `-1`（锚点=第二端点）/ `0`（边不含锚点）。
**对源边表 `edges`，锚点恒为第二端点 ⇒ `s_je = -1`**（Lead 指出的"site-anchor 为负"；
本件把 `sgn` 作为**任意** `κ → ι → ℝ` 保留，不改符号约定）。

`B N = 0`（前 40 行几何平衡 + 末行全 1 ⇒ `sum_e N_e = 0`）**不在本件使用**：本件是
**纯有限和重排**，不需要 `B N = 0`、不需要矩阵可逆、不需要正定、不含 `H0`。

本件证明（源第 29 行）：`2 * sum_j ⟪(Mx)_j, x_j • tangent_j⟫ = tau * sum_a ((G^T x)_a)^2`，
其中 `sum_a ((G^T x)_a)^2 = x^T G G^T x`。

**载体**：`κ` = 边指标（源 45 或 51 皆可，任意 `Fintype`）、`ι` = 锚点指标（源 `Fin 9`）、
`a : Fin 4`（源 N 的列数）；`Point = EuclideanSpace ℝ (Fin 2)`。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- 源 T（`interval_network_envelope.py` L53）：`T_je = 2 * s_je * ⟪d_e, tangent_j⟫`。 -/
def Tmat (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (j : ι) (e : κ) : ℝ :=
  2 * sgn e j * inner ℝ (evec e) (tang j)

/-- `G = T N`：`G_ja = sum_e T_je * N_ea`。 -/
def Gmat (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (N : κ → Fin 4 → ℝ) (j : ι) (a : Fin 4) : ℝ :=
  ∑ e, Tmat sgn evec tang j e * N e a

/-- `(G^T x)_a = sum_j G_ja * x_j`（源 `x` 是锚点角位移；`x_8 = 0` 由调用方约束）。 -/
def GtX (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (N : κ → Fin 4 → ℝ) (x : ι → ℝ) : Fin 4 → ℝ :=
  fun a => ∑ j, Gmat sgn evec tang N j a * x j

/-- `(T x)_e = sum_j T_je * x_j`：把 T 作用在 x 上的中间量。 -/
def Tx (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (x : ι → ℝ) (e : κ) : ℝ :=
  ∑ j, Tmat sgn evec tang j e * x j

/-- `Q x`（源 `Q = tau N G^T`）：`(Qx)_e = tau * sum_a N_ea * (G^T x)_a`。 -/
def Qx (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (N : κ → Fin 4 → ℝ) (τ : ℝ) (x : ι → ℝ) (e : κ) : ℝ :=
  τ * ∑ a, N e a * GtX sgn evec tang N x a

/-- `(Mx)_j = sum_e s_je (Qx)_e • d_e`（源第 29 行：锚点通量，"no factor 2"）。 -/
def Mx (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (N : κ → Fin 4 → ℝ) (τ : ℝ) (x : ι → ℝ) (j : ι) : Point :=
  ∑ e, (sgn e j * Qx sgn evec tang N τ x e) • evec e

/-- **关键重排（两处和的交换）**：`(G^T x)_a = sum_e N_ea * (T x)_e`。
这是源第 29 行"Direct summation"里唯一非平凡的一步，纯有限和重排。 -/
theorem GtX_eq (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (N : κ → Fin 4 → ℝ) (x : ι → ℝ) (a : Fin 4) :
    GtX sgn evec tang N x a = ∑ e, N e a * Tx sgn evec tang x e := by
  simp only [GtX, Gmat, Tx, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- 第一步：把 `⟨(Mx)_j, x_j • tangent_j⟩` 按双线性性展开。 -/
theorem two_M_eq (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (N : κ → Fin 4 → ℝ) (τ : ℝ) (x : ι → ℝ) :
    2 * ∑ j, inner ℝ (Mx sgn evec tang N τ x j) (x j • tang j)
      = ∑ j, ∑ e, Tmat sgn evec tang j e * Qx sgn evec tang N τ x e * x j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Mx, sum_inner]
  simp only [realInner_smul_right', realInner_smul_left']
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  unfold Tmat
  ring

/-- 第二步：交换 `j` 与 `e` 两处和，把 `x` 收进 `T x`。 -/
theorem sum_TQ_eq (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (N : κ → Fin 4 → ℝ) (τ : ℝ) (x : ι → ℝ) :
    ∑ j, ∑ e, Tmat sgn evec tang j e * Qx sgn evec tang N τ x e * x j
      = ∑ e, Qx sgn evec tang N τ x e * Tx sgn evec tang x e := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Tx, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- 第三步：代入 `Q = tau N G^T` 并把 `N` 收到 `G^T x` 上。 -/
theorem Qx_Tx_eq (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (N : κ → Fin 4 → ℝ) (τ : ℝ) (x : ι → ℝ) :
    ∑ e, Qx sgn evec tang N τ x e * Tx sgn evec tang x e
      = τ * ∑ a, GtX sgn evec tang N x a * (∑ e, N e a * Tx sgn evec tang x e) := by
  have h1 : ∀ e, Qx sgn evec tang N τ x e * Tx sgn evec tang x e
      = τ * ∑ a, (N e a * GtX sgn evec tang N x a) * Tx sgn evec tang x e := by
    intro e
    unfold Qx
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have h2 : ∀ a, (∑ e, (N e a * GtX sgn evec tang N x a) * Tx sgn evec tang x e)
      = GtX sgn evec tang N x a * ∑ e, N e a * Tx sgn evec tang x e := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  calc ∑ e, Qx sgn evec tang N τ x e * Tx sgn evec tang x e
      = ∑ e, τ * ∑ a, (N e a * GtX sgn evec tang N x a) * Tx sgn evec tang x e :=
        Finset.sum_congr rfl (fun e _ => h1 e)
    _ = τ * ∑ e, ∑ a, (N e a * GtX sgn evec tang N x a) * Tx sgn evec tang x e := by
        rw [← Finset.mul_sum]
    _ = τ * ∑ a, ∑ e, (N e a * GtX sgn evec tang N x a) * Tx sgn evec tang x e := by
        rw [Finset.sum_comm]
    _ = τ * ∑ a, GtX sgn evec tang N x a * ∑ e, N e a * Tx sgn evec tang x e := by
        refine congrArg (fun t => τ * t) ?_
        exact Finset.sum_congr rfl (fun a _ => h2 a)

/-- **主定理（源第 29 行）**：`2 sum_j ⟪(Mx)_j, x_j • tangent_j⟫ = tau sum_a ((G^T x)_a)^2`。

纯有限和重排 ⇒ **不需要** `B N = 0`、不需要矩阵可逆、不需要正定、不需要 `H0`。 -/
theorem adaptive_cross_identity (sgn : κ → ι → ℝ) (evec : κ → Point) (tang : ι → Point)
    (N : κ → Fin 4 → ℝ) (τ : ℝ) (x : ι → ℝ) :
    2 * ∑ j, inner ℝ (Mx sgn evec tang N τ x j) (x j • tang j)
      = τ * ∑ a, (GtX sgn evec tang N x a) ^ 2 := by
  rw [two_M_eq sgn evec tang N τ x, sum_TQ_eq sgn evec tang N τ x,
    Qx_Tx_eq sgn evec tang N τ x]
  refine congrArg (fun t => τ * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [GtX_eq sgn evec tang N x a]
  ring

/-- 右端写成 `x^T G G^T x` 的显式形状（与源记号对齐）。 -/
theorem adaptive_cross_identity_quadform (sgn : κ → ι → ℝ) (evec : κ → Point)
    (tang : ι → Point) (N : κ → Fin 4 → ℝ) (τ : ℝ) (x : ι → ℝ) :
    2 * ∑ j, inner ℝ (Mx sgn evec tang N τ x j) (x j • tang j)
      = τ * ∑ a, GtX sgn evec tang N x a * GtX sgn evec tang N x a := by
  rw [adaptive_cross_identity sgn evec tang N τ x]
  refine congrArg (fun t => τ * t) ?_
  exact Finset.sum_congr rfl (fun a _ => by ring)

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.GtX_eq
#print axioms N11Formalization.FlashLocal.two_M_eq
#print axioms N11Formalization.FlashLocal.sum_TQ_eq
#print axioms N11Formalization.FlashLocal.Qx_Tx_eq
#print axioms N11Formalization.FlashLocal.adaptive_cross_identity
#print axioms N11Formalization.FlashLocal.adaptive_cross_identity_quadform
