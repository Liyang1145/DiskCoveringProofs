import Mathlib
import N11Formalization.Definitions
import N11Formalization.Conditional.RootSpec

/-!
# 源构型的显式构造（GUIDE §2 的「Rstar 定义必须形式化」+ 反 schema 漂移）

依据 `N11-GLOBAL-OPTIMALITY-THEOREM.md` §"Exact definition and an attaining configuration" 与
`team-current/lead/TC-ROOT-SOURCE-IDENTITY.md` 逐条转写：

```
z = (a0,a1,a2,a3,y0,y1,R),  a4 = π − 2(a0+a1+a2+a3),  a = (a0,a1,a2,a3,a4,a3,a2,a1,a0)
θ4 = 0,  θ_{k+1} − θ_k = a_k + a_{k+1}
ρ_k = cos a_k − sqrt(R² − sin² a_k)            （sqrt 取非负支）
C_k = ρ_k (cos θ_k, sin θ_k),   B_k = (cos(θ_k+a_k), sin(θ_k+a_k))
U_k = C_k + C_{k+1} − B_k,      H0 = (y0,0),  H1 = (y1,0)
f = (|U1−H1| − R, |U2−H0| − R, |U3−H0| − R, |U8−H1| − R, |W−C6| − R)
W = ((y0+y1)/2, sqrt(R² − ((y1−y0)/2)²))
F(u,λ) = (f(z), e_R − Df(z)ᵀλ),   u = (z,λ) ∈ ℝ¹²  ← **12 变量就是 (z,λ)**
```

**关键事实（防止对象漂移）**：C891 的「12 变量 TC/KKT 系统」的变量是 `u = (z, λ)`
（`z ∈ ℝ⁷`、乘子 `λ ∈ ℝ⁵`，见 `repair_tc_krawczyk.py` 的 `NZ=7, N=12` 与 `system`），
而 `Rstar` 是 `u` 的**零基第 6 坐标** = `z` 的第 7 个分量 `R`。
本文件把 `sys` 显式钉成 `TCSystem`，并给出源构型的 11 个中心 `centersOfRoot u`。

**真实等级**：本文件全部是**定义** + 定义层性质（kernel-proved，无条件）；
不含根存在性、不含覆盖性等任何数值/几何结论。
-/

noncomputable section

namespace N11Formalization

/-- 源文的九槽角向量 `a = (a0,a1,a2,a3,a4,a3,a2,a1,a0)`，其中 `a4 = π − 2(a0+a1+a2+a3)`。
只读 `u` 的前 4 个坐标（后 8 个坐标是乘子等，不参与几何）。 -/
def angleVec (u : Fin 12 → ℝ) : Fin 9 → ℝ :=
  ![u 0, u 1, u 2, u 3, Real.pi - 2 * (u 0 + u 1 + u 2 + u 3), u 3, u 2, u 1, u 0]

/-- 角坐标 `θ`：`θ₄ = 0` 且 `θ_{k+1} − θ_k = a_k + a_{k+1}`（按递推展开成显式有限和）。 -/
def thetaOf (A : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![ -((A 0 + A 1) + (A 1 + A 2) + (A 2 + A 3) + (A 3 + A 4)),
     -((A 1 + A 2) + (A 2 + A 3) + (A 3 + A 4)),
     -((A 2 + A 3) + (A 3 + A 4)),
     -(A 3 + A 4),
     0,
     A 4 + A 5,
     (A 4 + A 5) + (A 5 + A 6),
     (A 4 + A 5) + (A 5 + A 6) + (A 6 + A 7),
     (A 4 + A 5) + (A 5 + A 6) + (A 6 + A 7) + (A 7 + A 8) ]

theorem thetaOf_four (A : Fin 9 → ℝ) : thetaOf A 4 = 0 := rfl

/-- **递推定义的正确性**：`θ_{k+1} − θ_k = a_k + a_{k+1}`（k = 0..7），即本文件里的显式
有限和确实满足源文的递推。 -/
theorem thetaOf_rec (A : Fin 9 → ℝ) (k : Fin 8) :
    thetaOf A ⟨(k : ℕ) + 1, by omega⟩ - thetaOf A ⟨(k : ℕ), by omega⟩
      = A ⟨(k : ℕ), by omega⟩ + A ⟨(k : ℕ) + 1, by omega⟩ := by
  fin_cases k <;> simp [thetaOf]

/-- **九槽角和恒为 π**：`Σ_k a_k = π`（`a4 = π − 2(...)` 与回文结构的结果）。 -/
theorem sum_angleVec (u : Fin 12 → ℝ) : ∑ k, angleVec u k = Real.pi := by
  simp [angleVec, Fin.sum_univ_succ]
  ring

/-- 环盘径向坐标 `ρ_k = cos a_k − sqrt(R² − sin² a_k)`（`sqrt` 取非负支）。 -/
def rhoK (u : Fin 12 → ℝ) (k : Fin 9) : ℝ :=
  Real.cos (angleVec u k) - Real.sqrt ((u 6) ^ 2 - (Real.sin (angleVec u k)) ^ 2)

/-- 环盘中心 `C_k = ρ_k (cos θ_k, sin θ_k)`。 -/
def ringCenter (u : Fin 12 → ℝ) (k : Fin 9) : Point :=
  !₂[rhoK u k * Real.cos (thetaOf (angleVec u) k), rhoK u k * Real.sin (thetaOf (angleVec u) k)]

/-- 弧端点 `B_k = (cos(θ_k + a_k), sin(θ_k + a_k))`。 -/
def arcEnd (u : Fin 12 → ℝ) (k : Fin 9) : Point :=
  !₂[Real.cos (thetaOf (angleVec u) k + angleVec u k),
      Real.sin (thetaOf (angleVec u) k + angleVec u k)]

/-- `U_k = C_k + C_{k+1} − B_k`（下标按模 9）。 -/
def Uvec (u : Fin 12 → ℝ) (k : Fin 9) : Point :=
  ringCenter u k + ringCenter u (k + 1) - arcEnd u k

/-- 第一个 hub `H0 = (y0, 0)`。 -/
def hub0 (u : Fin 12 → ℝ) : Point := !₂[u 4, 0]

/-- 第二个 hub `H1 = (y1, 0)`。 -/
def hub1 (u : Fin 12 → ℝ) : Point := !₂[u 5, 0]

/-- 第五个残差的辅助点 `W = ((y0+y1)/2, sqrt(R² − ((y1−y0)/2)²))`。 -/
def wPoint (u : Fin 12 → ℝ) : Point :=
  !₂[(u 4 + u 5) / 2, Real.sqrt ((u 6) ^ 2 - ((u 5 - u 4) / 2) ^ 2)]

/-- 源文的五个残差 `f : ℝ⁷ → ℝ⁵`（只读 `u` 的前 7 个坐标）。
顺序与源文一致：`(U1,H1),(U2,H0),(U3,H0),(U8,H1)`，再加 `(W,C6)`。 -/
def residual (u : Fin 12 → ℝ) : Fin 5 → ℝ :=
  ![dist (Uvec u 1) (hub1 u) - u 6,
    dist (Uvec u 2) (hub0 u) - u 6,
    dist (Uvec u 3) (hub0 u) - u 6,
    dist (Uvec u 8) (hub1 u) - u 6,
    dist (wPoint u) (ringCenter u 6) - u 6]

/-- **源构型的 11 个中心**：9 个环盘中心 `C_0,…,C_8`（下标 0–8）+ 两个 hub `H0,H1`（下标 9,10）。 -/
def centersOfRoot (u : Fin 12 → ℝ) : Fin 11 → Point :=
  fun i =>
    if h : (i : ℕ) < 9 then ringCenter u ⟨i, h⟩
    else if (i : ℕ) = 9 then hub0 u
    else hub1 u

theorem centersOfRoot_ring (u : Fin 12 → ℝ) (k : Fin 9) :
    centersOfRoot u ⟨(k : ℕ), by omega⟩ = ringCenter u k := by
  simp [centersOfRoot]

theorem centersOfRoot_nine (u : Fin 12 → ℝ) : centersOfRoot u 9 = hub0 u := by
  simp [centersOfRoot]

theorem centersOfRoot_ten (u : Fin 12 → ℝ) : centersOfRoot u 10 = hub1 u := by
  simp [centersOfRoot]

/-! ## 12 变量 TC/KKT 系统（把 `sys` 显式钉住，消除 schema 漂移） -/

/-- 取 `u` 的前 7 个坐标。 -/
def first7 (u : Fin 12 → ℝ) : Fin 7 → ℝ := fun i => u ⟨(i : ℕ), by omega⟩

/-- 取 `u` 的后 5 个坐标（KKT 乘子 `λ`）。 -/
def last5 (u : Fin 12 → ℝ) : Fin 5 → ℝ := fun i => u ⟨(i : ℕ) + 7, by omega⟩

/-- `f` 看作 `ℝ⁷ → ℝ⁵` 的函数（后 5 个坐标置 0，不影响 `f`）。 -/
def residualFun (z : Fin 7 → ℝ) : Fin 5 → ℝ :=
  residual fun i : Fin 12 => if h : (i : ℕ) < 7 then z ⟨(i : ℕ), h⟩ else 0

/-- Euler–Lagrange 一阶条件的乘子块 `λ ↦ (∂f/∂z)ᵀ λ`。

用 `fderiv`（Fréchet 导数）而不是手工求导：**消掉手工导数与源表达式树漂移的可能**。 -/
def adjointBlock (z : Fin 7 → ℝ) (lam : Fin 5 → ℝ) : Fin 7 → ℝ :=
  fun i => ∑ k : Fin 5, lam k * (fderiv ℝ residualFun z (Pi.single i 1)) k

/-- **12 变量 TC/KKT 系统**：`F(u) = (f(z), e_R − (∂f/∂z)ᵀλ)`，
变量 `u = (a0,a1,a2,a3,y0,y1,R,λ0,…,λ4) ∈ ℝ¹²`，`Rstar` 是其零基第 6 坐标。

**指标对应（易错处，务必显式）**：源文是
`F = f ++ [e_R[i] − Σ_k λ_k (∂f_k/∂z_i) | i ∈ range 7]`，其中 `e_R[i] = δ_{i,6}`
是 **z 指标**下的单位向量（`R` 是 z 的零基第 6 个分量）。
所以在这个 12 维向量里，前 5 个分量是 `f`；其余分量下标 `j = 5 + i`（`i` 为 z 指标 0…6），
而 `e_R` 的 `1` 落在 `j = 5 + 6 = 11`，**不是** `j = 6`。 -/
def TCSystem (u : Fin 12 → ℝ) : Fin 12 → ℝ :=
  fun i =>
    if h : (i : ℕ) < 5 then residual u ⟨(i : ℕ), h⟩
    else ((if (i : ℕ) = 11 then (1 : ℝ) else 0) - adjointBlock (first7 u) (last5 u) ⟨(i : ℕ) - 5, by omega⟩)

/-- **指标绑定的独立读数**：`e_R` 位于 **F 下标 11**（= z 下标 6 = `R`）。
把 z 指标与 F 指标混用就会把 `1` 放到 F 下标 6 —— 这是本文件修正过的一处转写漂移。 -/
theorem TCSystem_eR_at_eleven (u : Fin 12 → ℝ) :
    TCSystem u 11 = 1 - adjointBlock (first7 u) (last5 u) 6 := by
  simp [TCSystem]

/-- 对照：F 下标 6 属于乘子块（对应 z 下标 1），其 `e_R` 分量为 `0`。 -/
theorem TCSystem_six_no_eR (u : Fin 12 → ℝ) :
    TCSystem u 6 = 0 - adjointBlock (first7 u) (last5 u) 1 := by
  simp [TCSystem]

/-- 前 5 个分量就是源文的 `f`。 -/
theorem TCSystem_first (u : Fin 12 → ℝ) (i : Fin 5) :
    TCSystem u ⟨(i : ℕ), by omega⟩ = residual u ⟨(i : ℕ), by omega⟩ := by
  simp [TCSystem]

/-- **源构型的 11 中心是覆盖对象**：C892 的精确目标（不再是抽象 `∃ c`）。 -/
def C892Attainment (S : C891RootSpec) : Prop :=
  Covers (centersOfRoot S.root) (Rstar S)

/-- **用显式 `TCSystem` 实例化 C891 规格**：盒内存在唯一根即得 `C891RootSpec`，
此时 `sys` 被钉成源文的 TC/KKT 系统（不再是任意函数字段）。 -/
def tcRootSpec (boxLo boxHi : Fin 12 → ℚ)
    (h : ∃! z : Fin 12 → ℝ,
      (∀ i : Fin 12, (boxLo i : ℝ) ≤ z i ∧ z i ≤ (boxHi i : ℝ)) ∧ TCSystem z = 0) :
    C891RootSpec where
  sys := TCSystem
  boxLo := boxLo
  boxHi := boxHi
  exists_unique := h
  radiusIndex := 6

/-- **条件主定理（C892 对象已固定）**：只差
(1) 盒内 `∃!`（G1）、(2) `C892Attainment`（G2）、(3) 下界（G3）。 -/
theorem n11_main_of_C892 (S : C891RootSpec) (h892 : C892Attainment S)
    (hbound : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → Rstar S ≤ r) :
    N11MainStatement (Rstar S) :=
  n11_main_conditional S ⟨centersOfRoot S.root, h892⟩ hbound

end N11Formalization

