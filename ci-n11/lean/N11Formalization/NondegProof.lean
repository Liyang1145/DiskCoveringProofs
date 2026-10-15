/-
# `Precond` 七条非退化条件 `hnd*` 的**证明**（证书盒 `B = closedBall certCR rhoCertR` 上）

## 本条要证什么

`Precond.TCSystem_unique_root_of_full_data` 的前提清单里有七条**不依赖** `D`/`Jt` 的非退化条件
（全部在证书盒 `B = Metric.closedBall certCR rhoCertR` 上），本文件把它们**在内核里证出来**：

| # | 条件 | 本文件定理 | 类型 |
|---|---|---|---|
| 1 | `(x 6)^2 - sin²(angleVec x j) ≠ 0`（9 条） | `nd_hndRho` | 标量型 |
| 2 | `(x 6)^2 - ((x 5 - x 4)/2)^2 ≠ 0` | `nd_hndW` | 标量型（纯有理） |
| 3 | `Uvec x 1 ≠ hub1 x` | `nd_hndU1` | 点分离型 |
| 4 | `Uvec x 2 ≠ hub0 x` | `nd_hndU2` | 点分离型 |
| 5 | `Uvec x 3 ≠ hub0 x` | `nd_hndU3` | 点分离型 |
| 6 | `Uvec x 8 ≠ hub1 x` | `nd_hndU8` | 点分离型 |
| 7 | `wPoint x ≠ ringCenter x 6` | `nd_hndWp` | 点分离型 |

## 证明路线（值侧区间求值 + 非零/不相等接口）

* **标的物**：`Point = EuclideanSpace ℝ (Fin 2)`；角度 = 弧度；盒端点 = **精确有理数**
  （`boxLoCert`/`boxHiCert`，分母 `2^82`），无宿主浮点参与任何端点。
* **盒**：`ndBox i = ⟨boxLoCert i, boxHiCert i⟩`，`ndBox_mem` 由 `mem_closedBall_cert_iff` 给出
  「球口径 ⇒ 逐坐标盒口径」。
* **逐节点镜像表达式树**：`ndAngleBox`（`angleVec`）、`thetaInterval`（已有，`thetaOf`）、
  `ndRhoBox`（`rhoK`）、`ndRingBox`（`ringCenter`）、`ndArcBox`（`arcEnd`）、`ndUvecBox`（`Uvec`）、
  `ndHub0Box`/`ndHub1Box`（`hub0`/`hub1`）、`ndWPointBox`（`wPoint`）；
  每层给出 `*_mem` 包含性（由 `RatInterval.*_mem` 组合）。
* **三角算子**：用 `ResidualIntervalLag` 的**相位归约**算子 `sinTotLag`/`cosTotLag`
  （阶乘余项 `|q|^29/29!`、`|q|^28/28!`，**任何角度**都可用；窗内逐格钉住，窗外保守回退）。
  证书盒上 `θ_k` 的模达 `2.77 > 1`，故**不能**直接用窗外回退的 `sinIHighLag`/`cosIHighLag`。
* **收口**：
  - 标量型：`I.Mem g ∧ 0 < I.lo ⇒ g ≠ 0`（`NondegInterface.ne_zero_of_pos_lo`）；
  - 点分离型：`A.Mem x ∧ B.Mem y ∧ a ≤ A.lo − B.hi ∧ 0 < a ⇒ a ≤ |x − y|`
    （本文件 `le_abs_sub_of_lo_sub_hi`，及其 A/B 互换版），再经 `point_ne_of_coord`
    （某一坐标分离 ⇒ 两点不等）落到 `Point` 级不等。
    五条点分离**各用单坐标**（逐条下界见 §5 表），下界全取 `1/10`，余量 ≥ 2.2 倍。
* **读数**：§5 的 `nd*_read` 全是 `norm_num` 在**精确有理端点**上做的内核判定
  （`0 < I.lo` / `a ≤ ·`），**没有任何外部数值表当端点来源**。

## 与外部数值件的关系（口径，勿误读）

`evidence/interval-ad/nd_bounds.out.txt`（C1070，经 box-rstar 第二条独立路径 C1100 复核）
的七条下界**是参照、不是证明**。本文件的读数与它**独立**：端点全部由 Lean 的区间算子算出，
数值一致性只能作为**发现错误**的手段。本件复算的盒上下界与该参照的十进制读数逐条一致
（`hndRho` 最紧 `j=4`、`hndW`、五条点分离 ≈ `3.7998e-1` 量级），见 `evidence/hnd-lean/`。

## 实现注意（踩过的坑）

* `![...] i`（`Matrix.vecCons` 数组）对**具体下标** `norm_num`/`simp` **不归约**
  （`(6 : Fin 12)` 是 `OfNat` 实例项，不是 `⟨6, ⋯⟩`）⇒ 盒端点用 **`rfl` 证明的下标等式**
  `ndBoxLo_i`/`ndBoxHi_i` 送进 `norm_num` 的引理表（写错字面量 ⇒ `rfl` 立刻失败，自检）。
* `Fin` **字面量模式匹配**的 `def`（`ndAngleBox q | 0 => ...`）反而**可以**被 `norm_num` 展开。
* `(k + 1 : Fin 9)` 与字面量下标**不是** defeq，需 `by decide` 的后继等式（`nd_fin_succ_*`）。
* 相位归约的窗口是 `[-1,1]`（`sinIHighLag`/`cosWinLag` 同窗口，`cosWinLag` 用 `highAbs`/`lowAbs`
  取紧端点），`inWindow` 恰好保证**约化后**的盒落在窗内 ⇒ 无回退、无精度塌陷。

## 真实等级

**kernel-proved，无条件**（无 `sorry`、无自定义 `axiom`、无 `native_decide`）。
作用域：证书盒 `closedBall certCR rhoCertR` 上的**全称**断言（不是单点读数）。
-/
import N11Formalization.BoxRstar
import N11Formalization.ResidualIntervalLag
import N11Formalization.NondegInterface

noncomputable section

namespace N11Formalization

open RatInterval

/-! ## 0. 证书盒与盒成员 -/

/-- 证书盒：逐坐标的**精确有理**区间 `[boxLoCert i, boxHiCert i]`（半宽 = `rhoCert`）。 -/
def ndBox : Fin 12 → RatInterval := fun i => ⟨boxLoCert i, boxHiCert i⟩

/-- **球口径 ⇒ 盒口径**（逐坐标成员）。 -/
theorem ndBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) (i : Fin 12) :
    (ndBox i).Mem (x i) :=
  RatInterval.mem_iff.mpr ((mem_closedBall_cert_iff (x := x)).mp hx i)

/-! ## 1. 盒端点的下标等式（`rfl` 自检：字面量写错即编译失败） -/

theorem ndBoxLo_0 : boxLoCert 0 = 1798923298417342433274219 / 2 ^ 82 := rfl
theorem ndBoxLo_1 : boxLoCert 1 = 1648215922234750999800171 / 2 ^ 82 := rfl
theorem ndBoxLo_2 : boxLoCert 2 = 1357971481365603998574955 / 2 ^ 82 := rfl
theorem ndBoxLo_3 : boxLoCert 3 = 1852132483251062452070763 / 2 ^ 82 := rfl
theorem ndBoxLo_4 : boxLoCert 4 = 1320038024120705549412715 / 2 ^ 82 := rfl
theorem ndBoxLo_5 : boxLoCert 5 = -722591886991921657599637 / 2 ^ 82 := rfl
theorem ndBoxLo_6 : boxLoCert 6 = 1837489159457200081021291 / 2 ^ 82 := rfl
theorem ndBoxLo_7 : boxLoCert 7 = -550469530967087572768405 / 2 ^ 82 := rfl
theorem ndBoxLo_8 : boxLoCert 8 = -123900825917530290181781 / 2 ^ 82 := rfl
theorem ndBoxLo_9 : boxLoCert 9 = -32135004506949125854869 / 2 ^ 82 := rfl
theorem ndBoxLo_10 : boxLoCert 10 = -95985936781297890809493 / 2 ^ 82 := rfl
theorem ndBoxLo_11 : boxLoCert 11 = -127714233188113900295829 / 2 ^ 82 := rfl

theorem ndBoxHi_0 : boxHiCert 0 = 1798923308088748990191253 / 2 ^ 82 := rfl
theorem ndBoxHi_1 : boxHiCert 1 = 1648215931906157556717205 / 2 ^ 82 := rfl
theorem ndBoxHi_2 : boxHiCert 2 = 1357971491037010555491989 / 2 ^ 82 := rfl
theorem ndBoxHi_3 : boxHiCert 3 = 1852132492922469008987797 / 2 ^ 82 := rfl
theorem ndBoxHi_4 : boxHiCert 4 = 1320038033792112106329749 / 2 ^ 82 := rfl
theorem ndBoxHi_5 : boxHiCert 5 = -722591877320515100682603 / 2 ^ 82 := rfl
theorem ndBoxHi_6 : boxHiCert 6 = 1837489169128606637938325 / 2 ^ 82 := rfl
theorem ndBoxHi_7 : boxHiCert 7 = -550469521295681015851371 / 2 ^ 82 := rfl
theorem ndBoxHi_8 : boxHiCert 8 = -123900816246123733264747 / 2 ^ 82 := rfl
theorem ndBoxHi_9 : boxHiCert 9 = -32134994835542568937835 / 2 ^ 82 := rfl
theorem ndBoxHi_10 : boxHiCert 10 = -95985927109891333892459 / 2 ^ 82 := rfl
theorem ndBoxHi_11 : boxHiCert 11 = -127714223516707343378795 / 2 ^ 82 := rfl

/-! ## 2. 盒版 `angleVec` 与其分支展开引理 -/

/-- `angleVec` 的**盒版**（逐槽镜像，`a4 = π − 2(a0+a1+a2+a3)` 用 `piI`）。 -/
def ndAngleBox (Q : Fin 12 → RatInterval) : Fin 9 → RatInterval
  | 0 => Q 0
  | 1 => Q 1
  | 2 => Q 2
  | 3 => Q 3
  | 4 => sub piI (mul (ofRat 2) (add (add (add (Q 0) (Q 1)) (Q 2)) (Q 3)))
  | 5 => Q 3
  | 6 => Q 2
  | 7 => Q 1
  | 8 => Q 0

theorem ndAngleBox_0 (Q : Fin 12 → RatInterval) : ndAngleBox Q 0 = Q 0 := rfl
theorem ndAngleBox_1 (Q : Fin 12 → RatInterval) : ndAngleBox Q 1 = Q 1 := rfl
theorem ndAngleBox_2 (Q : Fin 12 → RatInterval) : ndAngleBox Q 2 = Q 2 := rfl
theorem ndAngleBox_3 (Q : Fin 12 → RatInterval) : ndAngleBox Q 3 = Q 3 := rfl
theorem ndAngleBox_4 (Q : Fin 12 → RatInterval) :
    ndAngleBox Q 4 = sub piI (mul (ofRat 2) (add (add (add (Q 0) (Q 1)) (Q 2)) (Q 3))) := rfl
theorem ndAngleBox_5 (Q : Fin 12 → RatInterval) : ndAngleBox Q 5 = Q 3 := rfl
theorem ndAngleBox_6 (Q : Fin 12 → RatInterval) : ndAngleBox Q 6 = Q 2 := rfl
theorem ndAngleBox_7 (Q : Fin 12 → RatInterval) : ndAngleBox Q 7 = Q 1 := rfl
theorem ndAngleBox_8 (Q : Fin 12 → RatInterval) : ndAngleBox Q 8 = Q 0 := rfl

/-- `angleVec` 的盒包含性（逐槽 `exact`，靠 `rfl` 级 defeq 归约 `![...] i`）。 -/
theorem ndAngleBox_mem {Q : Fin 12 → RatInterval} {x : Fin 12 → ℝ}
    (hQ : ∀ i, (Q i).Mem (x i)) (k : Fin 9) : (ndAngleBox Q k).Mem (angleVec x k) := by
  fin_cases k
  · exact hQ 0
  · exact hQ 1
  · exact hQ 2
  · exact hQ 3
  · exact sub_mem piI_mem
      (mul_mem (ofRat_mem (2 : ℚ))
        (add_mem (add_mem (add_mem (hQ 0) (hQ 1)) (hQ 2)) (hQ 3)))
  · exact hQ 3
  · exact hQ 2
  · exact hQ 1
  · exact hQ 0

/-! ## 3. 几何构件的盒版 + 包含性 -/

/-- `rhoK` 的盒版：`cos a_k − √((x6)² − sin² a_k)`。 -/
def ndRhoBox (Q : Fin 12 → RatInterval) (k : Fin 9) : RatInterval :=
  sub (cosTotLag (ndAngleBox Q k))
    (sqrt (sub (sq (Q 6)) (sq (sinTotLag (ndAngleBox Q k)))))

theorem ndRhoBox_mem {Q : Fin 12 → RatInterval} {x : Fin 12 → ℝ}
    (hQ : ∀ i, (Q i).Mem (x i)) (k : Fin 9) : (ndRhoBox Q k).Mem (rhoK x k) := by
  rw [rhoK_eq]
  exact sub_mem (cosTotLag_mem (ndAngleBox_mem hQ k))
    (sqrt_mem (sub_mem (sq_mem_pow (hQ 6)) (sq_mem_pow (sinTotLag_mem (ndAngleBox_mem hQ k)))))

/-- `ringCenter` 的盒版（逐坐标）。 -/
def ndRingBox (Q : Fin 12 → RatInterval) (k : Fin 9) : Fin 2 → RatInterval
  | 0 => mul (ndRhoBox Q k) (cosTotLag (thetaInterval (ndAngleBox Q) k))
  | 1 => mul (ndRhoBox Q k) (sinTotLag (thetaInterval (ndAngleBox Q) k))

/-- `arcEnd` 的盒版（逐坐标）。 -/
def ndArcBox (Q : Fin 12 → RatInterval) (k : Fin 9) : Fin 2 → RatInterval
  | 0 => cosTotLag (add (thetaInterval (ndAngleBox Q) k) (ndAngleBox Q k))
  | 1 => sinTotLag (add (thetaInterval (ndAngleBox Q) k) (ndAngleBox Q k))

/-- `Uvec` 的盒版（逐坐标，`k+1` 取 `Fin 9` 加法）。 -/
def ndUvecBox (Q : Fin 12 → RatInterval) (k : Fin 9) : Fin 2 → RatInterval
  | 0 => sub (add ((ndRingBox Q k) 0) ((ndRingBox Q (k + 1)) 0)) ((ndArcBox Q k) 0)
  | 1 => sub (add ((ndRingBox Q k) 1) ((ndRingBox Q (k + 1)) 1)) ((ndArcBox Q k) 1)

/-- `hub0 = (x4, 0)` 的盒版。 -/
def ndHub0Box (Q : Fin 12 → RatInterval) : Fin 2 → RatInterval
  | 0 => Q 4
  | 1 => ofRat 0

/-- `hub1 = (x5, 0)` 的盒版。 -/
def ndHub1Box (Q : Fin 12 → RatInterval) : Fin 2 → RatInterval
  | 0 => Q 5
  | 1 => ofRat 0

/-- `wPoint` 的盒版。 -/
def ndWPointBox (Q : Fin 12 → RatInterval) : Fin 2 → RatInterval
  | 0 => mul (ofRat (1 / 2)) (add (Q 4) (Q 5))
  | 1 => sqrt (sub (sq (Q 6)) (sq (mul (ofRat (1 / 2)) (sub (Q 5) (Q 4)))))

theorem ndRingBox_0 (Q : Fin 12 → RatInterval) (k : Fin 9) :
    ndRingBox Q k 0 = mul (ndRhoBox Q k) (cosTotLag (thetaInterval (ndAngleBox Q) k)) := rfl
theorem ndRingBox_1 (Q : Fin 12 → RatInterval) (k : Fin 9) :
    ndRingBox Q k 1 = mul (ndRhoBox Q k) (sinTotLag (thetaInterval (ndAngleBox Q) k)) := rfl
theorem ndArcBox_0 (Q : Fin 12 → RatInterval) (k : Fin 9) :
    ndArcBox Q k 0 = cosTotLag (add (thetaInterval (ndAngleBox Q) k) (ndAngleBox Q k)) := rfl
theorem ndArcBox_1 (Q : Fin 12 → RatInterval) (k : Fin 9) :
    ndArcBox Q k 1 = sinTotLag (add (thetaInterval (ndAngleBox Q) k) (ndAngleBox Q k)) := rfl
theorem ndUvecBox_0 (Q : Fin 12 → RatInterval) (k : Fin 9) :
    ndUvecBox Q k 0 = sub (add ((ndRingBox Q k) 0) ((ndRingBox Q (k + 1)) 0))
      ((ndArcBox Q k) 0) := rfl
theorem ndUvecBox_1 (Q : Fin 12 → RatInterval) (k : Fin 9) :
    ndUvecBox Q k 1 = sub (add ((ndRingBox Q k) 1) ((ndRingBox Q (k + 1)) 1))
      ((ndArcBox Q k) 1) := rfl
theorem ndHub0Box_0 (Q : Fin 12 → RatInterval) : ndHub0Box Q 0 = Q 4 := rfl
theorem ndHub0Box_1 (Q : Fin 12 → RatInterval) : ndHub0Box Q 1 = ofRat 0 := rfl
theorem ndHub1Box_0 (Q : Fin 12 → RatInterval) : ndHub1Box Q 0 = Q 5 := rfl
theorem ndHub1Box_1 (Q : Fin 12 → RatInterval) : ndHub1Box Q 1 = ofRat 0 := rfl
theorem ndWPointBox_0 (Q : Fin 12 → RatInterval) :
    ndWPointBox Q 0 = mul (ofRat (1 / 2)) (add (Q 4) (Q 5)) := rfl
theorem ndWPointBox_1 (Q : Fin 12 → RatInterval) :
    ndWPointBox Q 1 = sqrt (sub (sq (Q 6)) (sq (mul (ofRat (1 / 2)) (sub (Q 5) (Q 4))))) := rfl

theorem ndRingBox_mem {Q : Fin 12 → RatInterval} {x : Fin 12 → ℝ}
    (hQ : ∀ i, (Q i).Mem (x i)) (k : Fin 9) (i : Fin 2) :
    (ndRingBox Q k i).Mem ((ringCenter x k).ofLp i) := by
  fin_cases i
  · show (mul (ndRhoBox Q k) (cosTotLag (thetaInterval (ndAngleBox Q) k))).Mem
      ((ringCenter x k).ofLp 0)
    rw [ringCenter_coord0]
    exact mul_mem (ndRhoBox_mem hQ k)
      (cosTotLag_mem (thetaInterval_mem (ndAngleBox_mem hQ) k))
  · show (mul (ndRhoBox Q k) (sinTotLag (thetaInterval (ndAngleBox Q) k))).Mem
      ((ringCenter x k).ofLp 1)
    rw [ringCenter_coord1]
    exact mul_mem (ndRhoBox_mem hQ k)
      (sinTotLag_mem (thetaInterval_mem (ndAngleBox_mem hQ) k))

theorem ndArcBox_mem {Q : Fin 12 → RatInterval} {x : Fin 12 → ℝ}
    (hQ : ∀ i, (Q i).Mem (x i)) (k : Fin 9) (i : Fin 2) :
    (ndArcBox Q k i).Mem ((arcEnd x k).ofLp i) := by
  fin_cases i
  · show (cosTotLag (add (thetaInterval (ndAngleBox Q) k) (ndAngleBox Q k))).Mem
      ((arcEnd x k).ofLp 0)
    rw [arcEnd_coord0]
    exact cosTotLag_mem (add_mem (thetaInterval_mem (ndAngleBox_mem hQ) k) (ndAngleBox_mem hQ k))
  · show (sinTotLag (add (thetaInterval (ndAngleBox Q) k) (ndAngleBox Q k))).Mem
      ((arcEnd x k).ofLp 1)
    rw [arcEnd_coord1]
    exact sinTotLag_mem (add_mem (thetaInterval_mem (ndAngleBox_mem hQ) k) (ndAngleBox_mem hQ k))

theorem ndUvecBox_mem {Q : Fin 12 → RatInterval} {x : Fin 12 → ℝ}
    (hQ : ∀ i, (Q i).Mem (x i)) (k : Fin 9) (i : Fin 2) :
    (ndUvecBox Q k i).Mem ((Uvec x k).ofLp i) := by
  fin_cases i
  · show (sub (add ((ndRingBox Q k) 0) ((ndRingBox Q (k + 1)) 0)) ((ndArcBox Q k) 0)).Mem
      ((Uvec x k).ofLp 0)
    rw [Uvec_coord0]
    exact sub_mem (add_mem (ndRingBox_mem hQ k 0) (ndRingBox_mem hQ (k + 1) 0))
      (ndArcBox_mem hQ k 0)
  · show (sub (add ((ndRingBox Q k) 1) ((ndRingBox Q (k + 1)) 1)) ((ndArcBox Q k) 1)).Mem
      ((Uvec x k).ofLp 1)
    rw [Uvec_coord1]
    exact sub_mem (add_mem (ndRingBox_mem hQ k 1) (ndRingBox_mem hQ (k + 1) 1))
      (ndArcBox_mem hQ k 1)

theorem ndHub0Box_mem {Q : Fin 12 → RatInterval} {x : Fin 12 → ℝ}
    (hQ : ∀ i, (Q i).Mem (x i)) (i : Fin 2) : (ndHub0Box Q i).Mem ((hub0 x).ofLp i) := by
  fin_cases i
  · show (Q 4).Mem ((hub0 x).ofLp 0)
    rw [hub0_coord0]
    exact hQ 4
  · show (ofRat 0).Mem ((hub0 x).ofLp 1)
    rw [hub0_coord1]
    simpa using ofRat_mem (0 : ℚ)

theorem ndHub1Box_mem {Q : Fin 12 → RatInterval} {x : Fin 12 → ℝ}
    (hQ : ∀ i, (Q i).Mem (x i)) (i : Fin 2) : (ndHub1Box Q i).Mem ((hub1 x).ofLp i) := by
  fin_cases i
  · show (Q 5).Mem ((hub1 x).ofLp 0)
    rw [hub1_coord0]
    exact hQ 5
  · show (ofRat 0).Mem ((hub1 x).ofLp 1)
    rw [hub1_coord1]
    simpa using ofRat_mem (0 : ℚ)

theorem ndWPointBox_mem {Q : Fin 12 → RatInterval} {x : Fin 12 → ℝ}
    (hQ : ∀ i, (Q i).Mem (x i)) (i : Fin 2) : (ndWPointBox Q i).Mem ((wPoint x).ofLp i) := by
  fin_cases i
  · show (mul (ofRat (1 / 2)) (add (Q 4) (Q 5))).Mem ((wPoint x).ofLp 0)
    rw [wPoint_coord0]
    have h : ((x 4 + x 5) / 2) = (((1 / 2 : ℚ) : ℝ) * (x 4 + x 5)) := by push_cast; ring
    rw [h]
    exact mul_mem (ofRat_mem (1 / 2)) (add_mem (hQ 4) (hQ 5))
  · show (sqrt (sub (sq (Q 6)) (sq (mul (ofRat (1 / 2)) (sub (Q 5) (Q 4)))))).Mem
      ((wPoint x).ofLp 1)
    rw [wPoint_coord1]
    have h : (((x 5 - x 4) / 2)) = (((1 / 2 : ℚ) : ℝ) * (x 5 - x 4)) := by push_cast; ring
    rw [h]
    exact sqrt_mem (sub_mem (sq_mem_pow (hQ 6))
      (sq_mem_pow (mul_mem (ofRat_mem (1 / 2)) (sub_mem (hQ 5) (hQ 4)))))

/-! ## 4. 非零/不相等接口（本文件的纯序引理） -/

/-- **坐标差下界（一侧）**：`x ∈ A`、`y ∈ B`、`A.lo − B.hi ≥ a ≥ 0` ⟹ `a ≤ |x − y|`。 -/
theorem le_abs_sub_of_lo_sub_hi {A B : RatInterval} {x y : ℝ} {a : ℚ}
    (hA : A.Mem x) (hB : B.Mem y) (ha : 0 ≤ a) (h : a ≤ A.lo - B.hi) :
    (a : ℝ) ≤ |x - y| := by
  have hx : (A.lo : ℝ) ≤ x := mem_lo_le hA
  have hy : y ≤ (B.hi : ℝ) := mem_le_hi hB
  have h1 : (((A.lo - B.hi : ℚ)) : ℝ) ≤ x - y := by push_cast; linarith
  have h2 : (a : ℝ) ≤ x - y := le_trans (by exact_mod_cast h) h1
  have h3 : (0 : ℝ) ≤ x - y := le_trans (by exact_mod_cast ha) h2
  rwa [abs_of_nonneg h3]

/-- **坐标差下界（另一侧）**：`B.lo − A.hi ≥ a ≥ 0` ⟹ `a ≤ |x − y|`。 -/
theorem le_abs_sub_of_lo_sub_hi' {A B : RatInterval} {x y : ℝ} {a : ℚ}
    (hA : A.Mem x) (hB : B.Mem y) (ha : 0 ≤ a) (h : a ≤ B.lo - A.hi) :
    (a : ℝ) ≤ |x - y| := by
  have hx : x ≤ (A.hi : ℝ) := mem_le_hi hA
  have hy : (B.lo : ℝ) ≤ y := mem_lo_le hB
  have h1 : (((B.lo - A.hi : ℚ)) : ℝ) ≤ y - x := by push_cast; linarith
  have h2 : (a : ℝ) ≤ y - x := le_trans (by exact_mod_cast h) h1
  have h3 : (0 : ℝ) ≤ y - x := le_trans (by exact_mod_cast ha) h2
  rw [abs_sub_comm, abs_of_nonneg h3]
  exact h2

/-- **点分离**：某一坐标的绝对差有严格正下界 ⟹ 两点不等。 -/
theorem point_ne_of_coord {p q : Point} {i : Fin 2} {a : ℚ} (ha : 0 < a)
    (h : (a : ℝ) ≤ |p.ofLp i - q.ofLp i|) : p ≠ q := by
  intro hpq
  have h1 : p.ofLp i = q.ofLp i := congrArg (fun p : Point => p.ofLp i) hpq
  rw [h1, sub_self, abs_zero] at h
  have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  linarith

/-! ## 5. 读数（`norm_num` 在精确有理端点上的内核判定） -/

/-- `Fin` 后继（`Fin` 字面量加法不是 defeq）。 -/
theorem nd_fin_succ_0 : ((0 : Fin 9) + 1) = 1 := by decide
theorem nd_fin_succ_1 : ((1 : Fin 9) + 1) = 2 := by decide
theorem nd_fin_succ_2 : ((2 : Fin 9) + 1) = 3 := by decide
theorem nd_fin_succ_3 : ((3 : Fin 9) + 1) = 4 := by decide
theorem nd_fin_succ_5 : ((5 : Fin 9) + 1) = 6 := by decide
theorem nd_fin_succ_6 : ((6 : Fin 9) + 1) = 7 := by decide
theorem nd_fin_succ_7 : ((7 : Fin 9) + 1) = 8 := by decide
theorem nd_fin_succ_8 : ((8 : Fin 9) + 1) = 0 := by decide

/-- **求值宏**：区间构件 + 相位归约三角算子 + 下标展开引理的全表。 -/
macro "nd_eval" : tactic =>
  `(tactic| norm_num [ndBox,
        ndBoxLo_0, ndBoxLo_1, ndBoxLo_2, ndBoxLo_3, ndBoxLo_4, ndBoxLo_5, ndBoxLo_6,
        ndBoxLo_7, ndBoxLo_8, ndBoxLo_9, ndBoxLo_10, ndBoxLo_11,
        ndBoxHi_0, ndBoxHi_1, ndBoxHi_2, ndBoxHi_3, ndBoxHi_4, ndBoxHi_5, ndBoxHi_6,
        ndBoxHi_7, ndBoxHi_8, ndBoxHi_9, ndBoxHi_10, ndBoxHi_11,
        ndAngleBox_0, ndAngleBox_1, ndAngleBox_2, ndAngleBox_3, ndAngleBox_4, ndAngleBox_5,
        ndAngleBox_6, ndAngleBox_7, ndAngleBox_8,
        ndRingBox_0, ndRingBox_1, ndArcBox_0, ndArcBox_1, ndUvecBox_0, ndUvecBox_1,
        ndHub0Box_0, ndHub0Box_1, ndHub1Box_0, ndHub1Box_1, ndWPointBox_0, ndWPointBox_1,
        nd_fin_succ_0, nd_fin_succ_1, nd_fin_succ_2, nd_fin_succ_3, nd_fin_succ_5,
        nd_fin_succ_6, nd_fin_succ_7, nd_fin_succ_8,
        ndRhoBox, ndRingBox, ndArcBox, ndUvecBox, ndHub0Box, ndHub1Box, ndWPointBox,
        piI, piLo, piHi,
        sinTotLag, cosTotLag, phaseOf, phaseRedLag, phaseBothLag, phasePosLag, phaseNegLag, inWindow,
        reducedBox, halfPiLo, halfPiHi, sinIHighLag, cosWinLag, sinLoNLag, sinHiNLag, cosLoNLag, cosHiNLag,
        sinTQ, cosTQ, Finset.sum_range_succ, Finset.sum_range_zero, lowAbs, highAbs, Int.toNat,
        thetaInterval, intv, RatInterval.sub, RatInterval.add, RatInterval.mul, RatInterval.neg, ofRat,
        RatInterval.sq, RatInterval.sqrt, sqrtLo, sqrtHi])

/-- **`hndW` 读数**：`(x6)² − ((x5−x4)/2)²` 在盒上的区间下界 `> 0`（纯有理，无三角）。 -/
theorem ndW_read : (0 : ℚ) <
    (sub (sq (ndBox 6)) (sq (mul (ofRat (1 / 2)) (sub (ndBox 5) (ndBox 4))))).lo := by
  nd_eval

/-- **`hndRho` 读数（逐 `j`）**：`(x6)² − sin²(angleVec · j)` 在盒上的区间下界 `> 0`。
逐条字面量下标（`Fin` 字面量模式匹配的 `def` 对字面量下标可展开），再由 `ndRho_read` 打包。 -/
theorem ndRho_read_0 : (0 : ℚ) <
    (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 0)))).lo := by nd_eval

theorem ndRho_read_1 : (0 : ℚ) <
    (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 1)))).lo := by nd_eval

theorem ndRho_read_2 : (0 : ℚ) <
    (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 2)))).lo := by nd_eval

theorem ndRho_read_3 : (0 : ℚ) <
    (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 3)))).lo := by nd_eval

theorem ndRho_read_4 : (0 : ℚ) <
    (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 4)))).lo := by nd_eval

theorem ndRho_read_5 : (0 : ℚ) <
    (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 5)))).lo := by nd_eval

theorem ndRho_read_6 : (0 : ℚ) <
    (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 6)))).lo := by nd_eval

theorem ndRho_read_7 : (0 : ℚ) <
    (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 7)))).lo := by nd_eval

theorem ndRho_read_8 : (0 : ℚ) <
    (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 8)))).lo := by nd_eval

/-- **`hndRho` 读数（9 条打包）**。 -/
theorem ndRho_read : ∀ j : Fin 9,
    (0 : ℚ) < (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox j)))).lo := by
  intro j
  fin_cases j
  · exact ndRho_read_0
  · exact ndRho_read_1
  · exact ndRho_read_2
  · exact ndRho_read_3
  · exact ndRho_read_4
  · exact ndRho_read_5
  · exact ndRho_read_6
  · exact ndRho_read_7
  · exact ndRho_read_8

/-- **`hndU1` 读数**：`Uvec · 1` 的第二坐标上界 `≤ −1/10`（`hub1` 的第二坐标恒为 `0`）。 -/
theorem ndU1_read : ((1 / 10 : ℚ)) ≤ -((ndUvecBox ndBox 1 1).hi) := by nd_eval

/-- **`hndU2` 读数**。 -/
theorem ndU2_read : ((1 / 10 : ℚ)) ≤ -((ndUvecBox ndBox 2 1).hi) := by nd_eval

/-- **`hndU3` 读数**。 -/
theorem ndU3_read : ((1 / 10 : ℚ)) ≤ -((ndUvecBox ndBox 3 1).hi) := by nd_eval

/-- **`hndU8` 读数**：第一坐标方向（`Uvec · 8` 与 `hub1` 的第一坐标差）。 -/
theorem ndU8_read : ((1 / 10 : ℚ)) ≤ (ndHub1Box ndBox 0).lo - (ndUvecBox ndBox 8 0).hi := by
  nd_eval

/-- **`hndWp` 读数**：第二坐标方向（`wPoint` 在下、`ringCenter · 6` 在上）。 -/
theorem ndWp_read : ((1 / 10 : ℚ)) ≤
    (ndRingBox ndBox 6 1).lo - (ndWPointBox ndBox 1).hi := by nd_eval

/-! ## 6. 七条 `hnd*` 的证书盒证明 -/

/-- **`hndRho`（9 条）**：盒上 `(x 6)² − sin²(angleVec x j) ≠ 0`。 -/
theorem nd_hndRho : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ j : Fin 9,
    (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0 := by
  intro x hx j
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hmem : (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox j)))).Mem
      ((x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2) :=
    sub_mem (sq_mem_pow (hQ 6)) (sq_mem_pow (sinTotLag_mem (ndAngleBox_mem hQ j)))
  exact ne_zero_of_pos_lo (by exact_mod_cast ndRho_read j) hmem

/-- **`hndW`**：盒上 `(x 6)² − ((x 5 − x 4)/2)² ≠ 0`。 -/
theorem nd_hndW : ∀ x ∈ Metric.closedBall certCR rhoCertR,
    (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0 := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hmem : (sub (sq (ndBox 6))
      (sq (mul (ofRat (1 / 2)) (sub (ndBox 5) (ndBox 4))))).Mem
      ((x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2) := by
    refine sub_mem (sq_mem_pow (hQ 6)) (sq_mem_pow ?_)
    have h : ((x 5 - x 4) / 2) = (((1 / 2 : ℚ) : ℝ) * (x 5 - x 4)) := by push_cast; ring
    rw [h]
    exact mul_mem (ofRat_mem (1 / 2)) (sub_mem (hQ 5) (hQ 4))
  exact ne_zero_of_pos_lo (by exact_mod_cast ndW_read) hmem

/-- **`hndU1`**：`Uvec x 1 ≠ hub1 x`（第二坐标分离）。 -/
theorem nd_hndU1 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 1 ≠ hub1 x := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hU : (ndUvecBox ndBox 1 1).Mem ((Uvec x 1).ofLp 1) := ndUvecBox_mem hQ 1 1
  have hH : (ndHub1Box ndBox 1).Mem ((hub1 x).ofLp 1) := ndHub1Box_mem hQ 1
  have h0 : (ndHub1Box ndBox 1).lo = 0 := rfl
  refine point_ne_of_coord (i := 1) (a := 1 / 10) (by norm_num)
    (le_abs_sub_of_lo_sub_hi' hU hH (by norm_num) ?_)
  rw [h0]
  linarith [ndU1_read]

/-- **`hndU2`**：`Uvec x 2 ≠ hub0 x`。 -/
theorem nd_hndU2 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 2 ≠ hub0 x := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hU : (ndUvecBox ndBox 2 1).Mem ((Uvec x 2).ofLp 1) := ndUvecBox_mem hQ 2 1
  have hH : (ndHub0Box ndBox 1).Mem ((hub0 x).ofLp 1) := ndHub0Box_mem hQ 1
  have h0 : (ndHub0Box ndBox 1).lo = 0 := rfl
  refine point_ne_of_coord (i := 1) (a := 1 / 10) (by norm_num)
    (le_abs_sub_of_lo_sub_hi' hU hH (by norm_num) ?_)
  rw [h0]
  linarith [ndU2_read]

/-- **`hndU3`**：`Uvec x 3 ≠ hub0 x`。 -/
theorem nd_hndU3 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 3 ≠ hub0 x := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hU : (ndUvecBox ndBox 3 1).Mem ((Uvec x 3).ofLp 1) := ndUvecBox_mem hQ 3 1
  have hH : (ndHub0Box ndBox 1).Mem ((hub0 x).ofLp 1) := ndHub0Box_mem hQ 1
  have h0 : (ndHub0Box ndBox 1).lo = 0 := rfl
  refine point_ne_of_coord (i := 1) (a := 1 / 10) (by norm_num)
    (le_abs_sub_of_lo_sub_hi' hU hH (by norm_num) ?_)
  rw [h0]
  linarith [ndU3_read]

/-- **`hndU8`**：`Uvec x 8 ≠ hub1 x`（第一坐标分离）。 -/
theorem nd_hndU8 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 8 ≠ hub1 x := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hU : (ndUvecBox ndBox 8 0).Mem ((Uvec x 8).ofLp 0) := ndUvecBox_mem hQ 8 0
  have hH : (ndHub1Box ndBox 0).Mem ((hub1 x).ofLp 0) := ndHub1Box_mem hQ 0
  exact point_ne_of_coord (i := 0) (a := 1 / 10) (by norm_num)
    (le_abs_sub_of_lo_sub_hi' hU hH (by norm_num) ndU8_read)

/-- **`hndWp`**：`wPoint x ≠ ringCenter x 6`（第二坐标分离）。 -/
theorem nd_hndWp : ∀ x ∈ Metric.closedBall certCR rhoCertR, wPoint x ≠ ringCenter x 6 := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hR : (ndRingBox ndBox 6 1).Mem ((ringCenter x 6).ofLp 1) := ndRingBox_mem hQ 6 1
  have hW : (ndWPointBox ndBox 1).Mem ((wPoint x).ofLp 1) := ndWPointBox_mem hQ 1
  exact (point_ne_of_coord (i := 1) (a := 1 / 10) (by norm_num)
    (le_abs_sub_of_lo_sub_hi hR hW (by norm_num) ndWp_read)).symm

/-! ## 7. 打包（供 `Precond.TCSystem_unique_root_of_full_data` 一次性消费） -/

/-- **七条非退化条件的打包形式**：三段 `∀ x ∈ closedBall certCR rhoCertR` 的合取，
可直接喂给 `TCSystem_unique_root_of_full_data` 的 `hndRho … hndWp` 位置。 -/
theorem nd_all :
    (∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ j : Fin 9,
        (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0) ∧
      (∀ x ∈ Metric.closedBall certCR rhoCertR,
          (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0) ∧
      (∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 1 ≠ hub1 x) ∧
      (∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 2 ≠ hub0 x) ∧
      (∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 3 ≠ hub0 x) ∧
      (∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 8 ≠ hub1 x) ∧
      (∀ x ∈ Metric.closedBall certCR rhoCertR, wPoint x ≠ ringCenter x 6) :=
  ⟨nd_hndRho, nd_hndW, nd_hndU1, nd_hndU2, nd_hndU3, nd_hndU8, nd_hndWp⟩

/-! ## 8. 负对照（**判别力**证据：同一套求值器 + 同一套读数形状，改错 ⇒ 报假）

口径（与 `evidence/interval-ad/nd_bounds.out.txt` §负对照 的方法学一致）：
`≠0` / `≠` 型断言**不能用常数平移**破坏（平移只换号、要么需要 1e-9 量级刀锋对准），
稳健的破坏手段是**放大盒**（NC1/NC2/NC5）与**变异公式/坐标**（NC3/NC4）。
下面每条都是内核判定的**否定命题**，与 §5 的正向读数**同形同性**，故构成判别力证据。 -/

/-- **NC1（放大盒，`hndRho` 的 `R` 坐标）**：把 `x6` 的盒放宽 `±1/5`，同一读数**报假**。 -/
theorem ndNC1_rho :
    (sub (sq (⟨boxLoCert 6 - 1 / 5, boxHiCert 6 + 1 / 5⟩ : RatInterval))
      (sq (sinTotLag (ndAngleBox ndBox 4)))).lo ≤ 0 := by
  nd_eval

/-- **NC2（放大盒，`hndW` 的 `R` 坐标）**：纯有理读数，同一改错**报假**。

**量化备注（如实分层）**：放宽 `±1/100` 时本条**仍然成立**（`(x6)² − ((x5−x4)/2)²` 的下界
仍 `≈ +9.22e-2 > 0`），必须放宽到 `±1/5` 才翻号（`hndW` 的「厚度」在该坐标上约 `1.69e-1`）。
这与 `evidence/interval-ad` 的 NC1（`ρ→1e-3` 只打穿最紧的 `hndRho`）同类：**放大盒**
是稳健手段，但**幅度要够**才翻号。 -/
theorem ndNC2_W :
    (sub (sq (⟨boxLoCert 6 - 1 / 5, boxHiCert 6 + 1 / 5⟩ : RatInterval))
      (sq (mul (ofRat (1 / 2)) (sub (ndBox 5) (ndBox 4))))).lo ≤ 0 := by
  nd_eval

/-- **NC3（符号变异，`hndU1`）**：把 `Uvec · 1` 第二坐标的**上界**错说成**下界**，
报假 —— 求值器确实分得清 `−0.378…` 与 `+0.378…`（读数不是恒真）。 -/
theorem ndNC3_signU1 : ¬ (((1 / 10 : ℚ)) ≤ (ndUvecBox ndBox 1 1).lo) := by
  nd_eval

/-- **NC4（坐标变异，`hndU8`）**：`Uvec · 8` 与 `hub1` 的**第二**坐标几乎重合
（`≈ 4.4e-8`），用第二坐标做分离**报假** —— 证明 §6 选第一坐标不是任意的。 -/
theorem ndNC4_coordU8 :
    ¬ (((1 / 10 : ℚ)) ≤ (ndHub1Box ndBox 1).lo - (ndUvecBox ndBox 8 1).hi) := by
  nd_eval

/-- **NC5（放大盒，`hndRho` 的角坐标）**：把 `a0` 的盒放宽 `±1`（越出 `sin` 窗口 ⇒
相位算子保守回退 `[-1,1]`），同一读数**报假**。 -/
theorem ndNC5_rho_angle :
    (sub (sq (ndBox 6))
      (sq (sinTotLag (⟨boxLoCert 0 - 1, boxHiCert 0 + 1⟩ : RatInterval)))).lo ≤ 0 := by
  nd_eval

/-! ## 9. 接口审计：把七条 `hnd*` 真正**插进** `Precond` 的 G1 入口

本条不引入新数学，只做**消费方视角**的检查：`TCSystem_unique_root_of_full_data` 的前提清单里
七个 `hnd*` 位置**原样**不接受输入 —— 于是「G1 还差什么」只剩 `Y/Yinv/Jt/Jt 包络/hsum/Fm/hFm/η/残差界`
（即 `D`/`Jt` 一侧的数据），非退化条件**不再**是前提。

**剩余前提的状态（全队公共认知，写准比写全重要）**：
* `Jt`（Jacobian 逐元素包络）：Lead 报（**本件未独立复核**）已接根，但状态是
  **95/144 无条件 + 49/144 条件于 `Hess`**（`jt-build` 交付、`jth-assembly` 在做 `Hess`）
  ⇒ 下面清单里的 `Jt` 必须读作「**条件于 `Hess`**」，**不是**「已给」。
* `Y/Yinv`：源预条件子是 binary64 **近似逆**，取不到精确有理左逆 ⇒ 该走 `PrecondRight` 的
  **右收缩**不等式（`‖I − J·Y‖ ≤ K' < 1`）；本件按 `Precond` 的左逆形态书写，右侧入口同形。
* `Fm`（`TCSystem c` 的逐项包络）后 7 分量（乘子块）：`fm-eval` 一侧。 -/

/-- **G1（完全有理化形态）在证书球上的实例化**：七条 `hnd*` 已由本文件证出，
仅剩 `Y/Yinv/Jt/Fm/η/K` 一侧的数据前提。 -/
theorem nd_plug_full_data
    (Y Yinv : Fin 12 → Fin 12 → ℚ)
    (hYinv : ∀ i j : Fin 12, ∑ k : Fin 12, Yinv i k * Y k j = (if i = j then (1 : ℚ) else 0))
    (K η : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hη0 : 0 ≤ η)
    (Jt : Fin 12 → Fin 12 → RatInterval)
    (hJ : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K)
    (Fm : Fin 12 → RatInterval)
    (hFm : ∀ k : Fin 12, (Fm k).Mem (TCSystem certCR k))
    (hηb : ∀ i : Fin 12, (((incrMatVec Y Fm i).abs).hi : ℝ) ≤ η)
    (hres : η + K * rhoCertR < rhoCertR) :
    ∃! x : Fin 12 → ℝ, x ∈ Metric.closedBall certCR rhoCertR ∧ TCSystem x = 0 :=
  TCSystem_unique_root_of_full_data (c := certCR) (ρ := rhoCertR) Y Yinv hYinv
    rhoCertR_pos hK0 hK1 hη0
    nd_hndRho nd_hndW nd_hndU1 nd_hndU2 nd_hndU3 nd_hndU8 nd_hndWp Jt hJ hsum Fm hFm hηb hres

/-! ## 10. **端到端接线自检**（G1 数据 ⇒ `C891RootSpec` ⇒ `Rstar` 锁定）

把 §9 的球口径 `∃!`（= `RootSpecBall`）继续走完 Lead 维护的两段桥：
`BoxRstar.root_spec_certBox`（球口径 → 盒口径 `∃!`）→ `TCSystem.tcRootSpec`
（盒口径 `∃!` → `C891RootSpec`，`sys` 钉成 `TCSystem`、`radiusIndex = 6`）→
`Rstar_mem_of_krawczyk` / `Rstar_lt_R0_of_krawczyk`（`Rstar` 落入证书盒 + `< 19/50`）。

目的只有一个：**证明整条链的接口形状无缝**（没有需要 Lead 侧再做 cast/口径转换的缝），
从而把 G1 的剩余义务**精确**化为 §9 列出的那组数据前提。 -/

/-- **端到端**：仅以 `Y/Yinv/Jt/hJ/hsum/Fm/hFm/hηb/hres` 为输入，
一次收口得到 `C891RootSpec`（`sys = TCSystem`、盒 = 证书盒、`radiusIndex = 6`），
并同时得到 `Rstar ∈ [boxLoCert 6, boxHiCert 6]` 与 `Rstar < 19/50`。 -/
theorem nd_end_to_end
    (Y Yinv : Fin 12 → Fin 12 → ℚ)
    (hYinv : ∀ i j : Fin 12, ∑ k : Fin 12, Yinv i k * Y k j = (if i = j then (1 : ℚ) else 0))
    (K η : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hη0 : 0 ≤ η)
    (Jt : Fin 12 → Fin 12 → RatInterval)
    (hJ : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K)
    (Fm : Fin 12 → RatInterval)
    (hFm : ∀ k : Fin 12, (Fm k).Mem (TCSystem certCR k))
    (hηb : ∀ i : Fin 12, (((incrMatVec Y Fm i).abs).hi : ℝ) ≤ η)
    (hres : η + K * rhoCertR < rhoCertR) :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ S.radiusIndex = 6 ∧
        ((boxLoCert 6 : ℝ) ≤ Rstar S ∧ Rstar S ≤ (boxHiCert 6 : ℝ)) ∧ Rstar S < 19 / 50 := by
  have hball : RootSpecBall :=
    nd_plug_full_data Y Yinv hYinv K η hK0 hK1 hη0 Jt hJ hsum Fm hFm hηb hres
  refine ⟨tcRootSpec boxLoCert boxHiCert (root_spec_certBox hball),
    rfl, rfl, rfl, tcRootSpec_radiusIndex boxLoCert boxHiCert (root_spec_certBox hball), ?_, ?_⟩
  · exact Rstar_mem_of_krawczyk rfl ⟨rfl, rfl⟩ rfl
  · exact Rstar_lt_R0_of_krawczyk rfl ⟨rfl, rfl⟩ rfl

/-! ## 11. 源数据可实现的那条 G1 入口（右侧收缩）同样吃这七条 + 一处结论形状接口发现

`BoxRstar.c891RootSpec_of_right_data`（R10：源 `Y` 是 binary64 近似逆，故走 `‖I − J·Y‖ ≤ K' < 1`）
的**前提清单里也有同样七个 `hnd*`**（且被**两处**用到：`krawczykMat` 侧的行和界路线、
以及 `Transport.differentiableAt_TCSystem_of_conditions` 的**可微性**）⇒ 本文件七条定理在该路径上
同样是承重的。下面 (1) 做插拔自检；(2) 记录一处**结论形状**接口发现。 -/

/-- **(1) 右侧收缩入口的插拔自检**：七条 `hnd*` 原样插入
`BoxRstar.c891RootSpec_of_right_data` 的七个位置（证明该入口的非退化前提同样清零）。

**结论形状**：与 `c891RootSpec_of_right_data`（Lead 采纳本文件 §11(2) 的建议后，其结论已含
`radiusIndex = 6`）**逐字同形**，含第 4 个合取项。 -/
theorem nd_plug_right_data
    (Y : Fin 12 → Fin 12 → ℚ) (K η K' : ℝ)
    (hK0 : 0 ≤ K) (hK1 : K < 1) (hη0 : 0 ≤ η) (hK'0 : 0 ≤ K') (hK'1 : K' < 1)
    (Jt : Fin 12 → Fin 12 → RatInterval)
    (hJ : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K)
    (hsumR : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMatR Jt Y i j).lo : ℝ)| |((krawczykMatR Jt Y i j).hi : ℝ)| ≤ K')
    (Fm : Fin 12 → RatInterval)
    (hFm : ∀ k : Fin 12, (Fm k).Mem (TCSystem certCR k))
    (hηb : ∀ i : Fin 12, (((incrMatVec Y Fm i).abs).hi : ℝ) ≤ η)
    (hres : η + K * rhoCertR < rhoCertR) :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ S.radiusIndex = 6 :=
  c891RootSpec_of_right_data Y hK0 hK1 hη0 hK'0 hK'1
    nd_hndRho nd_hndW nd_hndU1 nd_hndU2 nd_hndU3 nd_hndU8 nd_hndWp Jt hJ hsum hsumR Fm hFm hηb hres

/-- **(1′) 源数据可实现路径的端到端**：与 §10 `nd_end_to_end` 同款，但走**右侧收缩**入口
（源 `Y` 是 binary64 近似逆，取不到精确有理左逆 ⇒ 这条才是源数据的可实现路径）。
`radiusIndex = 6` 由 `c891RootSpec_of_right_data` 的结论（Lead 已升级为 `_with_idx` 形态）直接给出，
故这里能从构造子一次拿全：`sys`/`boxLo`/`boxHi`/`radiusIndex` + `Rstar` 双侧锁定 + `Rstar < 19/50`。 -/
theorem nd_end_to_end_right
    (Y : Fin 12 → Fin 12 → ℚ) (K η K' : ℝ)
    (hK0 : 0 ≤ K) (hK1 : K < 1) (hη0 : 0 ≤ η) (hK'0 : 0 ≤ K') (hK'1 : K' < 1)
    (Jt : Fin 12 → Fin 12 → RatInterval)
    (hJ : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K)
    (hsumR : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMatR Jt Y i j).lo : ℝ)| |((krawczykMatR Jt Y i j).hi : ℝ)| ≤ K')
    (Fm : Fin 12 → RatInterval)
    (hFm : ∀ k : Fin 12, (Fm k).Mem (TCSystem certCR k))
    (hηb : ∀ i : Fin 12, (((incrMatVec Y Fm i).abs).hi : ℝ) ≤ η)
    (hres : η + K * rhoCertR < rhoCertR) :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ S.radiusIndex = 6 ∧
        ((boxLoCert 6 : ℝ) ≤ Rstar S ∧ Rstar S ≤ (boxHiCert 6 : ℝ)) ∧ Rstar S < 19 / 50 := by
  obtain ⟨S, h1, h2, h3, h4⟩ :=
    nd_plug_right_data Y K η K' hK0 hK1 hη0 hK'0 hK'1 Jt hJ hsum hsumR Fm hFm hηb hres
  refine ⟨S, h1, h2, h3, h4, ?_, ?_⟩
  · exact Rstar_mem_of_krawczyk h1 ⟨h2, h3⟩ h4
  · exact Rstar_lt_R0_of_krawczyk h1 ⟨h2, h3⟩ h4

/-- **(2) 结论形状接口发现（内核证明）**：`C891RootSpec` 的四个字段里，
`sys`/`boxLo`/`boxHi` **不决定** `radiusIndex` —— 存在两个 `C891RootSpec`，
三字段逐字相同而 `radiusIndex` 不同。

**为什么值得记**：`BoxRstar.c891RootSpec_of_right_data` 的结论只给三字段
（它走的是 `c891RootSpec_of_ball`，**不是** `c891RootSpec_of_ball_with_idx`），
而下游把 `Rstar` 钉到第 6 坐标用的 `BoxRstar.Rstar_mem_of_krawczyk` **要求**
`hidx : S.radiusIndex = 6`。⇒ 从右侧数据路径拿到 `S` 后，`radiusIndex` **不能**从结论里读出，
也不能从其余三字段推出（本定理即其内核证据）。
**建议（Lead 侧一行改动）**：把 `c891RootSpec_of_right_data` 的结论改用
`c891RootSpec_of_ball_with_idx`（同一个见证 `tcRootSpec …`，`radiusIndex` 字段由 `rfl` 给出）。 -/
theorem nd_radiusIndex_not_free :
    ∃ S T : C891RootSpec,
      S.sys = T.sys ∧ S.boxLo = T.boxLo ∧ S.boxHi = T.boxHi ∧ S.radiusIndex ≠ T.radiusIndex := by
  have hex : ∃! z : Fin 12 → ℝ,
      (∀ i : Fin 12, ((0 : ℚ) : ℝ) ≤ z i ∧ z i ≤ ((0 : ℚ) : ℝ)) ∧
        (fun _ : Fin 12 → ℝ => (0 : Fin 12 → ℝ)) z = 0 :=
    ⟨fun _ => 0, ⟨fun i => by simp only [Rat.cast_zero]; exact ⟨le_refl 0, le_refl 0⟩, rfl⟩,
      fun w hw => funext fun i => by
        have h1 := (hw.1 i).1
        have h2 := (hw.1 i).2
        simp only [Rat.cast_zero] at h1 h2
        exact le_antisymm h2 h1⟩
  have hne : (6 : Fin 12) ≠ (0 : Fin 12) := by decide
  let S : C891RootSpec :=
    { sys := fun _ => 0, boxLo := fun _ => 0, boxHi := fun _ => 0,
      exists_unique := hex, radiusIndex := 6 }
  let T : C891RootSpec := { S with radiusIndex := 0 }
  refine ⟨S, T, rfl, rfl, rfl, ?_⟩
  show (6 : Fin 12) ≠ (0 : Fin 12)
  exact hne

/-! ## 12. **第二条判据**：五条点分离型改用「两点距离下界」重证（Lead 批准折叠进根）

§6 的五条点分离型（`hndU1/U2/U3/U8/Wp`）用的是**单坐标**判据：
`le_abs_sub_of_lo_sub_hi`/`'`（`A.lo − B.hi ≥ a`）+ `point_ne_of_coord` —— **只用到被选中的那一个坐标**。
本节换**另一条判据**：

* `RatInterval.distInterval`（`√((Δx)² + (Δy)²)`，**两个坐标都进入**且经 `sqrt`）给出**两点距离的下界**；
* 收口改用 `dist p q ≠ 0 ⇒ p ≠ q`（`point_ne_of_dist_lower`）。

**价值定位（如实，勿升格）**：这是「**不同判据 + 不同表达式树**，但**同一求值器**（`nd_eval`）
与**同一盒定义**」的第二条路线 —— **不是**与 §6 完全独立（共享仪器），
但**判据与坐标选择都不同**：若 §6 的**坐标选择、符号方向或单坐标端点**有错，
本节（用两坐标、经 `sqrt`）**不会跟着错**。故它把这三类错误从"一次采样"提升为"两条不同判据同结论"。 -/

/-- **`dist` 正下界 ⇒ 两点不等**（与坐标分离无关的收口）。 -/
theorem point_ne_of_dist_lower {p q : Point} {a : ℚ} (ha : 0 < a)
    (h : (a : ℝ) ≤ dist p q) : p ≠ q := by
  intro hpq
  rw [hpq, dist_self] at h
  have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  linarith

/-- `hndU1` 的距离读数：`dist(Uvec · 1, hub1 ·) > 1/10`（区间下界）。 -/
theorem ndDist_read_U1 :
    ((1 / 10 : ℚ)) ≤ (distInterval (ndUvecBox ndBox 1) (ndHub1Box ndBox)).lo := by
  simp only [distInterval]
  nd_eval

theorem ndDist_read_U2 :
    ((1 / 10 : ℚ)) ≤ (distInterval (ndUvecBox ndBox 2) (ndHub0Box ndBox)).lo := by
  simp only [distInterval]
  nd_eval

theorem ndDist_read_U3 :
    ((1 / 10 : ℚ)) ≤ (distInterval (ndUvecBox ndBox 3) (ndHub0Box ndBox)).lo := by
  simp only [distInterval]
  nd_eval

theorem ndDist_read_U8 :
    ((1 / 10 : ℚ)) ≤ (distInterval (ndUvecBox ndBox 8) (ndHub1Box ndBox)).lo := by
  simp only [distInterval]
  nd_eval

theorem ndDist_read_Wp :
    ((1 / 10 : ℚ)) ≤ (distInterval (ndWPointBox ndBox) (ndRingBox ndBox 6)).lo := by
  simp only [distInterval]
  nd_eval

/-- **`hndU1`（第二判据）**：`Uvec x 1 ≠ hub1 x`，由**两点距离下界**收口。 -/
theorem nd_hndU1_via_dist : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 1 ≠ hub1 x := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hm : (distInterval (ndUvecBox ndBox 1) (ndHub1Box ndBox)).Mem (dist (Uvec x 1) (hub1 x)) :=
    distInterval_mem (fun i => ndUvecBox_mem hQ 1 i) (fun i => ndHub1Box_mem hQ i)
  exact point_ne_of_dist_lower (a := 1 / 10) (by norm_num)
    (le_trans (by exact_mod_cast ndDist_read_U1) (mem_lo_le hm))

/-- **`hndU2`（第二判据）**。 -/
theorem nd_hndU2_via_dist : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 2 ≠ hub0 x := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hm : (distInterval (ndUvecBox ndBox 2) (ndHub0Box ndBox)).Mem (dist (Uvec x 2) (hub0 x)) :=
    distInterval_mem (fun i => ndUvecBox_mem hQ 2 i) (fun i => ndHub0Box_mem hQ i)
  exact point_ne_of_dist_lower (a := 1 / 10) (by norm_num)
    (le_trans (by exact_mod_cast ndDist_read_U2) (mem_lo_le hm))

/-- **`hndU3`（第二判据）**。 -/
theorem nd_hndU3_via_dist : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 3 ≠ hub0 x := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hm : (distInterval (ndUvecBox ndBox 3) (ndHub0Box ndBox)).Mem (dist (Uvec x 3) (hub0 x)) :=
    distInterval_mem (fun i => ndUvecBox_mem hQ 3 i) (fun i => ndHub0Box_mem hQ i)
  exact point_ne_of_dist_lower (a := 1 / 10) (by norm_num)
    (le_trans (by exact_mod_cast ndDist_read_U3) (mem_lo_le hm))

/-- **`hndU8`（第二判据）**。 -/
theorem nd_hndU8_via_dist : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 8 ≠ hub1 x := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hm : (distInterval (ndUvecBox ndBox 8) (ndHub1Box ndBox)).Mem (dist (Uvec x 8) (hub1 x)) :=
    distInterval_mem (fun i => ndUvecBox_mem hQ 8 i) (fun i => ndHub1Box_mem hQ i)
  exact point_ne_of_dist_lower (a := 1 / 10) (by norm_num)
    (le_trans (by exact_mod_cast ndDist_read_U8) (mem_lo_le hm))

/-- **`hndWp`（第二判据）**：`wPoint x ≠ ringCenter x 6`。 -/
theorem nd_hndWp_via_dist : ∀ x ∈ Metric.closedBall certCR rhoCertR, wPoint x ≠ ringCenter x 6 := by
  intro x hx
  have hQ : ∀ i, (ndBox i).Mem (x i) := ndBox_mem hx
  have hm : (distInterval (ndWPointBox ndBox) (ndRingBox ndBox 6)).Mem
      (dist (wPoint x) (ringCenter x 6)) :=
    distInterval_mem (fun i => ndWPointBox_mem hQ i) (fun i => ndRingBox_mem hQ 6 i)
  exact point_ne_of_dist_lower (a := 1 / 10) (by norm_num)
    (le_trans (by exact_mod_cast ndDist_read_Wp) (mem_lo_le hm))

/-- **两条判据的一致性打包**：§6（单坐标差）与 §12（二维距离）对同五条断言给出同结论。 -/
theorem nd_all_via_dist :
    (∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 1 ≠ hub1 x) ∧
      (∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 2 ≠ hub0 x) ∧
      (∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 3 ≠ hub0 x) ∧
      (∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 8 ≠ hub1 x) ∧
      (∀ x ∈ Metric.closedBall certCR rhoCertR, wPoint x ≠ ringCenter x 6) :=
  ⟨nd_hndU1_via_dist, nd_hndU2_via_dist, nd_hndU3_via_dist, nd_hndU8_via_dist, nd_hndWp_via_dist⟩

end N11Formalization
