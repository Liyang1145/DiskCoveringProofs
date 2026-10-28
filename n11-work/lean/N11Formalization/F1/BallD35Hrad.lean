/-
  evidence/f1-step2/F1-BallD35.lean
  ================================

  **F1 第 2 步（`compIv` 的盒版）· 件 AB** = 六步顺序的 ①–③ + ⑤

  * `F1-BallD35-A.lean`（`63CF293A8F36A28D` ✓ 已过门）是**件 A**（①–③）；
  * 本件 = **件 A 的全部内容**（逐字，便于单文件 `-File` 门）+ **②③ 的收尾**
    （`WpIvBox` 族 + `dUxIvBox`/`dUyIvBox`）+ **⑤ 的复合**（`compIvBox` + `compIvBox_mem`）。

  **与盒心版（`ResidualDerivD`）的全部差别 —— 只有两类，且都是必须的** ✓：
  1. `a_j`/`θ_j` 的**盒**取 `ndAngleBox ndBox` / `thetaInterval (ndAngleBox ndBox)`（替掉盒心字面量）；
  2. **点冻结项必须换成含 `x` 的区间** ✓✗：
     `ofRat (2 * cCert 6)` → `mul (ofRat 2) (ndBox 6)`，
     `ofRat (2 * ((cCert 5 - cCert 4)/2))` → `mul (ofRat 2) (mul (ofRat (1/2)) (sub (ndBox 5) (ndBox 4)))`。
     否则对 `x ≠ u0` **不成立** ✗。

  **真实侧**写成 `*Real` 系列（一般点 `x` 的同一棵树）；`Mem` 目标是**逐点真实表达式** ✓
  （**不是** `fderiv` 本身 ✗ —— 桥到 `fderiv` 是件 C，见文件末）。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`。
-/
import N11Formalization.NondegProof
import N11Formalization.ResidualDerivD

noncomputable section

namespace N11Formalization

open RatInterval

/-! ## ① `Wk` / `2√Wk` 的盒版 -/

def wkBox (j : Fin 9) : RatInterval :=
  sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox j)))

theorem wkBox_pos (j : Fin 9) : (0 : ℚ) < (wkBox j).lo :=
  ndRho_read j

theorem wkBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) (j : Fin 9) :
    (wkBox j).Mem (x 6 * x 6 - Real.sin (angleVec x j) * Real.sin (angleVec x j)) := by
  have hQ : ∀ i : Fin 12, (ndBox i).Mem (x i) := ndBox_mem hx
  exact RatInterval.sub_mem (RatInterval.sq_mem (hQ 6))
    (RatInterval.sq_mem (RatInterval.sinTotLag_mem (ndAngleBox_mem hQ j)))

theorem wkBox_valid (j : Fin 9) : Valid (wkBox j) :=
  valid_of_mem (wkBox_mem certCR_mem_ball j)

def sqrtWkIvBox (j : Fin 9) : RatInterval := (wkBox j).sqrt

def twoSqrtWkIvBox (j : Fin 9) : RatInterval := mul (ofRat 2) (sqrtWkIvBox j)

theorem sqrtWkIvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (j : Fin 9) :
    (sqrtWkIvBox j).Mem
      (Real.sqrt (x 6 * x 6 - Real.sin (angleVec x j) * Real.sin (angleVec x j))) :=
  RatInterval.sqrt_mem (wkBox_mem hx j)

theorem twoSqrtWkIvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (j : Fin 9) :
    (twoSqrtWkIvBox j).Mem
      (2 * Real.sqrt (x 6 * x 6 - Real.sin (angleVec x j) * Real.sin (angleVec x j))) := by
  rw [twoSqrtWkIvBox]
  have h := RatInterval.mul_mem (RatInterval.ofRat_mem (2 : ℚ)) (sqrtWkIvBox_mem hx j)
  simpa using h

theorem twoSqrtWkIvBox_pos (j : Fin 9) : 0 < (twoSqrtWkIvBox j).lo :=
  twoMulIv_pos (sqrtWkIvBox j) (sqrtLo_pos (wkBox_pos j))
    (RatInterval.sqrt_valid (wkBox_valid j))

/-! ## ② `Apt` / `Bpt`、`DxIv` / `DyIv` / `radIv` 的盒版 -/

def AptBox : Fin 5 → Fin 2 → RatInterval
  | 0 => ndUvecBox ndBox 1
  | 1 => ndUvecBox ndBox 2
  | 2 => ndUvecBox ndBox 3
  | 3 => ndUvecBox ndBox 8
  | 4 => ndWPointBox ndBox

def BptBox : Fin 5 → Fin 2 → RatInterval
  | 0 => ndHub1Box ndBox
  | 1 => ndHub0Box ndBox
  | 2 => ndHub0Box ndBox
  | 3 => ndHub1Box ndBox
  | 4 => ndRingBox ndBox 6

theorem AptBox_mem (k : Fin 5) (i : Fin 2) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) : ((AptBox k) i).Mem (((Apt k) x).ofLp i) := by
  have hQ : ∀ i : Fin 12, (ndBox i).Mem (x i) := ndBox_mem hx
  match k with
  | 0 => exact ndUvecBox_mem hQ 1 i
  | 1 => exact ndUvecBox_mem hQ 2 i
  | 2 => exact ndUvecBox_mem hQ 3 i
  | 3 => exact ndUvecBox_mem hQ 8 i
  | 4 => exact ndWPointBox_mem hQ i

theorem BptBox_mem (k : Fin 5) (i : Fin 2) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) : ((BptBox k) i).Mem (((Bpt k) x).ofLp i) := by
  have hQ : ∀ i : Fin 12, (ndBox i).Mem (x i) := ndBox_mem hx
  match k with
  | 0 => exact ndHub1Box_mem hQ i
  | 1 => exact ndHub0Box_mem hQ i
  | 2 => exact ndHub0Box_mem hQ i
  | 3 => exact ndHub1Box_mem hQ i
  | 4 => exact ndRingBox_mem hQ 6 i

def DxIvBox (k : Fin 5) : RatInterval := sub ((AptBox k) 0) ((BptBox k) 0)

def DyIvBox (k : Fin 5) : RatInterval := sub ((AptBox k) 1) ((BptBox k) 1)

def radIvBox (k : Fin 5) : RatInterval := add (sq (DxIvBox k)) (sq (DyIvBox k))

def radSqrtIvBox (k : Fin 5) : RatInterval := (radIvBox k).sqrt

def twoRadSqrtIvBox (k : Fin 5) : RatInterval := mul (ofRat 2) (radSqrtIvBox k)

theorem DxIvBox_mem (k : Fin 5) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (DxIvBox k).Mem (((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) :=
  RatInterval.sub_mem (AptBox_mem k 0 hx) (BptBox_mem k 0 hx)

theorem DyIvBox_mem (k : Fin 5) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (DyIvBox k).Mem (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) :=
  RatInterval.sub_mem (AptBox_mem k 1 hx) (BptBox_mem k 1 hx)

theorem radIvBox_mem (k : Fin 5) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (radIvBox k).Mem ((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2
      + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2) :=
  RatInterval.add_mem (RatInterval.sq_mem_pow (DxIvBox_mem k hx))
    (RatInterval.sq_mem_pow (DyIvBox_mem k hx))

theorem radIvBox_valid (k : Fin 5) : Valid (radIvBox k) :=
  valid_of_mem (radIvBox_mem k certCR_mem_ball)

theorem twoRadSqrtIvBox_mem (k : Fin 5) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (twoRadSqrtIvBox k).Mem
      (2 * Real.sqrt ((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2
        + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2)) := by
  rw [twoRadSqrtIvBox, radSqrtIvBox]
  have h := RatInterval.mul_mem (RatInterval.ofRat_mem (2 : ℚ))
    (RatInterval.sqrt_mem (radIvBox_mem k hx))
  simpa using h

theorem twoRadSqrtIvBox_pos (k : Fin 5) (h : 0 < (radIvBox k).lo) :
    0 < (twoRadSqrtIvBox k).lo :=
  twoMulIv_pos (radSqrtIvBox k) (sqrtLo_pos h) (RatInterval.sqrt_valid (radIvBox_valid k))

/-! ## ②bis `Wp` 的盒版（第 5 行 `wPoint` 用；`WpIv` 的严格下界 = `ndW_read` ✓） -/

def WpIvBox : RatInterval :=
  sub (sq (ndBox 6)) (sq (mul (ofRat (1 / 2)) (sub (ndBox 5) (ndBox 4))))

def WpReal (x : Fin 12 → ℝ) : ℝ := (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2

theorem WpIvBox_pos : (0 : ℚ) < WpIvBox.lo :=
  ndW_read

theorem WpIvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    WpIvBox.Mem (WpReal x) := by
  have hQ : ∀ i : Fin 12, (ndBox i).Mem (x i) := ndBox_mem hx
  have h1 : (mul (ofRat (1 / 2)) (sub (ndBox 5) (ndBox 4))).Mem
      (((1 / 2 : ℚ) : ℝ) * (x 5 - x 4)) :=
    RatInterval.mul_mem (RatInterval.ofRat_mem (1 / 2 : ℚ))
      (RatInterval.sub_mem (hQ 5) (hQ 4))
  have h2 : ((x 5 - x 4) / 2) = ((1 / 2 : ℚ) : ℝ) * (x 5 - x 4) := by push_cast; ring
  rw [WpReal, h2]
  exact RatInterval.sub_mem (RatInterval.sq_mem_pow (hQ 6)) (RatInterval.sq_mem_pow h1)

theorem WpIvBox_valid : Valid WpIvBox :=
  valid_of_mem (WpIvBox_mem certCR_mem_ball)

def sqrtWpIvBox : RatInterval := WpIvBox.sqrt

def twoSqrtWpIvBox : RatInterval := mul (ofRat 2) sqrtWpIvBox

theorem sqrtWpIvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    sqrtWpIvBox.Mem (Real.sqrt (WpReal x)) :=
  RatInterval.sqrt_mem (WpIvBox_mem hx)

theorem twoSqrtWpIvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    twoSqrtWpIvBox.Mem (2 * Real.sqrt (WpReal x)) := by
  rw [twoSqrtWpIvBox]
  have h := RatInterval.mul_mem (RatInterval.ofRat_mem (2 : ℚ)) (sqrtWpIvBox_mem hx)
  simpa using h

theorem twoSqrtWpIvBox_pos (h : 0 < WpIvBox.lo) : 0 < twoSqrtWpIvBox.lo :=
  twoMulIv_pos sqrtWpIvBox (sqrtLo_pos h) (RatInterval.sqrt_valid WpIvBox_valid)

/-! ## ③ 导数叶子的盒版（真实侧 = 一般点 `x` 的同一棵树） -/

def drhoReal (x : Fin 12 → ℝ) (j : Fin 9) (i : Fin 7) : ℝ :=
  -(Real.sin (angleVec x j)) * (dAngle j i : ℝ)
    - (1 / (2 * Real.sqrt (x 6 * x 6 - Real.sin (angleVec x j) * Real.sin (angleVec x j))))
      * ((2 * x 6) * (if i = 6 then 1 else 0 : ℝ)
        - (2 * Real.sin (angleVec x j)) * ((Real.cos (angleVec x j)) * (dAngle j i : ℝ)))

def ring0Real (x : Fin 12 → ℝ) (j : Fin 9) (i : Fin 7) : ℝ :=
  rhoK x j * (-(Real.sin (thetaOf (angleVec x) j)) * (dTheta j i : ℝ))
    + Real.cos (thetaOf (angleVec x) j) * drhoReal x j i

def ring1Real (x : Fin 12 → ℝ) (j : Fin 9) (i : Fin 7) : ℝ :=
  rhoK x j * (Real.cos (thetaOf (angleVec x) j) * (dTheta j i : ℝ))
    + Real.sin (thetaOf (angleVec x) j) * drhoReal x j i

def arc0Real (x : Fin 12 → ℝ) (j : Fin 9) (i : Fin 7) : ℝ :=
  -(Real.sin (thetaOf (angleVec x) j + angleVec x j)) * ((dTheta j i : ℝ) + (dAngle j i : ℝ))

def arc1Real (x : Fin 12 → ℝ) (j : Fin 9) (i : Fin 7) : ℝ :=
  (Real.cos (thetaOf (angleVec x) j + angleVec x j)) * ((dTheta j i : ℝ) + (dAngle j i : ℝ))

def dUvec0Real (x : Fin 12 → ℝ) (k : Fin 9) (i : Fin 7) : ℝ :=
  ring0Real x k i + ring0Real x (k + 1) i - arc0Real x k i

def dUvec1Real (x : Fin 12 → ℝ) (k : Fin 9) (i : Fin 7) : ℝ :=
  ring1Real x k i + ring1Real x (k + 1) i - arc1Real x k i

def drhoIvBox (j : Fin 9) (i : Fin 7) : RatInterval :=
  sub (mul (neg (sinTotLag (ndAngleBox ndBox j))) (ofRat (((dAngle j i : ℤ) : ℚ))))
    (mul (invPos (twoSqrtWkIvBox j))
      (sub (mul (mul (ofRat 2) (ndBox 6)) (deltaIv 6 i))
        (mul (mul (ofRat 2) (sinTotLag (ndAngleBox ndBox j)))
          (mul (cosTotLag (ndAngleBox ndBox j)) (ofRat (((dAngle j i : ℤ) : ℚ)))))))

def ring0IvBox (j : Fin 9) (i : Fin 7) : RatInterval :=
  add (mul (ndRhoBox ndBox j)
      (mul (neg (sinTotLag (thetaInterval (ndAngleBox ndBox) j)))
        (ofRat (((dTheta j i : ℤ) : ℚ)))))
    (mul (cosTotLag (thetaInterval (ndAngleBox ndBox) j)) (drhoIvBox j i))

def ring1IvBox (j : Fin 9) (i : Fin 7) : RatInterval :=
  add (mul (ndRhoBox ndBox j)
      (mul (cosTotLag (thetaInterval (ndAngleBox ndBox) j))
        (ofRat (((dTheta j i : ℤ) : ℚ)))))
    (mul (sinTotLag (thetaInterval (ndAngleBox ndBox) j)) (drhoIvBox j i))

def arc0IvBox (j : Fin 9) (i : Fin 7) : RatInterval :=
  mul (neg (sinTotLag (add ((thetaInterval (ndAngleBox ndBox)) j) (ndAngleBox ndBox j))))
    (add (ofRat (((dTheta j i : ℤ) : ℚ))) (ofRat (((dAngle j i : ℤ) : ℚ))))

def arc1IvBox (j : Fin 9) (i : Fin 7) : RatInterval :=
  mul (cosTotLag (add ((thetaInterval (ndAngleBox ndBox)) j) (ndAngleBox ndBox j)))
    (add (ofRat (((dTheta j i : ℤ) : ℚ))) (ofRat (((dAngle j i : ℤ) : ℚ))))

def dUvec0IvBox (k : Fin 9) (i : Fin 7) : RatInterval :=
  sub (add (ring0IvBox k i) (ring0IvBox (k + 1) i)) (arc0IvBox k i)

def dUvec1IvBox (k : Fin 9) (i : Fin 7) : RatInterval :=
  sub (add (ring1IvBox k i) (ring1IvBox (k + 1) i)) (arc1IvBox k i)

theorem drhoIvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (j : Fin 9) (i : Fin 7) (h : 0 < (twoSqrtWkIvBox j).lo) :
    (drhoIvBox j i).Mem (drhoReal x j i) := by
  have hQ : ∀ i : Fin 12, (ndBox i).Mem (x i) := ndBox_mem hx
  refine RatInterval.sub_mem ?_ ?_
  · have h1 := RatInterval.mul_mem
      (RatInterval.neg_mem (RatInterval.sinTotLag_mem (ndAngleBox_mem hQ j)))
      (RatInterval.ofRat_mem (((dAngle j i : ℤ) : ℚ)))
    simpa using h1
  · refine RatInterval.mul_mem (invPos_mem_div (twoSqrtWkIvBox_mem hx j) h) ?_
    refine RatInterval.sub_mem ?_ ?_
    · have h1 := RatInterval.mul_mem
        (RatInterval.mul_mem (RatInterval.ofRat_mem (2 : ℚ)) (hQ 6)) (deltaIv_mem 6 i)
      simpa using h1
    · have h1 := RatInterval.mul_mem
        (RatInterval.mul_mem (RatInterval.ofRat_mem (2 : ℚ))
          (RatInterval.sinTotLag_mem (ndAngleBox_mem hQ j)))
        (RatInterval.mul_mem (RatInterval.cosTotLag_mem (ndAngleBox_mem hQ j))
          (RatInterval.ofRat_mem (((dAngle j i : ℤ) : ℚ))))
      simpa using h1

theorem ring0IvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (j : Fin 9) (i : Fin 7) (h : 0 < (twoSqrtWkIvBox j).lo) :
    (ring0IvBox j i).Mem (ring0Real x j i) := by
  have hQ : ∀ i : Fin 12, (ndBox i).Mem (x i) := ndBox_mem hx
  refine RatInterval.add_mem ?_ ?_
  · refine RatInterval.mul_mem (ndRhoBox_mem hQ j) ?_
    refine RatInterval.mul_mem
      (RatInterval.neg_mem (RatInterval.sinTotLag_mem
        (thetaInterval_mem (ndAngleBox_mem hQ) j))) ?_
    simpa using RatInterval.ofRat_mem (((dTheta j i : ℤ) : ℚ))
  · exact RatInterval.mul_mem
      (RatInterval.cosTotLag_mem (thetaInterval_mem (ndAngleBox_mem hQ) j))
      (drhoIvBox_mem hx j i h)

theorem ring1IvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (j : Fin 9) (i : Fin 7) (h : 0 < (twoSqrtWkIvBox j).lo) :
    (ring1IvBox j i).Mem (ring1Real x j i) := by
  have hQ : ∀ i : Fin 12, (ndBox i).Mem (x i) := ndBox_mem hx
  refine RatInterval.add_mem ?_ ?_
  · refine RatInterval.mul_mem (ndRhoBox_mem hQ j) ?_
    refine RatInterval.mul_mem
      (RatInterval.cosTotLag_mem (thetaInterval_mem (ndAngleBox_mem hQ) j)) ?_
    simpa using RatInterval.ofRat_mem (((dTheta j i : ℤ) : ℚ))
  · exact RatInterval.mul_mem
      (RatInterval.sinTotLag_mem (thetaInterval_mem (ndAngleBox_mem hQ) j))
      (drhoIvBox_mem hx j i h)

theorem arc0IvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (j : Fin 9) (i : Fin 7) : (arc0IvBox j i).Mem (arc0Real x j i) := by
  have hQ : ∀ i : Fin 12, (ndBox i).Mem (x i) := ndBox_mem hx
  refine RatInterval.mul_mem
    (RatInterval.neg_mem (RatInterval.sinTotLag_mem
      (RatInterval.add_mem (thetaInterval_mem (ndAngleBox_mem hQ) j)
        (ndAngleBox_mem hQ j)))) ?_
  have h1 := RatInterval.add_mem (RatInterval.ofRat_mem (((dTheta j i : ℤ) : ℚ)))
    (RatInterval.ofRat_mem (((dAngle j i : ℤ) : ℚ)))
  simpa using h1

theorem arc1IvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (j : Fin 9) (i : Fin 7) : (arc1IvBox j i).Mem (arc1Real x j i) := by
  have hQ : ∀ i : Fin 12, (ndBox i).Mem (x i) := ndBox_mem hx
  refine RatInterval.mul_mem
    (RatInterval.cosTotLag_mem
      (RatInterval.add_mem (thetaInterval_mem (ndAngleBox_mem hQ) j)
        (ndAngleBox_mem hQ j))) ?_
  have h1 := RatInterval.add_mem (RatInterval.ofRat_mem (((dTheta j i : ℤ) : ℚ)))
    (RatInterval.ofRat_mem (((dAngle j i : ℤ) : ℚ)))
  simpa using h1

theorem dUvec0IvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (k : Fin 9) (i : Fin 7)
    (h0 : 0 < (twoSqrtWkIvBox k).lo) (h1 : 0 < (twoSqrtWkIvBox (k + 1)).lo) :
    (dUvec0IvBox k i).Mem (dUvec0Real x k i) :=
  RatInterval.sub_mem
    (RatInterval.add_mem (ring0IvBox_mem hx k i h0) (ring0IvBox_mem hx (k + 1) i h1))
    (arc0IvBox_mem hx k i)

theorem dUvec1IvBox_mem {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (k : Fin 9) (i : Fin 7)
    (h0 : 0 < (twoSqrtWkIvBox k).lo) (h1 : 0 < (twoSqrtWkIvBox (k + 1)).lo) :
    (dUvec1IvBox k i).Mem (dUvec1Real x k i) :=
  RatInterval.sub_mem
    (RatInterval.add_mem (ring1IvBox_mem hx k i h0) (ring1IvBox_mem hx (k + 1) i h1))
    (arc1IvBox_mem hx k i)

/-! ## ③bis `dUx` / `dUy` 的盒版（含第 5 行的 `wPoint`） -/

def dUxIvBox : Fin 5 → Fin 7 → RatInterval
  | 0, i => sub (dUvec0IvBox 1 i) (deltaIv 5 i)
  | 1, i => sub (dUvec0IvBox 2 i) (deltaIv 4 i)
  | 2, i => sub (dUvec0IvBox 3 i) (deltaIv 4 i)
  | 3, i => sub (dUvec0IvBox 8 i) (deltaIv 5 i)
  | 4, i => sub (mul (ofRat (1 / 2)) (add (deltaIv 4 i) (deltaIv 5 i))) (ring0IvBox 6 i)

def dUyIvBox : Fin 5 → Fin 7 → RatInterval
  | 0, i => sub (dUvec1IvBox 1 i) (ofRat 0)
  | 1, i => sub (dUvec1IvBox 2 i) (ofRat 0)
  | 2, i => sub (dUvec1IvBox 3 i) (ofRat 0)
  | 3, i => sub (dUvec1IvBox 8 i) (ofRat 0)
  | 4, i => sub (mul (invPos twoSqrtWpIvBox)
      (sub (mul (mul (ofRat 2) (ndBox 6)) (deltaIv 6 i))
        (mul (mul (ofRat 2) (mul (ofRat (1 / 2)) (sub (ndBox 5) (ndBox 4))))
          (mul (ofRat (1 / 2)) (sub (deltaIv 5 i) (deltaIv 4 i))))))
    (ring1IvBox 6 i)

def dUxReal : Fin 5 → Fin 7 → (Fin 12 → ℝ) → ℝ
  | 0, i, x => dUvec0Real x 1 i - (coord 5) (Pi.single i 1)
  | 1, i, x => dUvec0Real x 2 i - (coord 4) (Pi.single i 1)
  | 2, i, x => dUvec0Real x 3 i - (coord 4) (Pi.single i 1)
  | 3, i, x => dUvec0Real x 8 i - (coord 5) (Pi.single i 1)
  | 4, i, x => ((1 / 2 : ℝ) • (coord 4 + coord 5)) (Pi.single i 1) - ring0Real x 6 i

def dUyReal : Fin 5 → Fin 7 → (Fin 12 → ℝ) → ℝ
  | 0, i, x => dUvec1Real x 1 i - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)
  | 1, i, x => dUvec1Real x 2 i - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)
  | 2, i, x => dUvec1Real x 3 i - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)
  | 3, i, x => dUvec1Real x 8 i - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)
  | 4, i, x => ((1 / (2 * Real.sqrt (WpReal x))) • ((2 * x 6) • coord 6
        - (2 * ((x 5 - x 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))) (Pi.single i 1)
      - ring1Real x 6 i

theorem dUxIvBox_mem (k : Fin 5) (i : Fin 7) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (dUxIvBox k i).Mem (dUxReal k i x) := by
  have h2 : ∀ j : Fin 9, 0 < (twoSqrtWkIvBox j).lo := twoSqrtWkIvBox_pos
  fin_cases k
  · simp only [dUxIvBox, dUxReal]
    rw [coord_apply_single 5 i]
    exact RatInterval.sub_mem (dUvec0IvBox_mem hx 1 i (h2 1) (h2 (1 + 1))) (deltaIv_mem 5 i)
  · simp only [dUxIvBox, dUxReal]
    rw [coord_apply_single 4 i]
    exact RatInterval.sub_mem (dUvec0IvBox_mem hx 2 i (h2 2) (h2 (2 + 1))) (deltaIv_mem 4 i)
  · simp only [dUxIvBox, dUxReal]
    rw [coord_apply_single 4 i]
    exact RatInterval.sub_mem (dUvec0IvBox_mem hx 3 i (h2 3) (h2 (3 + 1))) (deltaIv_mem 4 i)
  · simp only [dUxIvBox, dUxReal]
    rw [coord_apply_single 5 i]
    exact RatInterval.sub_mem (dUvec0IvBox_mem hx 8 i (h2 8) (h2 (8 + 1))) (deltaIv_mem 5 i)
  · simp only [dUxIvBox, dUxReal]
    refine RatInterval.sub_mem ?_ (ring0IvBox_mem hx 6 i (h2 6))
    rw [halfAddCoord_single i]
    have h := RatInterval.mul_mem (RatInterval.ofRat_mem (1 / 2 : ℚ))
      (RatInterval.add_mem (deltaIv_mem 4 i) (deltaIv_mem 5 i))
    have hc : (((1 / 2 : ℚ)) : ℝ) = (1 / 2 : ℝ) := by norm_num
    rw [hc] at h
    exact h

theorem dUyIvBox_mem (k : Fin 5) (i : Fin 7) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (dUyIvBox k i).Mem (dUyReal k i x) := by
  have h2 : ∀ j : Fin 9, 0 < (twoSqrtWkIvBox j).lo := twoSqrtWkIvBox_pos
  fin_cases k
  · simp only [dUyIvBox, dUyReal]
    exact RatInterval.sub_mem (dUvec1IvBox_mem hx 1 i (h2 1) (h2 (1 + 1))) (zeroCLM_mem i)
  · simp only [dUyIvBox, dUyReal]
    exact RatInterval.sub_mem (dUvec1IvBox_mem hx 2 i (h2 2) (h2 (2 + 1))) (zeroCLM_mem i)
  · simp only [dUyIvBox, dUyReal]
    exact RatInterval.sub_mem (dUvec1IvBox_mem hx 3 i (h2 3) (h2 (3 + 1))) (zeroCLM_mem i)
  · simp only [dUyIvBox, dUyReal]
    exact RatInterval.sub_mem (dUvec1IvBox_mem hx 8 i (h2 8) (h2 (8 + 1))) (zeroCLM_mem i)
  · simp only [dUyIvBox, dUyReal]
    refine RatInterval.sub_mem ?_ (ring1IvBox_mem hx 6 i (h2 6))
    simp only [smul_apply, sub_apply, smul_eq_mul, coord_apply_single]
    refine RatInterval.mul_mem
      (invPos_mem_div (twoSqrtWpIvBox_mem hx) (twoSqrtWpIvBox_pos WpIvBox_pos)) ?_
    have hQ : ∀ i : Fin 12, (ndBox i).Mem (x i) := ndBox_mem hx
    refine RatInterval.sub_mem ?_ ?_
    · have h := RatInterval.mul_mem
        (RatInterval.mul_mem (RatInterval.ofRat_mem (2 : ℚ)) (hQ 6)) (deltaIv_mem 6 i)
      have hc : ((2 : ℚ) : ℝ) = 2 := by norm_num
      rw [hc] at h
      exact h
    · have h := RatInterval.mul_mem
        (RatInterval.mul_mem (RatInterval.ofRat_mem (2 : ℚ))
          (RatInterval.mul_mem (RatInterval.ofRat_mem (1 / 2 : ℚ))
            (RatInterval.sub_mem (hQ 5) (hQ 4))))
        (RatInterval.mul_mem (RatInterval.ofRat_mem (1 / 2 : ℚ))
          (RatInterval.sub_mem (deltaIv_mem 5 i) (deltaIv_mem 4 i)))
      have hc1 : ((2 : ℚ) : ℝ) = 2 := by norm_num
      have hc2 : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
      have hc3 : (2 : ℝ) * ((1 / 2 : ℝ) * (x 5 - x 4)) = 2 * ((x 5 - x 4) / 2) := by ring
      rw [hc1, hc2, hc3] at h
      exact h

/-! ## ⑤ 复合：`compIv` 的盒版 + 球上 `Mem` -/

def compIvBox (k : Fin 5) (i : Fin 7) : RatInterval :=
  sub (mul (invPos (twoRadSqrtIvBox k))
        (add (mul (mul (ofRat 2) (DxIvBox k)) (dUxIvBox k i))
          (mul (mul (ofRat 2) (DyIvBox k)) (dUyIvBox k i))))
    (deltaIv 6 i)

/-- **⑤ 的球级 `Mem`**（对**逐点真实表达式**；桥到 `fderiv` 属件 C）。
`hrad` 是**唯一**未消前提（`radIvBox k` 的严格正性 = 探针读到的 `Δx²+Δy² ≥ 1.44e-1`）✓。 -/
theorem compIvBox_mem (k : Fin 5) (i : Fin 7) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) (hrad : 0 < (radIvBox k).lo) :
    (compIvBox k i).Mem
      ((1 / (2 * Real.sqrt ((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2
              + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2)))
          * (2 * (((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) * dUxReal k i x
            + 2 * (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) * dUyReal k i x)
        - (if i = 6 then 1 else 0 : ℝ)) := by
  refine RatInterval.sub_mem (RatInterval.mul_mem ?_ ?_) (deltaIv_mem 6 i)
  · exact invPos_mem_div (twoRadSqrtIvBox_mem k hx) (twoRadSqrtIvBox_pos k hrad)
  · refine RatInterval.add_mem ?_ ?_
    · exact RatInterval.mul_mem
        (RatInterval.mul_mem (RatInterval.ofRat_mem 2) (DxIvBox_mem k hx)) (dUxIvBox_mem k i hx)
    · exact RatInterval.mul_mem
        (RatInterval.mul_mem (RatInterval.ofRat_mem 2) (DyIvBox_mem k hx)) (dUyIvBox_mem k i hx)

end N11Formalization

/-! ## 未闭合义务（件 C）

把 `*Real` 桥到 `fderiv ℝ residualFun (first7 x) (Pi.single i 1)` 需要**一般点**的链式法则
（`ResidualDerivNode`/`Node2`/`Dist` 全是**点冻结于 `u0`** 的 ✗）。这是本批最大的真实工作量，
且**本件 A/B 不依赖它**（`*Real` 的 `Mem` 已成立 ✓）。 -/

#print axioms N11Formalization.wkBox_pos
#print axioms N11Formalization.twoSqrtWkIvBox_pos
#print axioms N11Formalization.radIvBox_mem
#print axioms N11Formalization.twoRadSqrtIvBox_pos
#print axioms N11Formalization.WpIvBox_pos
#print axioms N11Formalization.WpIvBox_mem
#print axioms N11Formalization.twoSqrtWpIvBox_pos
#print axioms N11Formalization.drhoIvBox_mem
#print axioms N11Formalization.ring0IvBox_mem
#print axioms N11Formalization.arc1IvBox_mem
#print axioms N11Formalization.dUvec0IvBox_mem
#print axioms N11Formalization.dUxIvBox_mem
#print axioms N11Formalization.dUyIvBox_mem
#print axioms N11Formalization.compIvBox_mem


namespace N11Formalization

open RatInterval

/-! ## ⑥ 试消 `hrad`：`radIvBox k` 的严格正性（= "两批具体正性"之一）

`radIvBox k = (Δx)² + (Δy)²`（`Δ = Apt − Bpt`）。下面逐 `k` 把目标**显形**为
`AptBox`/`BptBox` 的字面量展开（`rfl` 级），再交给 **`NondegProof.nd_eval`** 做内核判定。
-/

/-- **`radIvBox 0` 的严格正性**。 -/
theorem radIvBox_pos_0 : (0 : ℚ) < (radIvBox 0).lo := by
  show (0 : ℚ) < (add (sq (sub ((ndUvecBox ndBox 1) 0) ((ndHub1Box ndBox) 0))) (sq (sub ((ndUvecBox ndBox 1) 1) ((ndHub1Box ndBox) 1)))).lo
  nd_eval

/-- **`radIvBox 1` 的严格正性**。 -/
theorem radIvBox_pos_1 : (0 : ℚ) < (radIvBox 1).lo := by
  show (0 : ℚ) < (add (sq (sub ((ndUvecBox ndBox 2) 0) ((ndHub0Box ndBox) 0))) (sq (sub ((ndUvecBox ndBox 2) 1) ((ndHub0Box ndBox) 1)))).lo
  nd_eval

/-- **`radIvBox 2` 的严格正性**。 -/
theorem radIvBox_pos_2 : (0 : ℚ) < (radIvBox 2).lo := by
  show (0 : ℚ) < (add (sq (sub ((ndUvecBox ndBox 3) 0) ((ndHub0Box ndBox) 0))) (sq (sub ((ndUvecBox ndBox 3) 1) ((ndHub0Box ndBox) 1)))).lo
  nd_eval

/-- **`radIvBox 3` 的严格正性**。 -/
theorem radIvBox_pos_3 : (0 : ℚ) < (radIvBox 3).lo := by
  show (0 : ℚ) < (add (sq (sub ((ndUvecBox ndBox 8) 0) ((ndHub1Box ndBox) 0))) (sq (sub ((ndUvecBox ndBox 8) 1) ((ndHub1Box ndBox) 1)))).lo
  nd_eval

/-- **`radIvBox 4` 的严格正性**。 -/
theorem radIvBox_pos_4 : (0 : ℚ) < (radIvBox 4).lo := by
  show (0 : ℚ) < (add (sq (sub ((ndWPointBox ndBox) 0) ((ndRingBox ndBox 6) 0))) (sq (sub ((ndWPointBox ndBox) 1) ((ndRingBox ndBox 6) 1)))).lo
  nd_eval

/-- **`hrad` 无条件形态**：5 个 `k` 全部 `> 0` ⇒ `compIvBox_mem` 的 `hrad` 可消 ✓。 -/
theorem radIvBox_pos : ∀ k : Fin 5, 0 < (radIvBox k).lo := by
  intro k
  fin_cases k
  · exact radIvBox_pos_0
  · exact radIvBox_pos_1
  · exact radIvBox_pos_2
  · exact radIvBox_pos_3
  · exact radIvBox_pos_4

/-! ## ⑦ **收口**：消掉 `hrad` ⇒ `compIvBox_mem` 的**无条件**形态 -/

/-- **F1 第 2 步的球级 `Mem`（无条件）**：`∀ x ∈ closedBall certCR rhoCertR`、`∀ k i`，
`compIvBox k i` 含**逐点真实表达式**（`Mem` 目标与 `compIvBox_mem` 逐字相同）。
`hrad` 由 `radIvBox_pos` 无条件供给 ✓。 -/
theorem compIvBox_mem_uncond (k : Fin 5) (i : Fin 7) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (compIvBox k i).Mem
      ((1 / (2 * Real.sqrt ((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2
              + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2)))
          * (2 * (((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) * dUxReal k i x
            + 2 * (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) * dUyReal k i x)
        - (if i = 6 then 1 else 0 : ℝ)) :=
  compIvBox_mem k i hx (radIvBox_pos k)

/-- **35 格打包（无条件）**：`∀ k : Fin 5, ∀ i : Fin 7` 的球级 `Mem` 合取。 -/
theorem compIvBox_mem_all (x : Fin 12 → ℝ) (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    ∀ k : Fin 5, ∀ i : Fin 7,
      (compIvBox k i).Mem
        ((1 / (2 * Real.sqrt ((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2
                + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2)))
            * (2 * (((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) * dUxReal k i x
              + 2 * (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) * dUyReal k i x)
          - (if i = 6 then 1 else 0 : ℝ)) :=
  fun k i => compIvBox_mem_uncond k i hx

#print axioms N11Formalization.radIvBox_pos_0
#print axioms N11Formalization.radIvBox_pos
#print axioms N11Formalization.radIvBox_pos_4
#print axioms N11Formalization.compIvBox_mem_uncond
#print axioms N11Formalization.compIvBox_mem_all

end N11Formalization
