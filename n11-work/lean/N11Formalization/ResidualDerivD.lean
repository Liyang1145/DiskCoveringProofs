/-
# `D` 阶段 3 —— **第 2 层：区间 + `hD`**

第 1 层（`ResidualDerivDist.lean`）给出 5 个残差分量的 **real 侧标量导数**。本文件给出
`D : Fin 5 → Fin 7 → RatInterval` 与 **`hD`**：`(D k i).Mem (∂f_k/∂z_i 在盒心)`。

## 设计口径
* **不重写区间算术**：全部叶子复用 `ResidualInterval` 的 `UvecInterval`/`hub*Interval`/
  `wPointInterval`/`ringCenterInterval`/`rhoInterval`/`sinTot`/`cosTot`/`thetaInterval`/
  `angleVecInterval` 及其 `*_mem`（这些是**已在内核验证过**的构件）。
* **`hub` 随 z 变**（第 1 层文件头警语）在区间侧同样体现：`Biv k` 的坐标 0 是 `ofRat (cCert 5/4)`。
* **`inv` 侧显式传正性**：`RatInterval.inv` 取 `h : B.hi < 0 ∨ 0 < B.lo`（`Interval/Core.lean`）；
  `sqrt` 侧**不需要**（定义内已 clamp，`sqrt_mem` 无条件）。为了让 `D` 本身**不带前提**（类型恰好是
  `Fin 5 → Fin 7 → RatInterval`），用 `invPos` 包装：`if h : 0 < B.lo then B.inv (Or.inr h) else ⟨0,0⟩`。
  `hD` 的证明处再把假设喂进 `dif_pos`。
* **未消前提（逐条列明）**：`hWk : ∀ j, 0 < (WkIv j).lo`（9 格）、
  `hrad : ∀ k, 0 < (radIv k).lo`（5 格，= 探针读到的 `Δx²+Δy² ≥ 1.2159e-1`）。
  这两族**正是**「两批具体正性」，各为**有限有理不等式**。

**真实等级**：本文件 kernel-proved（条件形态）。零 `sorry`、零自定义 `axiom`、零 `native_decide`。
-/
import N11Formalization.ResidualDerivDist
import N11Formalization.Transport
import N11Formalization.ResidualIntervalLag

noncomputable section

namespace N11Formalization

open RatInterval

/-! ## 0. `inv` 的**假设无关**包装（让 `D` 的类型恰好是 `Fin 5 → Fin 7 → RatInterval`） -/

/-- `0 < B.lo` 时给 `B⁻¹`，否则给退化区间 `[0,0]`（该分支在 `hD` 里会被 `dif_pos` 排除）。 -/
def invPos (B : RatInterval) : RatInterval :=
  if h : 0 < B.lo then B.inv (Or.inr h) else ⟨0, 0⟩

theorem invPos_mem {B : RatInterval} {y : ℝ} (hB : B.Mem y) (h : 0 < B.lo) :
    (invPos B).Mem y⁻¹ := by
  rw [invPos, dif_pos h]
  exact inv_mem hB (Or.inr h)

/-- **`1/y` 形态**（下游的 real 侧写的是 `1 / (2 * √…)`，与 `y⁻¹` 只差 `one_div`）。 -/
theorem invPos_mem_div {B : RatInterval} {y : ℝ} (hB : B.Mem y) (h : 0 < B.lo) :
    (invPos B).Mem (1 / y) := by
  rw [one_div]
  exact invPos_mem hB h

/-! ## 1. 传输：`pad12 u0` 与 `cCertR`（`u0 = first7 cCertR`） -/

theorem angleVec_u0_eq (j : Fin 9) : angleVec (pad12 u0) j = angleVec cCertR j :=
  congrFun (angleVec_transport cCertR) j

theorem thetaOf_u0_eq (j : Fin 9) :
    thetaOf (angleVec (pad12 u0)) j = thetaOf (angleVec cCertR) j :=
  thetaOf_transport cCertR j

theorem u0_six : u0 6 = cCertR 6 := rfl

theorem Uvec_u0_eq (k : Fin 9) : Uvec (pad12 u0) k = Uvec cCertR k := Uvec_transport cCertR k

theorem hub0_u0 : hub0 (pad12 u0) = hub0 cCertR := hub0_transport cCertR

theorem hub1_u0 : hub1 (pad12 u0) = hub1 cCertR := hub1_transport cCertR

theorem wPoint_u0 : wPoint (pad12 u0) = wPoint cCertR := wPoint_transport cCertR

theorem ringCenter_u0 (k : Fin 9) : ringCenter (pad12 u0) k = ringCenter cCertR k :=
  ringCenter_transport cCertR k

/-! ## 2. 盒心的区间叶子（全部复用 `ResidualInterval`） -/

def sinAIv (j : Fin 9) : RatInterval := sinTotLag (angleVecInterval cCert j)
def cosAIv (j : Fin 9) : RatInterval := cosTotLag (angleVecInterval cCert j)
def sinTIv (j : Fin 9) : RatInterval := sinTotLag (thetaInterval (angleVecInterval cCert) j)
def cosTIv (j : Fin 9) : RatInterval := cosTotLag (thetaInterval (angleVecInterval cCert) j)
def sinTAIv (j : Fin 9) : RatInterval :=
  sinTotLag (add ((thetaInterval (angleVecInterval cCert)) j) ((angleVecInterval cCert) j))
def cosTAIv (j : Fin 9) : RatInterval :=
  cosTotLag (add ((thetaInterval (angleVecInterval cCert)) j) ((angleVecInterval cCert) j))
def rhoIv (j : Fin 9) : RatInterval := rhoIntervalLag cCert j

/-- `Wk j` 的区间版。 -/
def WkIv (j : Fin 9) : RatInterval := sub (sq (ofRat (cCert 6))) (sq (sinAIv j))

/-- `Wp`（`wPoint` 坐标 1 的 radicand）的区间版。 -/
def WpIv : RatInterval :=
  sub (sq (ofRat (cCert 6)))
    (sq (mul (ofRat (1 / 2)) (sub (ofRat (cCert 5)) (ofRat (cCert 4)))))

def sqrtWkIv (j : Fin 9) : RatInterval := (WkIv j).sqrt
def twoSqrtWkIv (j : Fin 9) : RatInterval := mul (ofRat 2) (sqrtWkIv j)

theorem sinAIv_mem (j : Fin 9) : (sinAIv j).Mem (Real.sin (angleVec (pad12 u0) j)) := by
  rw [angleVec_u0_eq j]
  exact sinTotLag_mem (angleVecInterval_mem cCert j)

theorem cosAIv_mem (j : Fin 9) : (cosAIv j).Mem (Real.cos (angleVec (pad12 u0) j)) := by
  rw [angleVec_u0_eq j]
  exact cosTotLag_mem (angleVecInterval_mem cCert j)

theorem sinTIv_mem (j : Fin 9) :
    (sinTIv j).Mem (Real.sin (thetaOf (angleVec (pad12 u0)) j)) := by
  rw [thetaOf_u0_eq j]
  exact sinTotLag_mem (thetaInterval_mem (angleVecInterval_mem cCert) j)

theorem cosTIv_mem (j : Fin 9) :
    (cosTIv j).Mem (Real.cos (thetaOf (angleVec (pad12 u0)) j)) := by
  rw [thetaOf_u0_eq j]
  exact cosTotLag_mem (thetaInterval_mem (angleVecInterval_mem cCert) j)

theorem sinTAIv_mem (j : Fin 9) :
    (sinTAIv j).Mem (Real.sin (thetaOf (angleVec (pad12 u0)) j + angleVec (pad12 u0) j)) := by
  rw [thetaOf_u0_eq j, angleVec_u0_eq j]
  exact sinTotLag_mem (add_mem (thetaInterval_mem (angleVecInterval_mem cCert) j)
    (angleVecInterval_mem cCert j))

theorem cosTAIv_mem (j : Fin 9) :
    (cosTAIv j).Mem (Real.cos (thetaOf (angleVec (pad12 u0)) j + angleVec (pad12 u0) j)) := by
  rw [thetaOf_u0_eq j, angleVec_u0_eq j]
  exact cosTotLag_mem (add_mem (thetaInterval_mem (angleVecInterval_mem cCert) j)
    (angleVecInterval_mem cCert j))

theorem rhoIv_mem (j : Fin 9) : (rhoIv j).Mem (rhoK (pad12 u0) j) := by
  show (rhoIv j).Mem (rhoK (pad12 (first7 cCertR)) j)
  rw [rhoK_transport cCertR j]
  exact rhoIntervalLag_mem cCert j

theorem WkIv_mem (j : Fin 9) : (WkIv j).Mem (Wk j) := by
  rw [Wk, u0_six, angleVec_u0_eq j]
  exact sub_mem (sq_mem_pow (ofRat_mem (cCert 6)))
    (sq_mem_pow (sinTotLag_mem (angleVecInterval_mem cCert j)))

theorem sqrtWkIv_mem (j : Fin 9) : (sqrtWkIv j).Mem (Real.sqrt (Wk j)) :=
  sqrt_mem (WkIv_mem j)

theorem twoSqrtWkIv_mem (j : Fin 9) :
    (twoSqrtWkIv j).Mem (2 * Real.sqrt (Wk j)) := by
  rw [twoSqrtWkIv]
  have h := mul_mem (ofRat_mem (2 : ℚ)) (sqrtWkIv_mem j)
  simpa using h

/-! ## 3. 盒心各角的 `δ`：`Pi.single` 的取值 -/

theorem deltaSix_mem (i : Fin 7) :
    (ofRat (if i = 6 then (1 : ℚ) else 0)).Mem ((if i = 6 then (1 : ℝ) else 0)) := by
  by_cases h : i = 6
  · rw [if_pos h, if_pos h]
    simpa using ofRat_mem (1 : ℚ)
  · rw [if_neg h, if_neg h]
    simpa using ofRat_mem (0 : ℚ)

/-! ## 4. 导数节点的区间包络（镜像 `drhoCLM_single` / `fderiv_Uvec0/1` 的**同一棵树**） -/

/-- `drhoCLM j (single)` 的区间包络（镜像 `drhoCLM_single`）。 -/
def drhoIv (j : Fin 9) (i : Fin 7) : RatInterval :=
  sub (mul (neg (sinAIv j)) (ofRat (((dAngle j i : ℤ) : ℚ))))
    (mul (invPos (twoSqrtWkIv j))
      (sub (mul (ofRat (2 * cCert 6)) (ofRat (if i = 6 then (1 : ℚ) else 0)))
        (mul (mul (ofRat 2) (sinAIv j))
          (mul (cosAIv j) (ofRat (((dAngle j i : ℤ) : ℚ)))))))

/-- `ringCenter` 坐标 0 的导数区间（镜像 `fderiv_Uvec0` 里的第 1 项）。 -/
def ring0Iv (j : Fin 9) (i : Fin 7) : RatInterval :=
  add (mul (rhoIv j) (mul (neg (sinTIv j)) (ofRat (((dTheta j i : ℤ) : ℚ)))))
    (mul (cosTIv j) (drhoIv j i))

/-- `ringCenter` 坐标 1 的导数区间。 -/
def ring1Iv (j : Fin 9) (i : Fin 7) : RatInterval :=
  add (mul (rhoIv j) (mul (cosTIv j) (ofRat (((dTheta j i : ℤ) : ℚ)))))
    (mul (sinTIv j) (drhoIv j i))

/-- `arcEnd` 坐标 0 的导数区间。 -/
def arc0Iv (j : Fin 9) (i : Fin 7) : RatInterval :=
  mul (neg (sinTAIv j))
    (add (ofRat (((dTheta j i : ℤ) : ℚ))) (ofRat (((dAngle j i : ℤ) : ℚ))))

/-- `arcEnd` 坐标 1 的导数区间。 -/
def arc1Iv (j : Fin 9) (i : Fin 7) : RatInterval :=
  mul (cosTAIv j)
    (add (ofRat (((dTheta j i : ℤ) : ℚ))) (ofRat (((dAngle j i : ℤ) : ℚ))))

/-- `Uvec` 坐标 0 沿 `single i 1` 的导数区间 = `dring0 k + dring0 (k+1) − darc0 k` 的镜像。 -/
def dUvec0Iv (k : Fin 9) (i : Fin 7) : RatInterval :=
  sub (add (ring0Iv k i) (ring0Iv (k + 1) i)) (arc0Iv k i)

/-- `Uvec` 坐标 1 沿 `single i 1` 的导数区间。 -/
def dUvec1Iv (k : Fin 9) (i : Fin 7) : RatInterval :=
  sub (add (ring1Iv k i) (ring1Iv (k + 1) i)) (arc1Iv k i)

theorem drhoIv_mem (j : Fin 9) (i : Fin 7) (h : 0 < (twoSqrtWkIv j).lo) :
    (drhoIv j i).Mem (drhoCLM j (Pi.single i 1)) := by
  rw [drhoCLM_single j i]
  refine sub_mem ?_ ?_
  · have h1 := mul_mem (neg_mem (sinAIv_mem j))
      (ofRat_mem (((dAngle j i : ℤ) : ℚ)))
    simpa using h1
  · refine mul_mem (invPos_mem_div (twoSqrtWkIv_mem j) h) ?_
    refine sub_mem ?_ ?_
    · have h1 := mul_mem (ofRat_mem (2 * cCert 6)) (deltaSix_mem i)
      have h2 : ((2 * cCert 6 : ℚ) : ℝ) = 2 * u0 6 := by
        rw [u0_six]
        push_cast
        rfl
      rw [h2] at h1
      exact h1
    · have h1 := mul_mem (mul_mem (ofRat_mem (2 : ℚ)) (sinAIv_mem j))
          (mul_mem (cosAIv_mem j) (ofRat_mem (((dAngle j i : ℤ) : ℚ))))
      simpa using h1

theorem ring0Iv_mem (j : Fin 9) (i : Fin 7) (h : 0 < (twoSqrtWkIv j).lo) :
    (ring0Iv j i).Mem
      (rhoK (pad12 u0) j * (-(Real.sin (thetaOf (angleVec (pad12 u0)) j))
          * (dTheta j i : ℝ))
        + Real.cos (thetaOf (angleVec (pad12 u0)) j) * (drhoCLM j (Pi.single i 1))) := by
  refine add_mem (mul_mem (rhoIv_mem j) (mul_mem (neg_mem (sinTIv_mem j)) ?_)) ?_
  · have h1 := ofRat_mem (((dTheta j i : ℤ) : ℚ))
    simpa using h1
  · exact mul_mem (cosTIv_mem j) (drhoIv_mem j i h)

theorem ring1Iv_mem (j : Fin 9) (i : Fin 7) (h : 0 < (twoSqrtWkIv j).lo) :
    (ring1Iv j i).Mem
      (rhoK (pad12 u0) j * (Real.cos (thetaOf (angleVec (pad12 u0)) j)
          * (dTheta j i : ℝ))
        + Real.sin (thetaOf (angleVec (pad12 u0)) j) * (drhoCLM j (Pi.single i 1))) := by
  refine add_mem (mul_mem (rhoIv_mem j) (mul_mem (cosTIv_mem j) ?_)) ?_
  · have h1 := ofRat_mem (((dTheta j i : ℤ) : ℚ))
    simpa using h1
  · exact mul_mem (sinTIv_mem j) (drhoIv_mem j i h)

theorem arc0Iv_mem (j : Fin 9) (i : Fin 7) :
    (arc0Iv j i).Mem
      (-(Real.sin (thetaOf (angleVec (pad12 u0)) j + angleVec (pad12 u0) j))
        * ((dTheta j i : ℝ) + (dAngle j i : ℝ))) := by
  refine mul_mem (neg_mem (sinTAIv_mem j)) ?_
  have h1 := add_mem (ofRat_mem (((dTheta j i : ℤ) : ℚ)))
    (ofRat_mem (((dAngle j i : ℤ) : ℚ)))
  simpa using h1

theorem arc1Iv_mem (j : Fin 9) (i : Fin 7) :
    (arc1Iv j i).Mem
      ((Real.cos (thetaOf (angleVec (pad12 u0)) j + angleVec (pad12 u0) j))
        * ((dTheta j i : ℝ) + (dAngle j i : ℝ))) := by
  refine mul_mem (cosTAIv_mem j) ?_
  have h1 := add_mem (ofRat_mem (((dTheta j i : ℤ) : ℚ)))
    (ofRat_mem (((dAngle j i : ℤ) : ℚ)))
  simpa using h1

theorem dUvec0Iv_mem (k : Fin 9) (i : Fin 7)
    (h0 : 0 < (twoSqrtWkIv k).lo) (h1 : 0 < (twoSqrtWkIv (k + 1)).lo) :
    (dUvec0Iv k i).Mem
      ((dring0CLM k + dring0CLM (k + 1) - darc0CLM k) (Pi.single i 1)) := by
  rw [fderiv_Uvec0 k i]
  exact sub_mem (add_mem (ring0Iv_mem k i h0) (ring0Iv_mem (k + 1) i h1)) (arc0Iv_mem k i)

theorem dUvec1Iv_mem (k : Fin 9) (i : Fin 7)
    (h0 : 0 < (twoSqrtWkIv k).lo) (h1 : 0 < (twoSqrtWkIv (k + 1)).lo) :
    (dUvec1Iv k i).Mem
      ((dring1CLM k + dring1CLM (k + 1) - darc1CLM k) (Pi.single i 1)) := by
  rw [fderiv_Uvec1 k i]
  exact sub_mem (add_mem (ring1Iv_mem k i h0) (ring1Iv_mem (k + 1) i h1)) (arc1Iv_mem k i)

/-! ## 5. 5→1 化归：第 `k` 个残差的 `(A_k, B_k)`（**`B_k` 也随 z 变**） -/

/-- 第 `k` 个残差 `A_k` 的槽（`k=4` 用 `wPoint`，此槽占位不用）。 -/
def resSlot : Fin 5 → Fin 9
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 8
  | 4 => 0

/-- `B_k` 的**随 z 变的坐标**：`hub1→z₅`、`hub0→z₄`（`k=4` 用 `ringCenter 6`，占位）。 -/
def resHub : Fin 5 → Fin 7
  | 0 => 5
  | 1 => 4
  | 2 => 4
  | 3 => 5
  | 4 => 0

def Apt : Fin 5 → (Fin 12 → ℝ) → Point
  | 0, u => Uvec u 1
  | 1, u => Uvec u 2
  | 2, u => Uvec u 3
  | 3, u => Uvec u 8
  | 4, u => wPoint u

def Bpt : Fin 5 → (Fin 12 → ℝ) → Point
  | 0, u => hub1 u
  | 1, u => hub0 u
  | 2, u => hub0 u
  | 3, u => hub1 u
  | 4, u => ringCenter u 6

def Aiv : Fin 5 → Fin 2 → RatInterval
  | 0 => UvecIntervalLag cCert 1
  | 1 => UvecIntervalLag cCert 2
  | 2 => UvecIntervalLag cCert 3
  | 3 => UvecIntervalLag cCert 8
  | 4 => wPointIntervalLag cCert

def Biv : Fin 5 → Fin 2 → RatInterval
  | 0 => hub1Interval cCert
  | 1 => hub0Interval cCert
  | 2 => hub0Interval cCert
  | 3 => hub1Interval cCert
  | 4 => ringCenterIntervalLag cCert 6

theorem Aiv_mem : ∀ (k : Fin 5) (i : Fin 2), ((Aiv k) i).Mem (((Apt k) (pad12 u0)).ofLp i)
  | 0, 0 => by simp only [Aiv, Apt]; rw [Uvec_u0_eq 1]; exact UvecIntervalLag_mem cCert 1 0
  | 0, 1 => by simp only [Aiv, Apt]; rw [Uvec_u0_eq 1]; exact UvecIntervalLag_mem cCert 1 1
  | 1, 0 => by simp only [Aiv, Apt]; rw [Uvec_u0_eq 2]; exact UvecIntervalLag_mem cCert 2 0
  | 1, 1 => by simp only [Aiv, Apt]; rw [Uvec_u0_eq 2]; exact UvecIntervalLag_mem cCert 2 1
  | 2, 0 => by simp only [Aiv, Apt]; rw [Uvec_u0_eq 3]; exact UvecIntervalLag_mem cCert 3 0
  | 2, 1 => by simp only [Aiv, Apt]; rw [Uvec_u0_eq 3]; exact UvecIntervalLag_mem cCert 3 1
  | 3, 0 => by simp only [Aiv, Apt]; rw [Uvec_u0_eq 8]; exact UvecIntervalLag_mem cCert 8 0
  | 3, 1 => by simp only [Aiv, Apt]; rw [Uvec_u0_eq 8]; exact UvecIntervalLag_mem cCert 8 1
  | 4, 0 => by simp only [Aiv, Apt]; rw [wPoint_u0]; exact wPointIntervalLag_mem cCert 0
  | 4, 1 => by simp only [Aiv, Apt]; rw [wPoint_u0]; exact wPointIntervalLag_mem cCert 1

theorem Biv_mem : ∀ (k : Fin 5) (i : Fin 2), ((Biv k) i).Mem (((Bpt k) (pad12 u0)).ofLp i)
  | 0, 0 => by simp only [Biv, Bpt]; rw [hub1_u0]; exact hub1Interval_mem cCert 0
  | 0, 1 => by simp only [Biv, Bpt]; rw [hub1_u0]; exact hub1Interval_mem cCert 1
  | 1, 0 => by simp only [Biv, Bpt]; rw [hub0_u0]; exact hub0Interval_mem cCert 0
  | 1, 1 => by simp only [Biv, Bpt]; rw [hub0_u0]; exact hub0Interval_mem cCert 1
  | 2, 0 => by simp only [Biv, Bpt]; rw [hub0_u0]; exact hub0Interval_mem cCert 0
  | 2, 1 => by simp only [Biv, Bpt]; rw [hub0_u0]; exact hub0Interval_mem cCert 1
  | 3, 0 => by simp only [Biv, Bpt]; rw [hub1_u0]; exact hub1Interval_mem cCert 0
  | 3, 1 => by simp only [Biv, Bpt]; rw [hub1_u0]; exact hub1Interval_mem cCert 1
  | 4, 0 => by simp only [Biv, Bpt]; rw [ringCenter_u0 6]; exact ringCenterIntervalLag_mem cCert 6 0
  | 4, 1 => by simp only [Biv, Bpt]; rw [ringCenter_u0 6]; exact ringCenterIntervalLag_mem cCert 6 1

/-! ## 6. `Pi.single` 的坐标读数（具名）与 `δ` 区间 -/

theorem coord_apply_single (j i : Fin 7) :
    (coord j) (Pi.single i 1) = (if i = j then (1 : ℝ) else 0) := by
  rw [show (coord j : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1) = (Pi.single i 1 : Fin 7 → ℝ) j
    from rfl]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne (Ne.symm h), if_neg h]

def deltaIv (j i : Fin 7) : RatInterval := ofRat (if i = j then (1 : ℚ) else 0)

theorem deltaIv_mem (j i : Fin 7) :
    (deltaIv j i).Mem ((if i = j then (1 : ℝ) else 0)) := by
  by_cases h : i = j
  · rw [deltaIv, if_pos h, if_pos h]
    simpa using ofRat_mem (1 : ℚ)
  · rw [deltaIv, if_neg h, if_neg h]
    simpa using ofRat_mem (0 : ℚ)

theorem zeroCLM_mem (i : Fin 7) :
    (ofRat 0).Mem ((0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)) := by
  rw [zero_apply]
  simpa using ofRat_mem (0 : ℚ)

/-! ## 7. `Δ`、radicand 与「两批正性」到 `inv` 前提的机械转换 -/

def DxIv (k : Fin 5) : RatInterval := sub ((Aiv k) 0) ((Biv k) 0)
def DyIv (k : Fin 5) : RatInterval := sub ((Aiv k) 1) ((Biv k) 1)
def radIv (k : Fin 5) : RatInterval := add (sq (DxIv k)) (sq (DyIv k))
def radSqrtIv (k : Fin 5) : RatInterval := (radIv k).sqrt
def twoRadSqrtIv (k : Fin 5) : RatInterval := mul (ofRat 2) (radSqrtIv k)

theorem DxIv_mem (k : Fin 5) :
    (DxIv k).Mem (((Apt k) (pad12 u0)).ofLp 0 - ((Bpt k) (pad12 u0)).ofLp 0) :=
  sub_mem (Aiv_mem k 0) (Biv_mem k 0)

theorem DyIv_mem (k : Fin 5) :
    (DyIv k).Mem (((Apt k) (pad12 u0)).ofLp 1 - ((Bpt k) (pad12 u0)).ofLp 1) :=
  sub_mem (Aiv_mem k 1) (Biv_mem k 1)

/-- `Δx² + Δy²` 的区间包含性（`^2` 形态，与 real 侧一致）。 -/
theorem radIv_mem (k : Fin 5) :
    (radIv k).Mem ((((Apt k) (pad12 u0)).ofLp 0 - ((Bpt k) (pad12 u0)).ofLp 0) ^ 2
      + (((Apt k) (pad12 u0)).ofLp 1 - ((Bpt k) (pad12 u0)).ofLp 1) ^ 2) :=
  add_mem (sq_mem_pow (DxIv_mem k)) (sq_mem_pow (DyIv_mem k))

theorem twoRadSqrtIv_mem (k : Fin 5) :
    (twoRadSqrtIv k).Mem (2 * Real.sqrt ((((Apt k) (pad12 u0)).ofLp 0
      - ((Bpt k) (pad12 u0)).ofLp 0) ^ 2
      + (((Apt k) (pad12 u0)).ofLp 1 - ((Bpt k) (pad12 u0)).ofLp 1) ^ 2)) := by
  rw [twoRadSqrtIv, radSqrtIv]
  have h := mul_mem (ofRat_mem (2 : ℚ)) (sqrt_mem (radIv_mem k))
  simpa using h

/-- `0 < q ⟹ 0 < sqrtLo q`（`sqrtLo` 在 `q ≤ 0` 时退化为 `0`）。 -/
theorem sqrtLo_pos {q : ℚ} (hq : 0 < q) : 0 < sqrtLo q := by
  rw [sqrtLo, if_neg (not_le.mpr hq)]
  have hnum : 0 < q.num.natAbs := by
    have := Rat.num_pos.mpr hq
    omega
  have hden : 0 < q.den := q.den_pos
  have hprod : 0 < q.num.natAbs * q.den := Nat.mul_pos hnum hden
  have hs : 0 < Nat.sqrt (q.num.natAbs * q.den) := Nat.sqrt_pos.mpr hprod
  have hs' : (0 : ℚ) < ((Nat.sqrt (q.num.natAbs * q.den) : ℕ) : ℚ) := by
    exact_mod_cast hs
  exact div_pos hs' (by exact_mod_cast hden)

/-- `0 < B.lo` 与 `Valid B` ⟹ `0 < (mul (ofRat 2) B).lo`（`mul` 的四角是 `2·lo, 2·hi`）。 -/
theorem twoMulIv_pos (B : RatInterval) (h : 0 < B.lo) (hV : Valid B) :
    0 < (mul (ofRat 2) B).lo := by
  have h1 : (0 : ℚ) < 2 * B.lo := mul_pos (by norm_num) h
  have h2 : (0 : ℚ) < 2 * B.hi := mul_pos (by norm_num) (lt_of_lt_of_le h hV)
  unfold mul ofRat
  dsimp only
  exact lt_min (lt_min h1 h2) (lt_min h1 h2)

/-- `0 < (radIv k).lo ⟹ 0 < (twoRadSqrtIv k).lo`（`inv` 侧的前提）。 -/
theorem twoRadSqrtIv_pos (k : Fin 5) (h : 0 < (radIv k).lo) :
    0 < (twoRadSqrtIv k).lo :=
  twoMulIv_pos (radSqrtIv k) (sqrtLo_pos h) (valid_of_mem (sqrt_mem (radIv_mem k)))

/-- `0 < (radIv k).lo` ⟹ 两点分离（`Δx²+Δy² > 0`）。 -/
theorem sq_sum_ne_of_rad (k : Fin 5) (h : 0 < (radIv k).lo) :
    (((Apt k) (pad12 u0)).ofLp 0 - ((Bpt k) (pad12 u0)).ofLp 0) ^ 2
      + (((Apt k) (pad12 u0)).ofLp 1 - ((Bpt k) (pad12 u0)).ofLp 1) ^ 2 ≠ 0 := by
  intro hzero
  have hle := mem_lo_le (radIv_mem k)
  rw [hzero] at hle
  have hpos : (0 : ℝ) < ((radIv k).lo : ℝ) := by exact_mod_cast h
  linarith

/-- `0 < (WkIv j).lo ⟹ Wk j ≠ 0`。 -/
theorem Wk_ne_zero (j : Fin 9) (h : 0 < (WkIv j).lo) : Wk j ≠ 0 := by
  intro hz
  have hle := mem_lo_le (WkIv_mem j)
  rw [hz] at hle
  have hpos : (0 : ℝ) < ((WkIv j).lo : ℝ) := by exact_mod_cast h
  linarith

/-! ## 8. `Uvec` 版 `k=0..3` 的 Δ 导数区间 -/

def dUxIv (k : Fin 5) (i : Fin 7) : RatInterval :=
  sub (dUvec0Iv (resSlot k) i) (deltaIv (resHub k) i)

def dUyIv (k : Fin 5) (i : Fin 7) : RatInterval :=
  sub (dUvec1Iv (resSlot k) i) (ofRat 0)

theorem dUxIv_mem (k : Fin 5) (i : Fin 7)
    (h0 : 0 < (twoSqrtWkIv (resSlot k)).lo)
    (h1 : 0 < (twoSqrtWkIv ((resSlot k) + 1)).lo) :
    (dUxIv k i).Mem
      ((dring0CLM (resSlot k) + dring0CLM ((resSlot k) + 1) - darc0CLM (resSlot k))
          (Pi.single i 1) - (coord (resHub k)) (Pi.single i 1)) := by
  refine sub_mem (dUvec0Iv_mem (resSlot k) i h0 h1) ?_
  rw [coord_apply_single (resHub k) i]
  exact deltaIv_mem (resHub k) i

theorem dUyIv_mem (k : Fin 5) (i : Fin 7)
    (h0 : 0 < (twoSqrtWkIv (resSlot k)).lo)
    (h1 : 0 < (twoSqrtWkIv ((resSlot k) + 1)).lo) :
    (dUyIv k i).Mem
      ((dring1CLM (resSlot k) + dring1CLM ((resSlot k) + 1) - darc1CLM (resSlot k))
          (Pi.single i 1) - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)) :=
  sub_mem (dUvec1Iv_mem (resSlot k) i h0 h1) (zeroCLM_mem i)

/-! ## 9. `D` 的分量行（镜像 `fderiv_residualComp` 的**同一棵树**） -/

def compIv (k : Fin 5) (i : Fin 7) : RatInterval :=
  sub (mul (invPos (twoRadSqrtIv k))
        (add (mul (mul (ofRat 2) (DxIv k)) (dUxIv k i))
          (mul (mul (ofRat 2) (DyIv k)) (dUyIv k i))))
    (deltaIv 6 i)

theorem compIv_mem (k : Fin 5) (i : Fin 7)
    (h0 : 0 < (twoSqrtWkIv (resSlot k)).lo)
    (h1 : 0 < (twoSqrtWkIv ((resSlot k) + 1)).lo)
    (hrad : 0 < (radIv k).lo) :
    (compIv k i).Mem
      ((1 / (2 * Real.sqrt ((((Apt k) (pad12 u0)).ofLp 0 - ((Bpt k) (pad12 u0)).ofLp 0) ^ 2
              + (((Apt k) (pad12 u0)).ofLp 1 - ((Bpt k) (pad12 u0)).ofLp 1) ^ 2)))
          * (2 * (((Apt k) (pad12 u0)).ofLp 0 - ((Bpt k) (pad12 u0)).ofLp 0)
              * ((dring0CLM (resSlot k) + dring0CLM ((resSlot k) + 1) - darc0CLM (resSlot k))
                  (Pi.single i 1) - (coord (resHub k)) (Pi.single i 1))
            + 2 * (((Apt k) (pad12 u0)).ofLp 1 - ((Bpt k) (pad12 u0)).ofLp 1)
              * ((dring1CLM (resSlot k) + dring1CLM ((resSlot k) + 1) - darc1CLM (resSlot k))
                  (Pi.single i 1) - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ)) := by
  refine sub_mem (mul_mem (invPos_mem_div (twoRadSqrtIv_mem k) (twoRadSqrtIv_pos k hrad))
    (add_mem (mul_mem (mul_mem (ofRat_mem 2) (DxIv_mem k)) (dUxIv_mem k i h0 h1))
      (mul_mem (mul_mem (ofRat_mem 2) (DyIv_mem k)) (dUyIv_mem k i h0 h1))))
    (deltaIv_mem 6 i)

/-! ## 9b. 第 5 行（`k=4`）：`wPoint` / `ringCenter 6`（`Wp` 的 `sqrt` 侧正性单列） -/

theorem u0_five : u0 5 = cCertR 5 := rfl

theorem u0_four : u0 4 = cCertR 4 := rfl

def sqrtWpIv : RatInterval := WpIv.sqrt

def twoSqrtWpIv : RatInterval := mul (ofRat 2) sqrtWpIv

theorem WpIv_mem : WpIv.Mem Wp := by
  rw [Wp, u0_six, u0_five, u0_four]
  refine sub_mem (sq_mem_pow (ofRat_mem (cCert 6))) (sq_mem_pow ?_)
  have h : ((cCertR 5 - cCertR 4) / 2)
      = (((1 / 2 : ℚ) : ℝ) * ((cCert 5 : ℝ) - (cCert 4 : ℝ))) := by
    simp only [cCertR]
    push_cast
    ring
  rw [h]
  exact mul_mem (ofRat_mem (1 / 2)) (sub_mem (ofRat_mem (cCert 5)) (ofRat_mem (cCert 4)))

theorem sqrtWpIv_mem : sqrtWpIv.Mem (Real.sqrt Wp) := sqrt_mem WpIv_mem

theorem twoSqrtWpIv_mem : twoSqrtWpIv.Mem (2 * Real.sqrt Wp) := by
  rw [twoSqrtWpIv, sqrtWpIv]
  have h := mul_mem (ofRat_mem (2 : ℚ)) (sqrt_mem WpIv_mem)
  simpa using h

theorem twoSqrtWpIv_pos (h : 0 < WpIv.lo) : 0 < twoSqrtWpIv.lo :=
  twoMulIv_pos sqrtWpIv (sqrtLo_pos h) (valid_of_mem sqrtWpIv_mem)

theorem Wp_ne_zero (h : 0 < WpIv.lo) : Wp ≠ 0 := by
  intro hz
  have hle := mem_lo_le WpIv_mem
  rw [hz] at hle
  have hpos : (0 : ℝ) < ((WpIv.lo : ℚ) : ℝ) := by exact_mod_cast h
  linarith

/-- `wPoint` 坐标 0 的导数区间（`(1/2)•(coord 4 + coord 5)` 的镜像）。 -/
def dUx4Iv (i : Fin 7) : RatInterval :=
  sub (mul (ofRat (1 / 2)) (add (deltaIv 4 i) (deltaIv 5 i))) (ring0Iv 6 i)

/-- `wPoint` 坐标 1 的导数区间（`(1/(2√Wp))•(…)` 的镜像）。 -/
def dUy4Iv (i : Fin 7) : RatInterval :=
  sub (mul (invPos twoSqrtWpIv)
      (sub (mul (ofRat (2 * cCert 6)) (deltaIv 6 i))
        (mul (ofRat (2 * ((cCert 5 - cCert 4) / 2)))
          (mul (ofRat (1 / 2)) (sub (deltaIv 5 i) (deltaIv 4 i))))))
    (ring1Iv 6 i)

theorem halfAddCoord_single (i : Fin 7) :
    ((1 / 2 : ℝ) • (coord 4 + coord 5)) (Pi.single i 1)
      = (1 / 2) * ((if i = 4 then (1 : ℝ) else 0) + (if i = 5 then (1 : ℝ) else 0)) := by
  simp only [smul_apply, add_apply, smul_eq_mul, coord_apply_single]

theorem wpY_single (i : Fin 7) :
    ((1 / (2 * Real.sqrt Wp)) • ((2 * u0 6) • coord 6
        - (2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))))
        (Pi.single i 1)
      = (1 / (2 * Real.sqrt Wp)) * ((2 * u0 6) * (if i = 6 then (1 : ℝ) else 0)
          - (2 * ((u0 5 - u0 4) / 2)) * ((1 / 2) * ((if i = 5 then (1 : ℝ) else 0)
              - (if i = 4 then (1 : ℝ) else 0)))) := by
  simp only [smul_apply, sub_apply, smul_eq_mul, coord_apply_single]

theorem dUx4Iv_mem (i : Fin 7) (hW6 : 0 < (twoSqrtWkIv 6).lo) :
    (dUx4Iv i).Mem
      (((1 / 2 : ℝ) • (coord 4 + coord 5)) (Pi.single i 1)
        - dring0CLM 6 (Pi.single i 1)) := by
  refine sub_mem ?_ ?_
  · rw [halfAddCoord_single i]
    have h := mul_mem (ofRat_mem ((1 / 2 : ℚ)))
      (add_mem (deltaIv_mem 4 i) (deltaIv_mem 5 i))
    have hc : (((1 / 2 : ℚ)) : ℝ) = (1 / 2 : ℝ) := by norm_num
    rw [hc] at h
    exact h
  · rw [dring0CLM_single 6 i]
    exact ring0Iv_mem 6 i hW6

theorem dUy4Iv_mem (i : Fin 7) (hW6 : 0 < (twoSqrtWkIv 6).lo) (hWp : 0 < WpIv.lo) :
    (dUy4Iv i).Mem
      (((1 / (2 * Real.sqrt Wp)) • ((2 * u0 6) • coord 6
          - (2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))))
          (Pi.single i 1) - dring1CLM 6 (Pi.single i 1)) := by
  refine sub_mem ?_ ?_
  · rw [wpY_single i]
    refine mul_mem (invPos_mem_div twoSqrtWpIv_mem (twoSqrtWpIv_pos hWp)) ?_
    refine sub_mem ?_ ?_
    · have h := mul_mem (ofRat_mem (2 * cCert 6)) (deltaIv_mem 6 i)
      have hc : (((2 * cCert 6 : ℚ)) : ℝ) = 2 * u0 6 := by
        push_cast
        rw [u0_six, cCertR]
      rw [hc] at h
      exact h
    · have h := mul_mem (ofRat_mem (2 * ((cCert 5 - cCert 4) / 2)))
          (mul_mem (ofRat_mem ((1 / 2 : ℚ)))
            (sub_mem (deltaIv_mem 5 i) (deltaIv_mem 4 i)))
      have hc1 : (((2 * ((cCert 5 - cCert 4) / 2) : ℚ)) : ℝ)
          = 2 * ((u0 5 - u0 4) / 2) := by
        simp only [u0_five, u0_four, cCertR]
        push_cast
        ring
      have hc2 : (((1 / 2 : ℚ)) : ℝ) = (1 / 2 : ℝ) := by norm_num
      rw [hc1, hc2] at h
      exact h
  · rw [dring1CLM_single 6 i]
    exact ring1Iv_mem 6 i hW6

def compIv4 (i : Fin 7) : RatInterval :=
  sub (mul (invPos (twoRadSqrtIv 4))
        (add (mul (mul (ofRat 2) (DxIv 4)) (dUx4Iv i))
          (mul (mul (ofRat 2) (DyIv 4)) (dUy4Iv i))))
    (deltaIv 6 i)

theorem compIv4_mem (i : Fin 7) (hW6 : 0 < (twoSqrtWkIv 6).lo) (hWp : 0 < WpIv.lo)
    (hrad : 0 < (radIv 4).lo) :
    (compIv4 i).Mem
      ((1 / (2 * Real.sqrt ((((Apt 4) (pad12 u0)).ofLp 0 - ((Bpt 4) (pad12 u0)).ofLp 0) ^ 2
              + (((Apt 4) (pad12 u0)).ofLp 1 - ((Bpt 4) (pad12 u0)).ofLp 1) ^ 2)))
          * (2 * (((Apt 4) (pad12 u0)).ofLp 0 - ((Bpt 4) (pad12 u0)).ofLp 0)
              * (((1 / 2 : ℝ) • (coord 4 + coord 5)) (Pi.single i 1)
                - dring0CLM 6 (Pi.single i 1))
            + 2 * (((Apt 4) (pad12 u0)).ofLp 1 - ((Bpt 4) (pad12 u0)).ofLp 1)
              * (((1 / (2 * Real.sqrt Wp)) • ((2 * u0 6) • coord 6
                    - (2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))))
                  (Pi.single i 1) - dring1CLM 6 (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ)) :=
  sub_mem (mul_mem (invPos_mem_div (twoRadSqrtIv_mem 4) (twoRadSqrtIv_pos 4 hrad))
    (add_mem (mul_mem (mul_mem (ofRat_mem 2) (DxIv_mem 4)) (dUx4Iv_mem i hW6))
      (mul_mem (mul_mem (ofRat_mem 2) (DyIv_mem 4)) (dUy4Iv_mem i hW6 hWp))))
    (deltaIv_mem 6 i)

/-- **`D`（`Fin 5 × Fin 7` = 35 格）**：残差导数的**结构式**区间包络（未用外部数值表作端点来源）。 -/
def D : Fin 5 → Fin 7 → RatInterval
  | 0 => compIv 0
  | 1 => compIv 1
  | 2 => compIv 2
  | 3 => compIv 3
  | 4 => compIv4

/-! ## 10. 桥：`(fderiv ℝ residualFun u0 s) k` ↔ 分量的 `fderiv` -/

/-- `fderiv ℝ` 与坐标投影交换（`fderiv_apply` + `proj`）。 -/
theorem fderiv_apply_single (k : Fin 5) (i : Fin 7)
    (hd : DifferentiableAt ℝ residualFun u0) :
    ((fderiv ℝ residualFun u0) (Pi.single i 1)) k
      = (fderiv ℝ (fun z : Fin 7 → ℝ => residualFun z k) u0) (Pi.single i 1) := by
  rw [fderiv_apply hd k]
  rfl

/-! ## 11. `hD`（条件形态）：4 行 × 7 列 -/

theorem hD_0 (hd : DifferentiableAt ℝ residualFun u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (i : Fin 7) :
    (D 0 i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) 0) := by
  have h2 : ∀ j : Fin 9, 0 < (twoSqrtWkIv j).lo := fun j =>
    twoMulIv_pos (sqrtWkIv j) (sqrtLo_pos (hWk j)) (valid_of_mem (sqrtWkIv_mem j))
  rw [show fderiv ℝ residualFun (first7 cCertR) = fderiv ℝ residualFun u0 from rfl]
  rw [fderiv_apply_single 0 i hd]
  rw [fderiv_residual_0 i (Wk_ne_zero 1 (hWk 1)) (Wk_ne_zero (1 + 1) (hWk (1 + 1)))
    (sq_sum_ne_of_rad 0 (hrad 0))]
  exact compIv_mem 0 i (h2 1) (h2 (1 + 1)) (hrad 0)

theorem hD_1 (hd : DifferentiableAt ℝ residualFun u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (i : Fin 7) :
    (D 1 i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) 1) := by
  have h2 : ∀ j : Fin 9, 0 < (twoSqrtWkIv j).lo := fun j =>
    twoMulIv_pos (sqrtWkIv j) (sqrtLo_pos (hWk j)) (valid_of_mem (sqrtWkIv_mem j))
  rw [show fderiv ℝ residualFun (first7 cCertR) = fderiv ℝ residualFun u0 from rfl]
  rw [fderiv_apply_single 1 i hd]
  rw [fderiv_residual_1 i (Wk_ne_zero 2 (hWk 2)) (Wk_ne_zero (2 + 1) (hWk (2 + 1)))
    (sq_sum_ne_of_rad 1 (hrad 1))]
  exact compIv_mem 1 i (h2 2) (h2 (2 + 1)) (hrad 1)

theorem hD_2 (hd : DifferentiableAt ℝ residualFun u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (i : Fin 7) :
    (D 2 i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) 2) := by
  have h2 : ∀ j : Fin 9, 0 < (twoSqrtWkIv j).lo := fun j =>
    twoMulIv_pos (sqrtWkIv j) (sqrtLo_pos (hWk j)) (valid_of_mem (sqrtWkIv_mem j))
  rw [show fderiv ℝ residualFun (first7 cCertR) = fderiv ℝ residualFun u0 from rfl]
  rw [fderiv_apply_single 2 i hd]
  rw [fderiv_residual_2 i (Wk_ne_zero 3 (hWk 3)) (Wk_ne_zero (3 + 1) (hWk (3 + 1)))
    (sq_sum_ne_of_rad 2 (hrad 2))]
  exact compIv_mem 2 i (h2 3) (h2 (3 + 1)) (hrad 2)

theorem hD_3 (hd : DifferentiableAt ℝ residualFun u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (i : Fin 7) :
    (D 3 i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) 3) := by
  have h2 : ∀ j : Fin 9, 0 < (twoSqrtWkIv j).lo := fun j =>
    twoMulIv_pos (sqrtWkIv j) (sqrtLo_pos (hWk j)) (valid_of_mem (sqrtWkIv_mem j))
  rw [show fderiv ℝ residualFun (first7 cCertR) = fderiv ℝ residualFun u0 from rfl]
  rw [fderiv_apply_single 3 i hd]
  rw [fderiv_residual_3 i (Wk_ne_zero 8 (hWk 8)) (Wk_ne_zero (8 + 1) (hWk (8 + 1)))
    (sq_sum_ne_of_rad 3 (hrad 3))]
  exact compIv_mem 3 i (h2 8) (h2 (8 + 1)) (hrad 3)

theorem hD_4 (hd : DifferentiableAt ℝ residualFun u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hWp : 0 < WpIv.lo)
    (hrad : ∀ k : Fin 5, 0 < (radIv k).lo) (i : Fin 7) :
    (D 4 i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) 4) := by
  have h6 : 0 < (twoSqrtWkIv 6).lo :=
    twoMulIv_pos (sqrtWkIv 6) (sqrtLo_pos (hWk 6)) (valid_of_mem (sqrtWkIv_mem 6))
  rw [show fderiv ℝ residualFun (first7 cCertR) = fderiv ℝ residualFun u0 from rfl]
  rw [fderiv_apply_single 4 i hd]
  rw [fderiv_residual_4 i (Wk_ne_zero 6 (hWk 6)) (Wp_ne_zero hWp) (sq_sum_ne_of_rad 4 (hrad 4))]
  exact compIv4_mem i h6 hWp (hrad 4)

end N11Formalization
