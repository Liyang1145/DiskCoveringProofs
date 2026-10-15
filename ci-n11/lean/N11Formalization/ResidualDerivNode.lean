import N11Formalization.ResidualDeriv

/-!
# `D` 阶段 2 的**首个非线性节点**：`rhoK`（条件版，`W_k ≠ 0` 作显式前提）

**对象**：`ρ_k(z) = cos(a_k(z)) − √(R² − sin²(a_k(z)))`（`SourceIdentity.rhoK_eq` 是 `rfl` 级定义展开），
`z = (a0,a1,a2,a3,y0,y1,R)`、`R = z 6`、`a_k(z) = angleVec (pad12 z) k`。

**本文件交付（kernel-proved）**：
* `daCLM k`：`a_k` 在 `u0` 处的导数（CLM `∑_i dAngle k i • coord i`）；
* `hasFDerivAt_angleVec`：`HasFDerivAt (angleVec ∘ pad12 · k) (daCLM k) u0`（由脊柱的仿射性）；
* `Wk k`：盒心处的 radicand `R² − sin²a_k`；`hasFDerivAt_radicand`：它的导数；
* **`hasFDerivAt_rhoK (k) (hW : Wk k ≠ 0)`**：`ρ_k` 的链式导数（CLM 形式）；
* **`fderiv_rhoK (k) (i) (hW)`**：沿 `Pi.single i 1` 的**标量**读数（即 `∂ρ_k/∂z_i` 的包络表达式）。

**尚未闭合的唯一前提**：`Wk k ≠ 0`（盒心处 `W_k > 0`，实测最小 `k=4: 1.0931e-3`）。
它可走**纯有理**路线：`W_k = (R − sin a_k)(R + sin a_k)`，两因子皆正 —— 前者用
`Trig.sin_le_sinHi`（或阶乘版 `sin_le_sinHiNLag`）在**具体有理** `a_k` 上 `norm_num` 比较即可
（证书盒上 `sinHi 0.3883 ≈ 0.3786 < R ≈ 0.37997`，余量 ≈ 1.3e-3 ⇒ 安全）。
该 `hW` 的 9 个 `k` 是**下一步**（本文件先把它作为显式前提，避免假装无条件）。

**宽度预算**（已先算，见 `evidence/fm-eval/drho_budget.py` / C1064）：阶乘余项三角界下
`∂ρ_k/∂z_i` 的 63 格最大宽度 **6.86e-17**（放大因子 `1/(2√W) ≤ 15.12`）⇒ 该列安全。
-/

noncomputable section

namespace N11Formalization

open RatInterval

/-- `a_k` 在 `u0` 处的导数（CLM）。 -/
def daCLM (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ℝ := ∑ i : Fin 7, (dAngle k i : ℝ) • coord i

/-- `a_k = angleVec (pad12 ·) k` 在 `u0` 处的导数。 -/
theorem hasFDerivAt_angleVec (k : Fin 9) :
    HasFDerivAt (fun z : Fin 7 → ℝ => angleVec (pad12 z) k) (daCLM k) u0 := by
  have hlin : HasFDerivAt (fun z : Fin 7 → ℝ => ∑ i : Fin 7, (dAngle k i : ℝ) * z i)
      (∑ i : Fin 7, (dAngle k i : ℝ) • coord i) u0 := by
    rw [show (fun z : Fin 7 → ℝ => ∑ i : Fin 7, (dAngle k i : ℝ) * z i)
        = ∑ i : Fin 7, fun z : Fin 7 → ℝ => (dAngle k i : ℝ) * z i from rfl]
    refine HasFDerivAt.sum fun i _ => ?_
    have h1 : HasFDerivAt (⇑(coord i)) (coord i) u0 :=
      ContinuousLinearMap.hasFDerivAt (f := coord i) (x := u0)
    exact h1.const_mul ((dAngle k i : ℝ))
  have h : (fun z : Fin 7 → ℝ => angleVec (pad12 z) k)
      = fun z => angleVec (pad12 0) k + ∑ i : Fin 7, (dAngle k i : ℝ) * z i := by
    funext z
    exact angleVec_pad12_affine k z
  rw [h, daCLM]
  exact hlin.const_add (angleVec (pad12 0) k)

/-- 盒心处的 radicand `W_k = R² − sin²a_k`。 -/
def Wk (k : Fin 9) : ℝ := (u0 6) ^ 2 - (Real.sin (angleVec (pad12 u0) k)) ^ 2

/-- `z ↦ (z 6)² − sin²(a_k z)` 在 `u0` 处的导数。 -/
theorem hasFDerivAt_radicand (k : Fin 9) :
    HasFDerivAt (fun z : Fin 7 → ℝ => (z 6) ^ 2 - (Real.sin (angleVec (pad12 z) k)) ^ 2)
      ((2 * u0 6) • coord 6
        - (2 * Real.sin (angleVec (pad12 u0) k)) • ((Real.cos (angleVec (pad12 u0) k)) • daCLM k))
      u0 := by
  have hR : HasFDerivAt (fun z : Fin 7 → ℝ => z 6) (coord 6) u0 :=
    ContinuousLinearMap.hasFDerivAt (f := coord 6) (x := u0)
  have hR2 : HasFDerivAt (fun z : Fin 7 → ℝ => (z 6) ^ 2) ((2 * u0 6) • coord 6) u0 := by
    have h := hR.pow 2
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using h
  have hs : HasFDerivAt (fun z : Fin 7 → ℝ => Real.sin (angleVec (pad12 z) k))
      ((Real.cos (angleVec (pad12 u0) k)) • daCLM k) u0 :=
    (hasFDerivAt_angleVec k).sin
  have hs2 : HasFDerivAt (fun z : Fin 7 → ℝ => (Real.sin (angleVec (pad12 z) k)) ^ 2)
      ((2 * Real.sin (angleVec (pad12 u0) k))
        • ((Real.cos (angleVec (pad12 u0) k)) • daCLM k)) u0 := by
    have h := hs.pow 2
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using h
  exact hR2.sub hs2

/-- **`rhoK` 的链式导数（CLM 形式，条件版）**：`W_k ≠ 0` 是 `sqrt` 可微的唯一前提。 -/
theorem hasFDerivAt_rhoK (k : Fin 9) (hW : Wk k ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => rhoK (pad12 z) k)
      (-(Real.sin (angleVec (pad12 u0) k)) • daCLM k
        - (1 / (2 * Real.sqrt (Wk k))) • ((2 * u0 6) • coord 6
            - (2 * Real.sin (angleVec (pad12 u0) k))
              • ((Real.cos (angleVec (pad12 u0) k)) • daCLM k)))
      u0 := by
  have heq : (fun z : Fin 7 → ℝ => rhoK (pad12 z) k)
      = fun z => Real.cos (angleVec (pad12 z) k)
        - Real.sqrt ((z 6) ^ 2 - (Real.sin (angleVec (pad12 z) k)) ^ 2) := by
    funext z
    rw [rhoK_eq]
    rfl
  rw [heq]
  have h1 := (hasFDerivAt_angleVec k).cos
  have h2 := (hasFDerivAt_radicand k).sqrt (by simpa [Wk] using hW)
  exact h1.sub h2

/-- `daCLM k` 在 `Pi.single i 1` 上的取值 = `dAngle k i`。 -/
theorem daCLM_apply_single (k : Fin 9) (i : Fin 7) :
    daCLM k (Pi.single i 1) = (dAngle k i : ℝ) := by
  rw [daCLM, sum_apply]
  have hterm : ∀ j : Fin 7, (((dAngle k j : ℝ)) • coord j) (Pi.single i 1)
      = ((dAngle k j : ℝ)) * (Pi.single i 1 : Fin 7 → ℝ) j := by
    intro j
    rw [smul_apply, smul_eq_mul]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  exact sum_mul_single (fun j : Fin 7 => ((dAngle k j : ℝ))) i

/-- `coord 6` 在 `Pi.single i 1` 上的取值 = `if i = 6 then 1 else 0`。 -/
theorem coord_six_apply_single (i : Fin 7) :
    (coord 6) (Pi.single i 1) = (if i = 6 then 1 else 0 : ℝ) := by
  rw [show (coord 6 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1) = (Pi.single i 1 : Fin 7 → ℝ) 6
    from rfl]
  by_cases h : i = 6
  · subst h
    rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne (Ne.symm h), if_neg h]

/-- `θ_j` 在 `u0` 处的导数（CLM）。 -/
def dthetaCLM (j : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ℝ := ∑ i : Fin 7, (dTheta j i : ℝ) • coord i

/-- `θ_j = thetaOf (angleVec (pad12 ·)) j` 在 `u0` 处的导数。 -/
theorem hasFDerivAt_thetaOf (j : Fin 9) :
    HasFDerivAt (fun z : Fin 7 → ℝ => thetaOf (angleVec (pad12 z)) j) (dthetaCLM j) u0 := by
  have hlin : HasFDerivAt (fun z : Fin 7 → ℝ => ∑ i : Fin 7, (dTheta j i : ℝ) * z i)
      (∑ i : Fin 7, (dTheta j i : ℝ) • coord i) u0 := by
    rw [show (fun z : Fin 7 → ℝ => ∑ i : Fin 7, (dTheta j i : ℝ) * z i)
        = ∑ i : Fin 7, fun z : Fin 7 → ℝ => (dTheta j i : ℝ) * z i from rfl]
    refine HasFDerivAt.sum fun i _ => ?_
    have h1 : HasFDerivAt (⇑(coord i)) (coord i) u0 :=
      ContinuousLinearMap.hasFDerivAt (f := coord i) (x := u0)
    exact h1.const_mul ((dTheta j i : ℝ))
  have h : (fun z : Fin 7 → ℝ => thetaOf (angleVec (pad12 z)) j)
      = fun z => thetaOf (angleVec (pad12 0)) j + ∑ i : Fin 7, (dTheta j i : ℝ) * z i := by
    funext z
    exact thetaOf_angleVec_affine j z
  rw [h, dthetaCLM]
  exact hlin.const_add (thetaOf (angleVec (pad12 0)) j)

/-- `dthetaCLM j` 在 `Pi.single i 1` 上的取值 = `dTheta j i`。 -/
theorem dthetaCLM_apply_single (j : Fin 9) (i : Fin 7) :
    dthetaCLM j (Pi.single i 1) = (dTheta j i : ℝ) := by
  rw [dthetaCLM, sum_apply]
  have hterm : ∀ j' : Fin 7, (((dTheta j j' : ℝ)) • coord j') (Pi.single i 1)
      = ((dTheta j j' : ℝ)) * (Pi.single i 1 : Fin 7 → ℝ) j' := by
    intro j'
    rw [smul_apply, smul_eq_mul]
    rfl
  rw [Finset.sum_congr rfl fun j' _ => hterm j']
  exact sum_mul_single (fun j' : Fin 7 => ((dTheta j j' : ℝ))) i

/-- `ρ_k(z)` 的导数 CLM（= `hasFDerivAt_rhoK` 里的那个）。 -/
def drhoCLM (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  -(Real.sin (angleVec (pad12 u0) k)) • daCLM k
    - (1 / (2 * Real.sqrt (Wk k))) • ((2 * u0 6) • coord 6
        - (2 * Real.sin (angleVec (pad12 u0) k))
          • ((Real.cos (angleVec (pad12 u0) k)) • daCLM k))

/-- `ρ_k ∘ pad12` 的导数（CLM 形式，与 `hasFDerivAt_rhoK` 同一件事）。 -/
theorem hasFDerivAt_rhoK' (k : Fin 9) (hW : Wk k ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) (drhoCLM k) u0 :=
  hasFDerivAt_rhoK k hW

/-- **`ringCenter` 坐标 0**（`ρ_k·cos θ_k`）的导数（`HasFDerivAt` 形式，条件版）。 -/
theorem hasFDerivAt_ringCenter0 (k : Fin 9) (hW : Wk k ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.cos (thetaOf (angleVec (pad12 z)) k))
      (rhoK (pad12 u0) k • (-(Real.sin (thetaOf (angleVec (pad12 u0)) k)) • dthetaCLM k)
        + Real.cos (thetaOf (angleVec (pad12 u0)) k) • drhoCLM k) u0 := by
  have h := (hasFDerivAt_rhoK' k hW).mul ((hasFDerivAt_thetaOf k).cos)
  exact h

/-- **`ringCenter` 坐标 0** 沿 `Pi.single i 1` 的导数（标量读数，条件版）。 -/
theorem fderiv_ringCenter0 (k : Fin 9) (i : Fin 7) (hW : Wk k ≠ 0) :
    fderiv ℝ (fun z : Fin 7 → ℝ =>
        rhoK (pad12 z) k * Real.cos (thetaOf (angleVec (pad12 z)) k)) u0 (Pi.single i 1)
      = rhoK (pad12 u0) k
          * (-(Real.sin (thetaOf (angleVec (pad12 u0)) k)) * (dTheta k i : ℝ))
        + Real.cos (thetaOf (angleVec (pad12 u0)) k)
          * (-(Real.sin (angleVec (pad12 u0) k)) * (dAngle k i : ℝ)
            - (1 / (2 * Real.sqrt (Wk k))) * ((2 * u0 6) * (if i = 6 then 1 else 0)
              - (2 * Real.sin (angleVec (pad12 u0) k))
                * ((Real.cos (angleVec (pad12 u0) k)) * (dAngle k i : ℝ)))) := by
  rw [(hasFDerivAt_ringCenter0 k hW).fderiv, drhoCLM]
  simp only [add_apply, sub_apply, smul_apply]
  rw [daCLM_apply_single k i, dthetaCLM_apply_single k i, coord_six_apply_single i]
  simp only [smul_eq_mul]

/-- **`ringCenter` 坐标 1**（`ρ_k·sin θ_k`）的导数（`HasFDerivAt` 形式，条件版）。 -/
theorem hasFDerivAt_ringCenter1 (k : Fin 9) (hW : Wk k ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.sin (thetaOf (angleVec (pad12 z)) k))
      (rhoK (pad12 u0) k • ((Real.cos (thetaOf (angleVec (pad12 u0)) k)) • dthetaCLM k)
        + Real.sin (thetaOf (angleVec (pad12 u0)) k) • drhoCLM k) u0 := by
  have h := (hasFDerivAt_rhoK' k hW).mul ((hasFDerivAt_thetaOf k).sin)
  exact h

/-- **`ringCenter` 坐标 1** 沿 `Pi.single i 1` 的导数（标量读数，条件版）。 -/
theorem fderiv_ringCenter1 (k : Fin 9) (i : Fin 7) (hW : Wk k ≠ 0) :
    fderiv ℝ (fun z : Fin 7 → ℝ =>
        rhoK (pad12 z) k * Real.sin (thetaOf (angleVec (pad12 z)) k)) u0 (Pi.single i 1)
      = rhoK (pad12 u0) k
          * ((Real.cos (thetaOf (angleVec (pad12 u0)) k)) * (dTheta k i : ℝ))
        + Real.sin (thetaOf (angleVec (pad12 u0)) k)
          * (-(Real.sin (angleVec (pad12 u0) k)) * (dAngle k i : ℝ)
            - (1 / (2 * Real.sqrt (Wk k))) * ((2 * u0 6) * (if i = 6 then 1 else 0)
              - (2 * Real.sin (angleVec (pad12 u0) k))
                * ((Real.cos (angleVec (pad12 u0) k)) * (dAngle k i : ℝ)))) := by
  rw [(hasFDerivAt_ringCenter1 k hW).fderiv, drhoCLM]
  simp only [add_apply, sub_apply, smul_apply]
  rw [daCLM_apply_single k i, dthetaCLM_apply_single k i, coord_six_apply_single i]
  simp only [smul_eq_mul]

/-- **`arcEnd` 坐标 0**（`cos(θ_k + a_k)`）沿 `Pi.single i 1` 的导数（无条件）。 -/
theorem fderiv_arcEnd0 (k : Fin 9) (i : Fin 7) :
    fderiv ℝ (fun z : Fin 7 → ℝ =>
        Real.cos (thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k)) u0 (Pi.single i 1)
      = -(Real.sin (thetaOf (angleVec (pad12 u0)) k + angleVec (pad12 u0) k))
          * ((dTheta k i : ℝ) + (dAngle k i : ℝ)) := by
  have hadd : HasFDerivAt (fun z : Fin 7 → ℝ => thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k)
      (dthetaCLM k + daCLM k) u0 := (hasFDerivAt_thetaOf k).add (hasFDerivAt_angleVec k)
  rw [(hadd.cos).fderiv]
  simp only [smul_apply]
  rw [add_apply, dthetaCLM_apply_single k i, daCLM_apply_single k i]
  simp only [smul_eq_mul]

/-- **`arcEnd` 坐标 1**（`sin(θ_k + a_k)`）沿 `Pi.single i 1` 的导数（无条件）。 -/
theorem fderiv_arcEnd1 (k : Fin 9) (i : Fin 7) :
    fderiv ℝ (fun z : Fin 7 → ℝ =>
        Real.sin (thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k)) u0 (Pi.single i 1)
      = (Real.cos (thetaOf (angleVec (pad12 u0)) k + angleVec (pad12 u0) k))
          * ((dTheta k i : ℝ) + (dAngle k i : ℝ)) := by
  have hadd : HasFDerivAt (fun z : Fin 7 → ℝ => thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k)
      (dthetaCLM k + daCLM k) u0 := (hasFDerivAt_thetaOf k).add (hasFDerivAt_angleVec k)
  rw [(hadd.sin).fderiv]
  simp only [smul_apply]
  rw [add_apply, dthetaCLM_apply_single k i, daCLM_apply_single k i]
  simp only [smul_eq_mul]

theorem fderiv_rhoK (k : Fin 9) (i : Fin 7) (hW : Wk k ≠ 0) :
    fderiv ℝ (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) u0 (Pi.single i 1)
      = -(Real.sin (angleVec (pad12 u0) k)) * (dAngle k i : ℝ)
        - (1 / (2 * Real.sqrt (Wk k))) * ((2 * u0 6) * (if i = 6 then 1 else 0)
            - (2 * Real.sin (angleVec (pad12 u0) k))
              * ((Real.cos (angleVec (pad12 u0) k)) * (dAngle k i : ℝ))) := by
  rw [(hasFDerivAt_rhoK k hW).fderiv]
  simp only [sub_apply, smul_apply]
  rw [daCLM_apply_single k i, coord_six_apply_single i]
  simp only [smul_eq_mul]

/-- `ringCenter` 坐标 0 的导数 CLM（= `hasFDerivAt_ringCenter0` 里的那个）。 -/
def dring0CLM (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  rhoK (pad12 u0) k • (-(Real.sin (thetaOf (angleVec (pad12 u0)) k)) • dthetaCLM k)
    + Real.cos (thetaOf (angleVec (pad12 u0)) k) • drhoCLM k

/-- `ringCenter` 坐标 1 的导数 CLM。 -/
def dring1CLM (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  rhoK (pad12 u0) k • ((Real.cos (thetaOf (angleVec (pad12 u0)) k)) • dthetaCLM k)
    + Real.sin (thetaOf (angleVec (pad12 u0)) k) • drhoCLM k

/-- `arcEnd` 坐标 0 的导数 CLM。 -/
def darc0CLM (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  -(Real.sin (thetaOf (angleVec (pad12 u0)) k + angleVec (pad12 u0) k))
    • (dthetaCLM k + daCLM k)

/-- `arcEnd` 坐标 1 的导数 CLM。 -/
def darc1CLM (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  (Real.cos (thetaOf (angleVec (pad12 u0)) k + angleVec (pad12 u0) k))
    • (dthetaCLM k + daCLM k)

theorem hasFDerivAt_ringCenter0' (k : Fin 9) (hW : Wk k ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0) (dring0CLM k) u0 :=
  hasFDerivAt_ringCenter0 k hW

theorem hasFDerivAt_ringCenter1' (k : Fin 9) (hW : Wk k ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1) (dring1CLM k) u0 :=
  hasFDerivAt_ringCenter1 k hW

theorem hasFDerivAt_arcEnd0' (k : Fin 9) :
    HasFDerivAt (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 0) (darc0CLM k) u0 := by
  have hadd : HasFDerivAt (fun z : Fin 7 → ℝ => thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k)
      (dthetaCLM k + daCLM k) u0 := (hasFDerivAt_thetaOf k).add (hasFDerivAt_angleVec k)
  exact hadd.cos

theorem hasFDerivAt_arcEnd1' (k : Fin 9) :
    HasFDerivAt (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 1) (darc1CLM k) u0 := by
  have hadd : HasFDerivAt (fun z : Fin 7 → ℝ => thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k)
      (dthetaCLM k + daCLM k) u0 := (hasFDerivAt_thetaOf k).add (hasFDerivAt_angleVec k)
  exact hadd.sin

/-- **`Uvec` 坐标 0**（`C_k + C_{k+1} − B_k`）的导数（`HasFDerivAt` 形式；条件：两个 `Wk` 非零）。 -/
theorem hasFDerivAt_Uvec0 (k : Fin 9) (hW0 : Wk k ≠ 0) (hW1 : Wk (k + 1) ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => (Uvec (pad12 z) k).ofLp 0)
      (dring0CLM k + dring0CLM (k + 1) - darc0CLM k) u0 :=
  ((hasFDerivAt_ringCenter0' k hW0).add (hasFDerivAt_ringCenter0' (k + 1) hW1)).sub
    (hasFDerivAt_arcEnd0' k)

/-- **`Uvec` 坐标 1** 的导数（`HasFDerivAt` 形式；条件：两个 `Wk` 非零）。 -/
theorem hasFDerivAt_Uvec1 (k : Fin 9) (hW0 : Wk k ≠ 0) (hW1 : Wk (k + 1) ≠ 0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => (Uvec (pad12 z) k).ofLp 1)
      (dring1CLM k + dring1CLM (k + 1) - darc1CLM k) u0 :=
  ((hasFDerivAt_ringCenter1' k hW0).add (hasFDerivAt_ringCenter1' (k + 1) hW1)).sub
    (hasFDerivAt_arcEnd1' k)


/-- **`Uvec` 坐标 0 沿 `Pi.single i 1` 的导数**（"和"步；**`_ext` 后缀 = 与 `ResidualDerivNode2` 里
同名的 CLM 取值引理区分**，后者被 `ResidualDerivD` 以两参数形式引用，语义不同、不得改）。路线：`SourceIdentity.Uvec_coord0`
是 `rfl` ⇒ 在 `fderiv` 层用 `fderiv_sub`/`fderiv_add`，可微性由本文件已有的 CLM `HasFDerivAt`
引理 `.differentiableAt` 提供（**不需要**把 CLM 在 `Pi.single i 1` 上求值 —— 那条路会撞
"展开 vs 命名取值引理"的顺序冲突）。 -/
theorem fderiv_Uvec0_ext (k : Fin 9) (i : Fin 7) (hW0 : Wk k ≠ 0) (hW1 : Wk (k + 1) ≠ 0) :
    fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) k).ofLp 0) u0 (Pi.single i 1)
      = fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0) u0 (Pi.single i 1)
        + fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (k + 1)).ofLp 0) u0 (Pi.single i 1)
        - fderiv ℝ (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 0) u0 (Pi.single i 1) := by
  have hfun : (fun z : Fin 7 → ℝ => (Uvec (pad12 z) k).ofLp 0)
      = (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (k + 1)).ofLp 0)
        - (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 0) := by
    funext z
    rw [Uvec_coord0]
    rfl
  have hd1 : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0) u0 :=
    (hasFDerivAt_ringCenter0' k hW0).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (k + 1)).ofLp 0) u0 :=
    (hasFDerivAt_ringCenter0' (k + 1) hW1).differentiableAt
  have hd3 : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 0) u0 :=
    (hasFDerivAt_arcEnd0' k).differentiableAt
  rw [hfun, fderiv_sub (hd1.add hd2) hd3, fderiv_add hd1 hd2]
  simp only [add_apply, sub_apply]

/-- **`Uvec` 坐标 1 沿 `Pi.single i 1` 的导数**（同款）。 -/
theorem fderiv_Uvec1_ext (k : Fin 9) (i : Fin 7) (hW0 : Wk k ≠ 0) (hW1 : Wk (k + 1) ≠ 0) :
    fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) k).ofLp 1) u0 (Pi.single i 1)
      = fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1) u0 (Pi.single i 1)
        + fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (k + 1)).ofLp 1) u0 (Pi.single i 1)
        - fderiv ℝ (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 1) u0 (Pi.single i 1) := by
  have hfun : (fun z : Fin 7 → ℝ => (Uvec (pad12 z) k).ofLp 1)
      = (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (k + 1)).ofLp 1)
        - (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 1) := by
    funext z
    rw [Uvec_coord1]
    rfl
  have hd1 : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1) u0 :=
    (hasFDerivAt_ringCenter1' k hW0).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (k + 1)).ofLp 1) u0 :=
    (hasFDerivAt_ringCenter1' (k + 1) hW1).differentiableAt
  have hd3 : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 1) u0 :=
    (hasFDerivAt_arcEnd1' k).differentiableAt
  rw [hfun, fderiv_sub (hd1.add hd2) hd3, fderiv_add hd1 hd2]
  simp only [add_apply, sub_apply]

end N11Formalization
