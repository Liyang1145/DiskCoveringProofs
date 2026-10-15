/-
# `Uvec` 标量步：5 条 CLM 取值引理（Lead，R51）

**背景**：`ResidualDerivNode.lean` 的 `Uvec` 节点已完成 **CLM 步**（`hasFDerivAt_Uvec0/1`），
但**标量求值步**（把 CLM 在 `Pi.single i 1` 上的取值化成标量表达式）停摆多轮。
前任定位的根因：`rw [dring0CLM]` 这类"展开 CLM 定义"会先把命名取值引理变成不可匹配
（展开成 `Finset.sum`），而不展开则引理无从下手；重复 `rw [def, def]` 报
`Failed to rewrite using equation theorems`。

**做法**：照 `daCLM_apply_single`（该文件内已验证编译过）的**一次性**写法 ——
`rw [def]` 后用 `simp only` 把 CLM 的线性/系数规则与**已存在的**取值引理一次用完。

**命名**：本文件用 `*_single` 后缀（与 `ResidualDerivNode.lean` 中 `*_apply_single`
不同的名字），以便与队友的工作**并存、不冲突**；队友可自行改用其一。

**实现注记（给后来者）**：CLM 的取值引理名**不带 `ContinuousLinearMap.` 前缀**
（`sub_apply`/`add_apply`/`smul_apply`；带前缀的是**已弃用**别名，会报 deprecation warning）；
且本文件中 `neg_apply` 是**无用**的 simp 参数（`-a` 在 CLM 上已被归一为 `0 - a` 形态），
去掉可消 warning。

**口径**：RHS 里保留 `drhoCLM k (Pi.single i 1)` 记号，使 `dring0/1CLM` 的证明不必再展开 ρ；
后续节点要标量式时再 `rw [drhoCLM_single]` 即可。
-/
import N11Formalization.ResidualDerivNode

namespace N11Formalization

/-- `drhoCLM k` 在 `Pi.single i 1` 上的标量取值。 -/
theorem drhoCLM_single (k : Fin 9) (i : Fin 7) :
    drhoCLM k (Pi.single i 1)
      = -(Real.sin (angleVec (pad12 u0) k)) * (dAngle k i : ℝ)
        - (1 / (2 * Real.sqrt (Wk k)))
          * ((2 * u0 6) * (if i = 6 then 1 else 0 : ℝ)
             - (2 * Real.sin (angleVec (pad12 u0) k))
               * ((Real.cos (angleVec (pad12 u0) k)) * (dAngle k i : ℝ))) := by
  rw [drhoCLM]
  simp only [sub_apply, smul_apply, smul_eq_mul, daCLM_apply_single, coord_six_apply_single]

/-- `dring0CLM k` 在 `Pi.single i 1` 上的标量取值。 -/
theorem dring0CLM_single (k : Fin 9) (i : Fin 7) :
    dring0CLM k (Pi.single i 1)
      = rhoK (pad12 u0) k
          * (-(Real.sin (thetaOf (angleVec (pad12 u0)) k)) * (dTheta k i : ℝ))
        + Real.cos (thetaOf (angleVec (pad12 u0)) k) * (drhoCLM k (Pi.single i 1)) := by
  rw [dring0CLM]
  simp only [add_apply, smul_apply, smul_eq_mul, dthetaCLM_apply_single]

/-- `dring1CLM k` 在 `Pi.single i 1` 上的标量取值。 -/
theorem dring1CLM_single (k : Fin 9) (i : Fin 7) :
    dring1CLM k (Pi.single i 1)
      = rhoK (pad12 u0) k
          * (Real.cos (thetaOf (angleVec (pad12 u0)) k) * (dTheta k i : ℝ))
        + Real.sin (thetaOf (angleVec (pad12 u0)) k) * (drhoCLM k (Pi.single i 1)) := by
  rw [dring1CLM]
  simp only [add_apply, smul_apply, smul_eq_mul, dthetaCLM_apply_single]

/-- `darc0CLM k` 在 `Pi.single i 1` 上的标量取值。 -/
theorem darc0CLM_single (k : Fin 9) (i : Fin 7) :
    darc0CLM k (Pi.single i 1)
      = -(Real.sin (thetaOf (angleVec (pad12 u0)) k + angleVec (pad12 u0) k))
          * ((dTheta k i : ℝ) + (dAngle k i : ℝ)) := by
  rw [darc0CLM]
  simp only [smul_apply, add_apply, smul_eq_mul, dthetaCLM_apply_single, daCLM_apply_single]

/-- `darc1CLM k` 在 `Pi.single i 1` 上的标量取值。 -/
theorem darc1CLM_single (k : Fin 9) (i : Fin 7) :
    darc1CLM k (Pi.single i 1)
      = (Real.cos (thetaOf (angleVec (pad12 u0)) k + angleVec (pad12 u0) k))
          * ((dTheta k i : ℝ) + (dAngle k i : ℝ)) := by
  rw [darc1CLM]
  simp only [smul_apply, add_apply, smul_eq_mul, dthetaCLM_apply_single, daCLM_apply_single]

/-- **`Uvec` 坐标 0 的标量导数读数**：把 `hasFDerivAt_Uvec0/1` 的 CLM 在 `Pi.single i 1`
上求值（RHS 保留 `drhoCLM … (Pi.single i 1)` 记号，需要全标量式时再 `rw [drhoCLM_single]`）。 -/
theorem fderiv_Uvec0 (k : Fin 9) (i : Fin 7) :
    (dring0CLM k + dring0CLM (k + 1) - darc0CLM k) (Pi.single i 1)
      = rhoK (pad12 u0) k
            * (-(Real.sin (thetaOf (angleVec (pad12 u0)) k)) * (dTheta k i : ℝ))
          + Real.cos (thetaOf (angleVec (pad12 u0)) k) * (drhoCLM k (Pi.single i 1))
        + (rhoK (pad12 u0) (k + 1)
              * (-(Real.sin (thetaOf (angleVec (pad12 u0)) (k + 1))) * (dTheta (k + 1) i : ℝ))
            + Real.cos (thetaOf (angleVec (pad12 u0)) (k + 1)) * (drhoCLM (k + 1) (Pi.single i 1)))
        - (-(Real.sin (thetaOf (angleVec (pad12 u0)) k + angleVec (pad12 u0) k))
            * ((dTheta k i : ℝ) + (dAngle k i : ℝ))) := by
  simp only [add_apply, sub_apply, dring0CLM_single, darc0CLM_single]

/-- **`Uvec` 坐标 1 的标量导数读数**。 -/
theorem fderiv_Uvec1 (k : Fin 9) (i : Fin 7) :
    (dring1CLM k + dring1CLM (k + 1) - darc1CLM k) (Pi.single i 1)
      = rhoK (pad12 u0) k
            * (Real.cos (thetaOf (angleVec (pad12 u0)) k) * (dTheta k i : ℝ))
          + Real.sin (thetaOf (angleVec (pad12 u0)) k) * (drhoCLM k (Pi.single i 1))
        + (rhoK (pad12 u0) (k + 1)
              * (Real.cos (thetaOf (angleVec (pad12 u0)) (k + 1)) * (dTheta (k + 1) i : ℝ))
            + Real.sin (thetaOf (angleVec (pad12 u0)) (k + 1)) * (drhoCLM (k + 1) (Pi.single i 1)))
        - ((Real.cos (thetaOf (angleVec (pad12 u0)) k + angleVec (pad12 u0) k))
            * ((dTheta k i : ℝ) + (dAngle k i : ℝ))) := by
  simp only [add_apply, sub_apply, dring1CLM_single, darc1CLM_single]

end N11Formalization
