import N11Formalization.ResidualDistNode
-- 探针：`HasFDerivAt`(ℝ 值) ∘ `HasDerivAt`(标量) 的链式，以及 sqrt/norm_sq 的组合
#check @HasFDerivAt.comp_hasDerivAt
#check @HasFDerivAt.comp_hasDerivAt'
#check @HasDerivAt.comp_hasFDerivAt
#check @HasFDerivAt.hasDerivAt
#check @HasFDerivAt.const_mul
#check @HasFDerivAt.mul_const
#check @HasFDerivAt.sqrt
#check @ContinuousLinearMap.smulRight
#check @HasStrictFDerivAt.comp_hasDerivAt
#check @HasFDerivAt.comp_hasDerivWithinAt
#check @HasDerivAt.smul_const
#check @HasFDerivAt.smul_const
#check @norm_nonneg
#check @Real.sqrt_sq_eq_abs
#check @abs_of_nonneg
-- 目标形状的自测：先只到「平方范数 + 坐标」这一层
example (A B : EuclideanSpace ℝ (Fin 2)) : dist A B = Real.sqrt (‖A - B‖ ^ 2) := by
  rw [dist_eq_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
