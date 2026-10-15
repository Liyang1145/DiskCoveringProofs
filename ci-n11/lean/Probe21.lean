import Mathlib

open Metric

abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

#check @Real.contDiff_sin
#check @Real.contDiff_cos
#check @ContDiff.contDiffAt
#check @ContDiffAt.sqrt
#check @Real.contDiffAt_sqrt
#check @ContDiffAt.norm
#check @HasFDerivAt.norm
#check @ContDiffAt.dist
#check @ContDiffAt.sub
#check @ContDiffAt.mul
#check @ContDiffAt.comp
#check @ContinuousLinearEquiv.contDiff
#check @WithLp.equiv
#check @Homeomorph.contDiff
#check @ContDiffAt.of_le
#check @contDiffAt_id
#check @contDiffAt_const
#check @ContDiffAt.add
#check @HasFDerivAt.dist
#check @HasFDerivAt.norm
#check @HasStrictFDerivAt.hasFDerivAt
#check @HasFDerivAt.comp_hasFDerivWithinAt
#check @continuousLinearMap_hasFDerivAt
#check @ContDiffAt.div
