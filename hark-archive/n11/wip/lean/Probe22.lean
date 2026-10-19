import Mathlib

open Metric

abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

#check @ContinuousLinearMap.proj
#check @ContinuousLinearMap.apply
#check @ContinuousLinearMap.contDiff
#check @contDiffAt_pi
#check @ContDiffAt.pi
#check @contDiffAt_const
#check @contDiffAt_id
#check @ContDiffAt.smul
#check @ContDiffAt.const_smul
#check @contDiffAt_pi_iff
#check @ContinuousLinearEquiv.symm
#check @ContinuousLinearEquiv.contDiffAt
#check @ContDiffAt.real_sin
#check @Real.contDiff_sin
#check @ContDiffAt.congr
#check @ContDiffAt.congr_of_eventuallyEq
