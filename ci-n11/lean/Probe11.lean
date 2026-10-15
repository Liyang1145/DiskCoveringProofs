import Mathlib

example (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) : (⟨K, hK0⟩ : NNReal) < 1 := by
  exact_mod_cast hK1

example (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) : (⟨K, hK0⟩ : NNReal) < 1 := by
  rw [← NNReal.coe_lt_coe]
  simpa using hK1

#check @NNReal.coe_lt_coe
#check @NNReal.mk_lt_mk
#check @Subtype.mk_lt_mk
#check @NNReal.coe_lt_one
#check @NNReal.coe_lt_coe_iff
