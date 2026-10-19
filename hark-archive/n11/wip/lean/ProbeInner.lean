import Mathlib
import N11Formalization.Definitions
namespace N11Formalization
open scoped RealInnerProductSpace
example (x y : Point) : (inner ℝ x y : ℝ) = inner ℝ y x := by simp [real_inner_comm]
example (x y : Point) : (inner ℝ x y : ℝ) = inner ℝ y x := by rw [real_inner_comm]
example (x y z : Point) : (inner ℝ (x+y) z : ℝ) = inner ℝ z (x+y) := by simp [real_inner_comm]
#check @real_inner_smul_left
#check @norm_sub_sq_real
end N11Formalization
