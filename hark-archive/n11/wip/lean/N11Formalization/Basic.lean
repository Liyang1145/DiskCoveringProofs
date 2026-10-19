import Mathlib

theorem smoke_two_add_two : (2:ℕ) + 2 = 4 := rfl
theorem smoke_sqrt_lt (x : ℝ) (h : 0 ≤ x) : Real.sqrt x ^ 2 = x := Real.sq_sqrt h
