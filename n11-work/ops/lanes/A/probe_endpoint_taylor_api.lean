import Mathlib

example (a : ℚ) (n : ℕ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a ^ (n + 2) / ((Nat.factorial (n + 2) : ℕ) : ℚ) ≤
      a ^ n / ((Nat.factorial n : ℕ) : ℚ) := by
  have hpow : a ^ (n + 2) ≤ a ^ n :=
    pow_le_pow_of_le_one ha0 ha1 (by omega)
  calc
    a ^ (n + 2) / ((Nat.factorial (n + 2) : ℕ) : ℚ) ≤
        a ^ n / ((Nat.factorial (n + 2) : ℕ) : ℚ) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ a ^ n / ((Nat.factorial n : ℕ) : ℚ) := by
      exact div_le_div_of_nonneg_left (pow_nonneg ha0 n) (by positivity)
        (by exact_mod_cast Nat.factorial_le (by omega))
