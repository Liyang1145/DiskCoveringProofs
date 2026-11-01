import Mathlib

noncomputable section
namespace TmpN11Step

def sinTQ (m : ℕ) (q : ℚ) : ℚ :=
  ∑ k ∈ Finset.range m, (-1 : ℚ) ^ k * q ^ (2 * k + 1) / ((Nat.factorial (2 * k + 1) : ℕ) : ℚ)

def sinHiNLag (q : ℚ) : ℚ := sinTQ 14 q + |q| ^ 29 / ((Nat.factorial 29 : ℕ) : ℚ)

def q1 : ℚ := 401338461496096086213602692213956493526557/256000000000000000000000000000000000000000
def q2 : ℚ := 803462321155589620736821045273732862774301/512000000000000000000000000000000000000000
def mu1 : ℚ := 2427339000000000000000000000000000000507/50000000000000000000000000000000000000000
def lam : ℚ := 3623132999999999999999999999999999998363/20000000000000000000000000000000000000000
def node : ℚ := 643/2000

def val (q : ℚ) : ℚ :=
  (19/50)^2 * sinHiNLag q / 2 + (2 * node - sinHiNLag (2 * node)) / 2
    + lam * (2 * node) - mu1 * q

example : val q2 < val q1 := by
  norm_num [val, sinHiNLag, sinTQ, Finset.sum_range_succ]

end TmpN11Step
