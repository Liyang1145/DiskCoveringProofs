import Mathlib

set_option autoImplicit false
noncomputable section
namespace LaneAEndpointProbe

def piHi : ℚ := 314159265358979323847 / 10 ^ 20

def sinTQ (m : ℕ) (q : ℚ) : ℚ :=
  ∑ k ∈ Finset.range m, (-1 : ℚ) ^ k * q ^ (2 * k + 1) / ((Nat.factorial (2 * k + 1) : ℕ) : ℚ)

def sinLoNLag (q : ℚ) : ℚ := sinTQ 14 q - |q| ^ 29 / ((Nat.factorial 29 : ℕ) : ℚ)

def sinHiNLag (q : ℚ) : ℚ := sinTQ 14 q + |q| ^ 29 / ((Nat.factorial 29 : ℕ) : ℚ)

def capQ (q : ℚ) : ℚ := (19/50)*max (1/2) (min 1 (sinHiNLag (q/2)))

def nodeQ (U : ℚ) (N : ℕ) (k : Fin (N+1)) : ℚ := U*k.val/N

def binHi (j : Fin 8) : Fin 2049 :=
  ⟨if j.val = 7 then 2048 else 256 * j.val + 255, by split <;> omega⟩

def nodeBinAt (j : Fin 8) : ℚ :=
  ![239/1250, 239/1250, 133/625, 2721/10000,
    643/2000, 897/2500, 191/500, 1949/5000] j

def EndpointCheck (j : Fin 8) : Prop :=
  capQ (nodeQ piHi 2048 (binHi j)) ≤ sinLoNLag (nodeBinAt j)

theorem endpointCheck_0 : EndpointCheck 0 := by
  norm_num [EndpointCheck, capQ, nodeQ, binHi, nodeBinAt,
    sinHiNLag, sinLoNLag, sinTQ, Finset.sum_range_succ]

theorem endpointCheap_0 : (19/50 : ℚ) ≤ sinLoNLag (nodeBinAt 0) := by
  norm_num [sinLoNLag, sinTQ, Finset.sum_range_succ]

end LaneAEndpointProbe
#print axioms LaneAEndpointProbe.endpointCheap_0
