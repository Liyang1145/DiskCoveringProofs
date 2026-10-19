import Mathlib

/-! # ResumeRootRefine — abstract a-posteriori fixed-point bound (C922 refine, step 1)
Standalone: no project imports. Consumer (later): g x = x - Y·F(x) on certificate ball,
Lipschitz constant K from fixed Jt row sums; center c arbitrary rational point in ball. -/

namespace N11Formalization.ResumeRootRefine

/-- A posteriori: fixed point x* of a K-Lipschitz map on s, any c ∈ s ⇒
`‖x* - c‖ ≤ ‖g c - c‖ / (1 - K)`. -/
theorem fixed_point_near_center {E : Type*} [NormedAddCommGroup E]
    {g : E → E} {s : Set E} {K : NNReal} (hK : (K : ℝ) < 1)
    (hg : LipschitzOnWith K g s) {x c : E} (hx : x ∈ s) (hc : c ∈ s)
    (hfix : g x = x) : ‖x - c‖ ≤ ‖g c - c‖ / (1 - K) := by
  have h1 : ‖x - c‖ ≤ K * ‖x - c‖ + ‖g c - c‖ := by
    have hl := hg.norm_sub_le hx hc
    calc ‖x - c‖ = ‖(g x - g c) + (g c - c)‖ := by rw [hfix]; congr 1; abel
      _ ≤ ‖g x - g c‖ + ‖g c - c‖ := norm_add_le _ _
      _ ≤ K * ‖x - c‖ + ‖g c - c‖ := by linarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Coordinate form on `Fin n → ℝ` (sup norm): radius coordinate pinned. -/
theorem coord_le_of_fixed_point {n : ℕ} {g : (Fin n → ℝ) → (Fin n → ℝ)}
    {s : Set (Fin n → ℝ)} {K : NNReal} (hK : (K : ℝ) < 1)
    (hg : LipschitzOnWith K g s) {x c : Fin n → ℝ} (hx : x ∈ s) (hc : c ∈ s)
    (hfix : g x = x) (i : Fin n) {η : ℝ} (hη : ‖g c - c‖ ≤ η) :
    x i ≤ c i + η / (1 - K) := by
  have h := fixed_point_near_center hK hg hx hc hfix
  have hi : |x i - c i| ≤ ‖x - c‖ := by
    simpa using norm_le_pi_norm (x - c) i
  have : ‖g c - c‖ / (1 - K) ≤ η / (1 - K) :=
    div_le_div_of_nonneg_right hη (by linarith)
  linarith [le_abs_self (x i - c i)]

#print axioms fixed_point_near_center
#print axioms coord_le_of_fixed_point

end N11Formalization.ResumeRootRefine
