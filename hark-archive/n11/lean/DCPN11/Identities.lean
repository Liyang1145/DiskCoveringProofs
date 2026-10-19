/-
DCPN11/Identities.lean  —  the elementary identities of docs/N11_CHECK_SCOPE.md §
"Explicit candidate and equality identities" (items 1-4) for the C891 model.

STATUS: NOT YET COMPILED (see STATUS.md). All proofs below are complete drafts
(no `sorry`) but have not been checked by Lean.
-/
import DCPN11.Candidate

open Real ComplexConjugate

noncomputable section

namespace DCP.N11

/-! ### Generic plane identities -/

theorem pt_sub (x y u v : ℝ) : pt x y - pt u v = pt (x - u) (y - v) := by
  apply Complex.ext <;> simp [pt]

theorem sq_norm_pt (x y : ℝ) : ‖pt x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [pt]; ring

theorem norm_pt (x y : ℝ) : ‖pt x y‖ = √(x ^ 2 + y ^ 2) := by
  rw [← sq_norm_pt, Real.sqrt_sq (norm_nonneg _)]

theorem conj_pt (x y : ℝ) : conj (pt x y) = pt x (-y) := by
  apply Complex.ext <;> simp [pt]

/-! ### Identity 1: `ρ² - 2ρ cos a + 1 = R²` -/

theorem rho_identity (a R : ℝ) (h : sin a ^ 2 ≤ R ^ 2) :
    (cos a - √(R ^ 2 - sin a ^ 2)) ^ 2 - 2 * (cos a - √(R ^ 2 - sin a ^ 2)) * cos a + 1
      = R ^ 2 := by
  have hs : √(R ^ 2 - sin a ^ 2) ^ 2 = R ^ 2 - sin a ^ 2 := Real.sq_sqrt (by linarith)
  have hp := sin_sq_add_cos_sq a
  linear_combination hs - hp

/-- `|ρ e^{iθ} - e^{i(θ+a)}|² = ρ² - 2ρ cos a + 1`. -/
theorem sq_dist_site_switch (ρ θ a : ℝ) :
    ‖pt (ρ * cos θ) (ρ * sin θ) - pt (cos (θ + a)) (sin (θ + a))‖ ^ 2
      = ρ ^ 2 - 2 * ρ * cos a + 1 := by
  rw [pt_sub, sq_norm_pt, cos_add, sin_add]
  have hθ := sin_sq_add_cos_sq θ
  have ha := sin_sq_add_cos_sq a
  linear_combination (ρ ^ 2 - 2 * ρ * cos a + (sin a ^ 2 + cos a ^ 2)) * hθ + ha

/-- `|ρ e^{iθ} - e^{i(θ-a)}|² = ρ² - 2ρ cos a + 1`. -/
theorem sq_dist_site_switch' (ρ θ a : ℝ) :
    ‖pt (ρ * cos θ) (ρ * sin θ) - pt (cos (θ - a)) (sin (θ - a))‖ ^ 2
      = ρ ^ 2 - 2 * ρ * cos a + 1 := by
  have := sq_dist_site_switch ρ θ (-a)
  rwa [cos_neg, ← sub_eq_add_neg] at this

/-! ### Arc tiling: consecutive arcs share their switch -/

/-- `Σ a_k = π`. -/
theorem halfAngle_sum (z : Z) : ∑ k : Fin 9, halfAngle z k = π := by
  simp [Fin.sum_univ_succ, halfAngle]; ring

/-- `θ(k+1) - a(k+1) = θk + ak` for `k = 0..7`. -/
theorem theta_switch (z : Z) (k : Fin 9) (hk : k ≠ 8) :
    theta z (k + 1) - halfAngle z (k + 1) = theta z k + halfAngle z k := by
  fin_cases k <;> simp_all [theta, halfAngle] <;> ring

/-- Wrap-around: `θ0 - a0 + 2π = θ8 + a8`. -/
theorem theta_switch_wrap (z : Z) :
    theta z 0 - halfAngle z 0 + 2 * π = theta z 8 + halfAngle z 8 := by
  simp [theta, halfAngle]; ring

/-- Under the branch condition, `|C_k - B_k| = R`. -/
theorem dist_site_switch (z : Z) (k : Fin 9) (hb : sin (halfAngle z k) ^ 2 ≤ Rad z ^ 2)
    (hR : 0 ≤ Rad z) : ‖ringSite z k - switchPt z k‖ = Rad z := by
  have h2 : ‖ringSite z k - switchPt z k‖ ^ 2 = Rad z ^ 2 := by
    rw [ringSite, switchPt, sq_dist_site_switch]; exact rho_identity _ _ hb
  exact (pow_left_injective₀ (norm_nonneg _) hR two_ne_zero) h2

/-- Under the branch condition, `|C_{k+1} - B_k| = R` (including the wrap `k = 8`). -/
theorem dist_next_site_switch (z : Z) (k : Fin 9)
    (hb : sin (halfAngle z (k + 1)) ^ 2 ≤ Rad z ^ 2) (hR : 0 ≤ Rad z) :
    ‖ringSite z (k + 1) - switchPt z k‖ = Rad z := by
  have hB : switchPt z k =
      pt (cos (theta z (k + 1) - halfAngle z (k + 1)))
        (sin (theta z (k + 1) - halfAngle z (k + 1))) := by
    by_cases hk : k = 8
    · subst hk
      have h := theta_switch_wrap z
      have h0 : (8 : Fin 9) + 1 = 0 := rfl
      rw [switchPt, h0, ← h, add_comm (theta z 0 - halfAngle z 0), cos_add_two_pi,
        sin_add_two_pi]
    · rw [switchPt, theta_switch z k hk]
  have h2 : ‖ringSite z (k + 1) - switchPt z k‖ ^ 2 = Rad z ^ 2 := by
    rw [hB, ringSite, sq_dist_site_switch']; exact rho_identity _ _ hb
  exact (pow_left_injective₀ (norm_nonneg _) hR two_ne_zero) h2

/-! ### Identity 2: reflection in the midpoint, `U_k = C_k + C_{k+1} - B_k` -/

theorem pin_sub_site (z : Z) (k : Fin 9) :
    pin z k - ringSite z k = ringSite z (k + 1) - switchPt z k := by
  unfold pin; ring

theorem pin_sub_next_site (z : Z) (k : Fin 9) :
    pin z k - ringSite z (k + 1) = ringSite z k - switchPt z k := by
  unfold pin; ring

/-- `U_k` is at distance exactly `R` from both ring sites `C_k`, `C_{k+1}`. -/
theorem pin_dist_sites (z : Z) (k : Fin 9) (hR : 0 ≤ Rad z)
    (hb : sin (halfAngle z k) ^ 2 ≤ Rad z ^ 2)
    (hb' : sin (halfAngle z (k + 1)) ^ 2 ≤ Rad z ^ 2) :
    ‖pin z k - ringSite z k‖ = Rad z ∧ ‖pin z k - ringSite z (k + 1)‖ = Rad z := by
  rw [pin_sub_site, pin_sub_next_site]
  exact ⟨dist_next_site_switch z k hb' hR, dist_site_switch z k hb hR⟩

/-! ### Identity 3: reflection in the x-axis -/

theorem halfAngle_rev (z : Z) (k : Fin 9) : halfAngle z k.rev = halfAngle z k := by
  fin_cases k <;> rfl

theorem theta_rev (z : Z) (k : Fin 9) : theta z k.rev = - theta z k := by
  fin_cases k <;> simp [theta, halfAngle] <;> ring

theorem rho_rev (z : Z) (k : Fin 9) : rho z k.rev = rho z k := by
  simp [rho, halfAngle_rev]

/-- `conj C_k = C_{8-k}`. -/
theorem conj_ringSite (z : Z) (k : Fin 9) : conj (ringSite z k) = ringSite z k.rev := by
  rw [ringSite, ringSite, conj_pt, rho_rev, theta_rev, cos_neg, sin_neg]; ring_nf

/-- Hubs are real, hence fixed by the reflection. -/
theorem conj_hub0 (z : Z) : conj (hub0 z) = hub0 z := by simp [hub0, conj_pt]
theorem conj_hub1 (z : Z) : conj (hub1 z) = hub1 z := by simp [hub1, conj_pt]

/-- Reflected pin index `(7 - k) mod 9` (machine-checked bookkeeping:
`DCPCore.reflPin_matches_reflSite`). -/
def reflPinIdx (k : Fin 9) : Fin 9 := 7 - k

/-- `conj B_k = B_{7-k}` up to the `2π` wrap (cos/sin values agree). -/
theorem conj_switchPt (z : Z) (k : Fin 9) : conj (switchPt z k) = switchPt z (reflPinIdx k) := by
  -- draft: per index, `θ_{7-k} + a_{7-k} = -(θ_k + a_k)` for k ≤ 7, and for k = 8 the angle
  -- `-(θ8+a8) = θ8 + a8 - 2π` (from `theta_switch_wrap` and `theta_rev`).
  fin_cases k
  all_goals
    simp only [switchPt, conj_pt, reflPinIdx]
    first
    | (congr 1 <;> [rw [← cos_neg]; rw [← sin_neg]] <;> congr 1 <;>
        simp [theta, halfAngle] <;> ring)
    | (have h := theta_switch_wrap z
       congr 1
       · rw [← cos_neg, show -(theta z 8 + halfAngle z 8) = (theta z 8 + halfAngle z 8) - 2 * π by
           simp [theta, halfAngle] at h ⊢; linarith, cos_sub_two_pi]; rfl
       · rw [← sin_neg, show -(theta z 8 + halfAngle z 8) = (theta z 8 + halfAngle z 8) - 2 * π by
           simp [theta, halfAngle] at h ⊢; linarith, sin_sub_two_pi]; rfl)

/-- `conj U_k = U_{7-k}`. -/
theorem conj_pin (z : Z) (k : Fin 9) : conj (pin z k) = pin z (reflPinIdx k) := by
  -- draft: `C_{8-k} + C_{8-(k+1)} - B_{7-k}` with `8-k = (7-k)+1`.
  have h1 : k.rev = reflPinIdx k + 1 := by fin_cases k <;> rfl
  have h2 : (k + 1).rev = reflPinIdx k := by fin_cases k <;> rfl
  simp only [pin, map_sub, map_add, conj_ringSite, conj_switchPt, h1, h2]; ring

/-- Distance to a real point is reflection invariant. -/
theorem norm_conj_sub_real (w h : ℂ) (hh : conj h = h) : ‖conj w - h‖ = ‖w - h‖ := by
  rw [← hh, ← map_sub, Complex.norm_conj, hh]

/-! ### Identity 4: the waist point -/

theorem waist_dist_hub0 (z : Z) (hd : ((z 5 - z 4) / 2) ^ 2 ≤ Rad z ^ 2) (hR : 0 ≤ Rad z) :
    ‖waist z - hub0 z‖ = Rad z := by
  have hs : √(Rad z ^ 2 - ((z 5 - z 4) / 2) ^ 2) ^ 2 = Rad z ^ 2 - ((z 5 - z 4) / 2) ^ 2 :=
    Real.sq_sqrt (by linarith)
  have h2 : ‖waist z - hub0 z‖ ^ 2 = Rad z ^ 2 := by
    rw [waist, hub0, pt_sub, sq_norm_pt]; linear_combination hs
  exact (pow_left_injective₀ (norm_nonneg _) hR two_ne_zero) h2

theorem waist_dist_hub1 (z : Z) (hd : ((z 5 - z 4) / 2) ^ 2 ≤ Rad z ^ 2) (hR : 0 ≤ Rad z) :
    ‖waist z - hub1 z‖ = Rad z := by
  have hs : √(Rad z ^ 2 - ((z 5 - z 4) / 2) ^ 2) ^ 2 = Rad z ^ 2 - ((z 5 - z 4) / 2) ^ 2 :=
    Real.sq_sqrt (by linarith)
  have h2 : ‖waist z - hub1 z‖ ^ 2 = Rad z ^ 2 := by
    rw [waist, hub1, pt_sub, sq_norm_pt]; linear_combination hs
  exact (pow_left_injective₀ (norm_nonneg _) hR two_ne_zero) h2

/-! ### Consequence: the nine active faces (C892 equality part)

At a point with `con z = 0`, the four fan constraints, their reflections and the waist give
seven fan faces (edges 1,2,3,4,5,6,8) and two central faces whose three sites are all at
distance exactly `R` from one point. -/

theorem con_zero_iff (z : Z) (h : con z = 0) :
    ‖pin z 1 - hub1 z‖ = Rad z ∧ ‖pin z 2 - hub0 z‖ = Rad z ∧ ‖pin z 3 - hub0 z‖ = Rad z ∧
    ‖pin z 8 - hub1 z‖ = Rad z ∧ ‖waist z - ringSite z 6‖ = Rad z := by
  have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
  have h3 := congrFun h 3; have h4 := congrFun h 4
  simp [con] at h0 h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Reflected fan constraints: `|U4 - H0| = |U3 - H0|`, `|U5 - H0| = |U2 - H0|`,
`|U6 - H1| = |U1 - H1|`. -/
theorem reflected_fan (z : Z) :
    ‖pin z 4 - hub0 z‖ = ‖pin z 3 - hub0 z‖ ∧ ‖pin z 5 - hub0 z‖ = ‖pin z 2 - hub0 z‖ ∧
    ‖pin z 6 - hub1 z‖ = ‖pin z 1 - hub1 z‖ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← norm_conj_sub_real _ _ (conj_hub0 z), conj_pin]; rfl
  · rw [← norm_conj_sub_real _ _ (conj_hub0 z), conj_pin]; rfl
  · rw [← norm_conj_sub_real _ _ (conj_hub1 z), conj_pin]; rfl

/-- Mirror waist: `conj W` is at distance `R` from `C2` iff `W` is from `C6`. -/
theorem mirror_waist (z : Z) : ‖conj (waist z) - ringSite z 2‖ = ‖waist z - ringSite z 6‖ := by
  have h : ringSite z 2 = conj (ringSite z 6) := by rw [conj_ringSite]; rfl
  rw [h, ← map_sub, Complex.norm_conj]

end DCP.N11
