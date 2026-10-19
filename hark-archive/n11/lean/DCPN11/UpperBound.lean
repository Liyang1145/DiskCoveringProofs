/-
DCPN11/UpperBound.lean  —  C892: the C891 root configuration covers D at radius R*.

STATUS: NOT YET COMPILED (see STATUS.md).
Source: N11-GLOBAL-OPTIMALITY-THEOREM.md §"Exact definition and an attaining configuration";
STRICT-EMPTY-FACET-COMPLETENESS.md; check_tc_root_geometry.py; tools/mathcheck_n11.py
`geometry_check`; docs/N11_CHECK_SCOPE.md.
-/
import DCPN11.Problem
import DCPN11.Identities

open Real Metric Set

noncomputable section

namespace DCP.N11

/-- The eleven centres `C0..C8, H0, H1` (checker indices 0..10). -/
def centers (z : Z) : Fin 11 → ℂ := fun i =>
  if h : i.val < 9 then ringSite z ⟨i.val, h⟩ else if i.val = 9 then hub0 z else hub1 z

/-- Legality of the root box (checker `geometry_check`, first four `require`s):
`0 < a_k < π/2`, `sin² a_k < R²`, `0 < ρ_k < 1`, hubs strictly interior, waist branch.
Interval-trigonometric facts on the box; rational parts are machine-checked in
`DCPN11Core/RootBox.lean` (`angles_pos`, `angle_sum_hi/lo`, `angles_hi`, `hubs_interior`,
`waist_branch`). -/
structure Legal (z : Z) : Prop where
  R_pos : 0 < Rad z
  angle_pos : ∀ k, 0 < halfAngle z k
  angle_lt : ∀ k, halfAngle z k < π / 2
  branch : ∀ k, sin (halfAngle z k) ^ 2 < Rad z ^ 2
  rho_pos : ∀ k, 0 < rho z k
  rho_lt_one : ∀ k, rho z k < 1
  waist_branch : ((z 5 - z 4) / 2) ^ 2 < Rad z ^ 2

theorem legal_of_box {p : Fin 12 → ℝ} (hp : InBox p) : Legal (zPart p) := by
  sorry -- interval arithmetic on the box (sin/cos enclosures + `RootBox` rational facts)

/-- Boundary coverage: the nine arcs `[θk - ak, θk + ak]` tile the circle (`halfAngle_sum`,
`theta_switch`, `theta_switch_wrap`) and on its arc `|x - C_k|² = ρ² - 2ρ cos(φ-θk) + 1
≤ ρ² - 2ρ cos ak + 1 = R²`. Elementary; not yet written out. -/
theorem boundary_covered (z : Z) (hz : Legal z) :
    ∀ x : ℂ, ‖x‖ = 1 → ∃ i, dist x (centers z i) ≤ Rad z := by
  sorry

/-- Voronoi critical-point lemma (general, configuration independent): for finitely many
sites, `g(x) = min_i |x - c_i|` attains its maximum on `D` either on the circle `‖x‖ = 1`
or at a point `x` in the interior which lies in the convex hull of its nearest sites
(a Voronoi vertex when the nearest set has ≥ 3 affinely spanning sites). -/
theorem voronoi_critical_point {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℂ) :
    ∃ x ∈ D, (∀ y ∈ D, (⨅ i, dist y (c i)) ≤ ⨅ i, dist x (c i)) ∧
      (‖x‖ = 1 ∨ x ∈ convexHull ℝ (c '' {i | dist x (c i) = ⨅ j, dist x (c j)})) := by
  sorry

/-- Delaunay certificate of the root (checker `geometry_check`, interval part): the 11 listed
triangles (`DCPCore.faces`, incidence machine-checked) triangulate the hull, have strictly
empty circumcircles, their circumcentres lie in `int D`, nine have circumradius exactly `R`
(`Identities.lean`) and two (`(0,1,H1)`, `(7,8,H1)`) strictly smaller. Consequently every
interior point that is in the convex hull of its nearest sites is within `R` of a site. -/
theorem delaunay_certificate {p : Fin 12 → ℝ} (hp : InBox p) (hk : kkt p = 0) :
    ∀ x ∈ D, ‖x‖ < 1 →
      x ∈ convexHull ℝ ((centers (zPart p)) ''
        {i | dist x (centers (zPart p) i) = ⨅ j, dist x (centers (zPart p) j)}) →
      ∃ i, dist x (centers (zPart p) i) ≤ Rad (zPart p) := by
  sorry

/-- **C892.** The root configuration covers `D` at radius `p 6 = R*`. -/
theorem root_covers {p : Fin 12 → ℝ} (hp : InBox p) (hk : kkt p = 0) :
    Covers (centers (zPart p)) (Rad (zPart p)) := by
  -- draft assembly: take the maximiser of the nearest-site distance; it is either on the
  -- circle (`boundary_covered`) or an interior critical point (`delaunay_certificate`).
  have hL := legal_of_box hp
  obtain ⟨x₀, hx₀D, hmax, hcase⟩ := voronoi_critical_point (n := 11) (by norm_num)
    (centers (zPart p))
  have hx₀ : ∃ i, dist x₀ (centers (zPart p) i) ≤ Rad (zPart p) := by
    rcases hcase with h1 | hhull
    · exact boundary_covered _ hL x₀ h1
    · by_cases h1 : ‖x₀‖ = 1
      · exact boundary_covered _ hL x₀ h1
      · have hlt : ‖x₀‖ < 1 := lt_of_le_of_ne (by simpa [D] using hx₀D) h1
        exact delaunay_certificate hp hk x₀ hx₀D hlt hhull
  intro y hy
  obtain ⟨i, hi⟩ := hx₀
  have hinf : (⨅ j, dist y (centers (zPart p) j)) ≤ Rad (zPart p) :=
    (hmax y hy).trans ((ciInf_le (Finite.bddBelow_range _) i).trans hi)
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun j => dist y (centers (zPart p) j))
  exact mem_iUnion.2 ⟨j, mem_closedBall.2 (hj ▸ hinf)⟩

/-- Upper bound `r_D(11) ≤ R*`, with an explicit attaining configuration. -/
theorem upper_bound : ∃ c : Fin 11 → ℂ, Covers c Rstar := by
  -- draft
  obtain ⟨p, hp, hk, h6⟩ := Rstar_spec
  exact ⟨centers (zPart p), h6 ▸ root_covers hp hk⟩

end DCP.N11
