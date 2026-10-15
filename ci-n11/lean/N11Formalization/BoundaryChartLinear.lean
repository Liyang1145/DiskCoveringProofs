import Mathlib

/-!
Constant linear boundary system in reflection-fixed width/direction coordinates.
Coordinates x0..4 = widths; x5..8 = theta0..3; x9..10 = hub abscissae; x11 = radius.
This is NOT the physical-coordinate boundary Jacobian. Local width/rho diffeomorphism,
actual root branch membership and Fréchet chain identity remain separate obligations.
The five rows are boundary-switch orbits 0,1,2,3,8, NOT the five TC interior contacts.
-/
set_option autoImplicit false
namespace N11Formalization.BoundaryChartLinear

noncomputable section

def boundary (x : Fin 12 → ℝ) : Fin 5 → ℝ :=
  ![x 6 - x 5 - x 0 - x 1,
    x 7 - x 6 - x 1 - x 2,
    x 8 - x 7 - x 2 - x 3,
    -x 8 - x 3 - x 4,
    2 * x 5 - 2 * x 0]

def chart (z : Fin 7 → ℝ) : Fin 12 → ℝ :=
  ![z 0, z 1, z 2, z 3, -2 * (z 0 + z 1 + z 2 + z 3),
    z 0, 2 * z 0 + z 1, 2 * z 0 + 2 * z 1 + z 2,
    2 * z 0 + 2 * z 1 + 2 * z 2 + z 3, z 4, z 5, z 6]

def extract (x : Fin 12 → ℝ) : Fin 7 → ℝ :=
  ![x 0, x 1, x 2, x 3, x 9, x 10, x 11]

def rightInverse (b : Fin 5 → ℝ) : Fin 12 → ℝ :=
  ![0, 0, 0, 0, -b 3 - (b 2 + b 1 + b 0 + b 4 / 2),
    b 4 / 2, b 0 + b 4 / 2, b 1 + b 0 + b 4 / 2,
    b 2 + b 1 + b 0 + b 4 / 2, 0, 0, 0]

theorem boundary_rightInverse (b : Fin 5 → ℝ) : boundary (rightInverse b) = b := by
  funext i
  fin_cases i <;> simp [boundary, rightInverse, Fin.reduceFinMk] <;> ring

theorem boundary_surjective : Function.Surjective boundary := by
  intro b
  exact ⟨rightInverse b, boundary_rightInverse b⟩

theorem boundary_chart (z : Fin 7 → ℝ) : boundary (chart z) = 0 := by
  funext i
  fin_cases i <;> simp [boundary, chart, Fin.reduceFinMk] <;> ring

theorem extract_chart (z : Fin 7 → ℝ) : extract (chart z) = z := by
  funext i
  fin_cases i <;> simp [extract, chart, Fin.reduceFinMk]

theorem chart_injective : Function.Injective chart := by
  intro z w h
  have he := congrArg extract h
  simpa only [extract_chart] using he

theorem chart_extract_of_boundary_zero (x : Fin 12 → ℝ) (h : boundary x = 0) :
    chart (extract x) = x := by
  have h0 := congrFun h (0 : Fin 5)
  have h1 := congrFun h (1 : Fin 5)
  have h2 := congrFun h (2 : Fin 5)
  have h3 := congrFun h (3 : Fin 5)
  have h4 := congrFun h (4 : Fin 5)
  simp [boundary, Fin.reduceFinMk] at h0 h1 h2 h3 h4
  funext i
  fin_cases i <;> simp [chart, extract, Fin.reduceFinMk] <;> linarith

/-- Every kernel vector has unique seven chart coordinates; no numerical rank assumption. -/
theorem kernel_iff_chart (x : Fin 12 → ℝ) :
    boundary x = 0 ↔ ∃! z : Fin 7 → ℝ, chart z = x := by
  constructor
  · intro h
    refine ⟨extract x, chart_extract_of_boundary_zero x h, ?_⟩
    intro z hz
    have he := congrArg extract hz
    simpa only [extract_chart] using he
  · rintro ⟨z, hz, _⟩
    rw [← hz]
    exact boundary_chart z

/-- Explicit row independence: any annihilating row combination is zero. -/
theorem rows_independent (lam : Fin 5 → ℝ)
    (h : ∀ x : Fin 12 → ℝ, ∑ i, lam i * boundary x i = 0) : lam = 0 := by
  funext i
  have hi := h (rightInverse (Pi.single i 1))
  rw [boundary_rightInverse] at hi
  simpa [Pi.single_apply] using hi

/-- The exact source width/direction affine chart, retaining the angular origin -pi. -/
def affineChart (z : Fin 7 → ℝ) : Fin 12 → ℝ :=
  ![z 0, z 1, z 2, z 3, Real.pi - 2 * (z 0 + z 1 + z 2 + z 3),
    z 0 - Real.pi, 2 * z 0 + z 1 - Real.pi,
    2 * z 0 + 2 * z 1 + z 2 - Real.pi,
    2 * z 0 + 2 * z 1 + 2 * z 2 + z 3 - Real.pi, z 4, z 5, z 6]

def affineBoundary (x : Fin 12 → ℝ) : Fin 5 → ℝ :=
  boundary x + Pi.single 4 (2 * Real.pi)

theorem affineBoundary_affineChart (z : Fin 7 → ℝ) :
    affineBoundary (affineChart z) = 0 := by
  funext i
  fin_cases i <;> simp [affineBoundary, boundary, affineChart, Pi.single_apply, Fin.reduceFinMk] <;> ring

theorem affineChart_extract_of_zero (x : Fin 12 → ℝ) (h : affineBoundary x = 0) :
    affineChart (extract x) = x := by
  have h0 := congrFun h (0 : Fin 5)
  have h1 := congrFun h (1 : Fin 5)
  have h2 := congrFun h (2 : Fin 5)
  have h3 := congrFun h (3 : Fin 5)
  have h4 := congrFun h (4 : Fin 5)
  simp [affineBoundary, boundary, Pi.single_apply, Fin.reduceFinMk] at h0 h1 h2 h3 h4
  funext i
  fin_cases i <;> simp [affineChart, extract, Fin.reduceFinMk] <;> linarith

end
end N11Formalization.BoundaryChartLinear
#print axioms N11Formalization.BoundaryChartLinear.boundary_surjective
#print axioms N11Formalization.BoundaryChartLinear.kernel_iff_chart
#print axioms N11Formalization.BoundaryChartLinear.rows_independent
#print axioms N11Formalization.BoundaryChartLinear.affineChart_extract_of_zero
#check @N11Formalization.BoundaryChartLinear.kernel_iff_chart
#check @N11Formalization.BoundaryChartLinear.affineChart_extract_of_zero

