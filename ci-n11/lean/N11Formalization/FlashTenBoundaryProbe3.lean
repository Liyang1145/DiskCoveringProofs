import N11Formalization.FlashTenBoundary
open scoped Interval
open MeasureTheory
namespace N11Formalization
noncomputable def angPt (θ : ℝ) : Point := !₂[Real.cos θ, Real.sin θ]

example : Continuous angPt := by
  have h1 : Continuous fun θ : ℝ => ![Real.cos θ, Real.sin θ] := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> continuity
  have h2 : Continuous fun θ : ℝ => (EuclideanSpace.equiv (Fin 2) ℝ) (angPt θ) := by
    convert h1 using 1
    ext θ i; fin_cases i <;> simp [angPt]
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp h2
