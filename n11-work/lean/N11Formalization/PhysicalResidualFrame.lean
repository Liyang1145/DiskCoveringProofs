import Mathlib
import N11Formalization.BoundaryChartSource
import N11Formalization.TCChartStationarityRoot
import N11Formalization.RootBoundaryDualConsumer
set_option autoImplicit false
namespace N11Formalization.PhysicalResidualFrame
open N11Formalization
open BoundaryChartLinear BoundaryChartSource
noncomputable section

/-- Independent reflection-fixed half-widths, including the central ring width. -/
def widths (x : Fin 12 → ℝ) : Fin 9 → ℝ :=
  ![x 0, x 1, x 2, x 3, x 4, x 3, x 2, x 1, x 0]

/-- Independent reflection-fixed directions, with the central direction fixed to zero. -/
def directions (x : Fin 12 → ℝ) : Fin 9 → ℝ :=
  ![x 5, x 6, x 7, x 8, 0, -x 8, -x 7, -x 6, -x 5]

def radial (x : Fin 12 → ℝ) (k : Fin 9) : ℝ :=
  Real.cos (widths x k) - Real.sqrt ((x 11)^2 - Real.sin (widths x k)^2)

def center (x : Fin 12 → ℝ) (k : Fin 9) : Point :=
  !₂[radial x k * Real.cos (directions x k),
     radial x k * Real.sin (directions x k)]

def endpoint (x : Fin 12 → ℝ) (k : Fin 9) : Point :=
  !₂[Real.cos (directions x k + widths x k), Real.sin (directions x k + widths x k)]

def pin (x : Fin 12 → ℝ) (k : Fin 9) : Point :=
  center x k + center x (k+1) - endpoint x k

def hubA (x : Fin 12 → ℝ) : Point := !₂[x 9, 0]
def hubB (x : Fin 12 → ℝ) : Point := !₂[x 10, 0]
def centralPin (x : Fin 12 → ℝ) : Point :=
  !₂[(x 9+x 10)/2, Real.sqrt ((x 11)^2-((x 10-x 9)/2)^2)]

/-- Actual length residuals evaluated on the independent width/direction frame.
Away from the five boundary equations, these are not asserted to be equal-circle pins. -/
def residualFrame (x : Fin 12 → ℝ) : Fin 5 → ℝ :=
  ![dist (pin x 1) (hubB x) - x 11,
    dist (pin x 2) (hubA x) - x 11,
    dist (pin x 3) (hubA x) - x 11,
    dist (pin x 8) (hubB x) - x 11,
    dist (centralPin x) (center x 6) - x 11]

theorem widths_source (u : Fin 12 → ℝ) : widths (sourceFrame u) = angleVec u := by
  funext k
  fin_cases k <;> simp [widths, sourceFrame, angleVec]

theorem directions_source (u : Fin 12 → ℝ) :
    directions (sourceFrame u) = thetaOf (angleVec u) := by
  funext k
  fin_cases k <;> simp [directions, sourceFrame, thetaOf, angleVec] <;> ring

theorem radial_source (u : Fin 12 → ℝ) (k : Fin 9) :
    radial (sourceFrame u) k = rhoK u k := by
  rw [radial, widths_source]
  rfl

theorem center_source (u : Fin 12 → ℝ) (k : Fin 9) :
    center (sourceFrame u) k = ringCenter u k := by
  rw [center, radial_source, directions_source]
  rfl

theorem endpoint_source (u : Fin 12 → ℝ) (k : Fin 9) :
    endpoint (sourceFrame u) k = arcEnd u k := by
  rw [endpoint, directions_source, widths_source]
  rfl

theorem pin_source (u : Fin 12 → ℝ) (k : Fin 9) :
    pin (sourceFrame u) k = Uvec u k := by
  rw [pin, center_source, center_source, endpoint_source]
  rfl

theorem hubA_source (u : Fin 12 → ℝ) : hubA (sourceFrame u) = hub0 u := rfl
theorem hubB_source (u : Fin 12 → ℝ) : hubB (sourceFrame u) = hub1 u := rfl
theorem centralPin_source (u : Fin 12 → ℝ) : centralPin (sourceFrame u) = wPoint u := rfl

theorem residualFrame_source (u : Fin 12 → ℝ) :
    residualFrame (sourceFrame u) = residual u := by
  simp only [residualFrame, pin_source, hubA_source, hubB_source,
    centralPin_source, center_source]
  rfl

/-- The complete function identity, not just agreement at the root. -/
theorem residualFrame_chart (z : Fin 7 → ℝ) :
    residualFrame (affineChart z) = residualFun z := by
  let u : Fin 12 → ℝ := fun i => if h : (i : ℕ)<7 then z ⟨i,h⟩ else 0
  have h7 : first7 u = z := by
    funext i
    simp [u, first7, i.isLt]
  have hframe : sourceFrame u = affineChart z := by
    rw [sourceFrame_eq_affineChart, h7]
  rw [← hframe, residualFrame_source]
  rfl

def objectiveFrame (u : Fin 12 → ℝ) (x : Fin 12 → ℝ) : ℝ :=
  x 11 - ∑ k : Fin 5, last5 u k * residualFrame x k

theorem objectiveFrame_chart (u : Fin 12 → ℝ) :
    (fun z : Fin 7 → ℝ => objectiveFrame u (affineChart z)) =
      TCChartStationarity.objective u := by
  funext z
  simp only [objectiveFrame, residualFrame_chart, TCChartStationarity.objective]
  rfl

/-- Source-root boundary dual consumer with the chart-stationarity premise discharged
by the full physical residual identity. Only the physical derivative is left as a premise. -/
theorem sourceRoot_dual
    {df : (Fin 12 → ℝ) →L[ℝ] ℝ}
    (hdf : HasFDerivAt (objectiveFrame SourceExactRoot.sourceRoot) df
      (sourceFrame SourceExactRoot.sourceRoot)) :
    ∀ x : Fin 12 → ℝ,
      df x = ∑ j : Fin 5,
        BoundaryChartDual.multiplier (fun i => df (Pi.single i 1)) j * boundary x j := by
  apply RootBoundaryDualConsumer.physical_dual_factorization hdf
  rw [objectiveFrame_chart]
  exact TCChartStationarityRoot.sourceRoot_stationarity

end
end N11Formalization.PhysicalResidualFrame
#print N11Formalization.PhysicalResidualFrame.residualFrame_chart
#print N11Formalization.PhysicalResidualFrame.sourceRoot_dual
#print axioms N11Formalization.PhysicalResidualFrame.residualFrame_chart
#print axioms N11Formalization.PhysicalResidualFrame.sourceRoot_dual
