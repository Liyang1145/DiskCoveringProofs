import N11Formalization.ResumeNetwork
import N11Formalization.Geometry.ArcCovering
import N11Formalization.ResumeGlobalAnchor
import N11Formalization.ResumeGlobalDomain

/-!
# ResumeGlobal: Fin 9 simplex point ↦ unit anchors of the 51-edge network oracle.
U_i = circleMap θ_i, θ_i = anchorAngle L D y i (canonical chart, anchor 0 at angle 0).
-/

namespace N11Formalization.ResumeGlobal
open N11Formalization N11Formalization.ResumeNetwork

noncomputable def anchorsOf (L D : ℝ) (y : Fin 9 → ℝ) : Fin 9 → Point :=
  fun i => circleMap (anchorAngle L D y i)

theorem anchorsOf_norm (L D : ℝ) (y : Fin 9 → ℝ) (i : Fin 9) :
    ‖anchorsOf L D y i‖ = 1 := circleMap_norm _

theorem anchorsOf_zero (L D : ℝ) (y : Fin 9 → ℝ) :
    anchorsOf L D y 0 = circleMap 0 := by
  simp [anchorsOf, anchorAngle]

/-- Oracle on the chart: nonnegative, and finite (feasible at r = 2). -/
theorem oracleOf_nonneg (L D : ℝ) (y : Fin 9 → ℝ) : 0 ≤ V2 (anchorsOf L D y) :=
  oracle_nonneg fun i => (anchorsOf_norm L D y i).le

/-- Wrap anchor: θ_9 = 2π ⇒ circleMap θ_9 = circleMap θ_0 (cyclic closure of U_8→U_0). -/
theorem anchor_wrap (L D : ℝ) (y : Fin 9 → ℝ) (hy1 : ∑ q, y q = 1)
    (hD : D = 9 * L - 2 * Real.pi) :
    circleMap (anchorAngle L D y 9) = anchorsOf L D y 0 := by
  rw [anchor_nine L D y hy1 hD, anchorsOf_zero]
  simpa using circleMap_add_two_pi 0

/-- Chart-level global target (the consumer's `hglob` on the source domain). -/
def GlobalOnChart (L D R : ℝ) : Prop :=
  ∀ y : Fin 9 → ℝ, InSimplex9 y → R ^ 2 ≤ V2 (anchorsOf L D y)

end N11Formalization.ResumeGlobal

#print axioms N11Formalization.ResumeGlobal.oracleOf_nonneg
#print axioms N11Formalization.ResumeGlobal.anchor_wrap
