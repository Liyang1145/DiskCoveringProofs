import Mathlib
import N11Formalization.SourceAlphaOf
import N11Formalization.HarmonicSourceGeomConsumer
set_option autoImplicit false
namespace N11Formalization.SourceStressConsumer
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeDirichlet
open N11Formalization.ResumeHarmonic
open N11Formalization.HarmonicSourceTransport
open N11Formalization.HarmonicSourceGeomConsumer
open N11Formalization.SourceAlphaOf
open N11Formalization.ResumeLocalIncidence
open N11Formalization.SourceN2
open N11Formalization.FlashRootNetwork
open N11Formalization.LocalSharpAuxZ
open N11Formalization.HarmonicSourceGeometryV2
open N11Formalization.ResumeAnchorFlux
noncomputable section

/-- The explicit alphaOf factors produce a canonical 51-edge stress. -/
def alphaOfEdge (mu nu c b eta : Fin 9 → ℝ) (beta : Fin 9 → Fin 3 → ℝ) : Edge → ℝ :=
  alphaEdge (alphaOf mu nu c b eta beta)

/-- Parameterized source-stress consumer: factor positivity discharges nonnegativity and
zero stress on the two canonical slack face blocks; only the genuine 40 B2 force rows
remain as an explicit premise. -/
theorem exists_lift_of_alphaOf
    (mu nu c b eta : Fin 9 → ℝ) (beta : Fin 9 → Fin 3 → ℝ)
    (hface : ∀ j, 0 < mu j * c j)
    (htie : ∀ j, 0 < nu j * b j)
    (heta : ∀ j, 0 < eta j ∧ eta j < 1)
    (hbeta : ∀ j v, 0 < beta j v)
    {u : Fin 12 → ℝ}
    (hrows : ∀ w : SrcFree, ∀ q : Fin 2,
        ∑ s : SourceEdge,
          srcB2 u (HarmonicSourceGeometryV2.rowIdx w q) (srcFlat s) *
            alphaOfEdge mu nu c b eta beta (edgeMap s) = 0) :
    ∃ H : Free → Fin 9 → ℝ,
      (∀ v j, ∑ e, (alphaOfEdge mu nu c b eta beta e * incidence e v) * coeff H e j = 0) ∧
      (∀ W : Fin 9 → Point,
        energy (alphaOfEdge mu nu c b eta beta) W
            (fun i => lift H W (.inl i)) (fun f => lift H W (.inr f))
          = dirichletEnergy (alphaOfEdge mu nu c b eta beta) W
          ) ∧
      (∀ i, flux (alphaOfEdge mu nu c b eta beta) (canonAnchors u)
          (fun i => lift H (canonAnchors u) (.inl i))
          (fun f => lift H (canonAnchors u) (.inr f)) i
        = flux (alphaOfEdge mu nu c b eta beta) (canonAnchors u)
            (canonCenters u) (canonFaceZ u) i) ∧
      energy (alphaOfEdge mu nu c b eta beta) (canonAnchors u)
          (fun i => lift H (canonAnchors u) (.inl i))
          (fun f => lift H (canonAnchors u) (.inr f))
        = energy (alphaOfEdge mu nu c b eta beta) (canonAnchors u)
            (canonCenters u) (canonFaceZ u) := by
  have hpos : ∀ s : SourceEdge, 0 < alphaOf mu nu c b eta beta s :=
    SourceAlphaOf.alphaOf_pos_of mu nu c b eta beta hface htie heta hbeta
  have hα : ∀ e : Edge, 0 ≤ alphaOfEdge mu nu c b eta beta e := by
    intro e
    exact SourceAlphaOf.alphaEdge_nonneg_of _ (fun s => (hpos s).le) e
  have hzero : ∀ q : Fin 3,
      alphaOfEdge mu nu c b eta beta (.inr (5, q)) = 0 ∧
      alphaOfEdge mu nu c b eta beta (.inr (7, q)) = 0 := by
    intro q
    exact ⟨alphaEdge_slack_five _ q, alphaEdge_slack_seven _ q⟩
  apply exists_lift_of_source_B2force hα hzero
  exact hrows

end
end N11Formalization.SourceStressConsumer
#print axioms N11Formalization.SourceStressConsumer.exists_lift_of_alphaOf
