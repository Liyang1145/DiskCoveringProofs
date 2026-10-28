import N11Formalization.ActualOrderedMetricGraphs
import N11Formalization.ActualMetricClassReduction
import N11Formalization.MetricAreaRationalCertificate

/-! Lane A: exact reduction of the q0 degree-three field to the existing global
area-dual consumer (not freshly CI-verified in this worktree).

The graph normalization is already proved by
`ActualOrderedMetricGraphs.actual_q0_degree_three_table_graph`: a q0 cover with
a hub of degree three has the unique unrotated 21-edge table.  The remaining
mathematical input in the source proof is the exact rational area dual for
that table.  The structure below records precisely that input for every
original cover and refinement; no symmetry of the metric configuration is
assumed.  It is deliberately not inhabited here.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualQ0OrderedTwoFans ActualBoundaryNineTies ActualHubTriangleCensus
open ActualRefinementDoubleCounting ActualRingLinkBoundaryData
open ActualOrderedMetricGraphs ActualCanonicalSitePermutation
open ActualMetricClassReduction MetricAreaRationalCertificate

/-- The complete certificate consumed by the existing rational area dual,
bundled for one actual q0 refinement. -/
structure Degree3AreaCertificate {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) where
  v : NineTies c r
  mu : Fin 11 → ℚ
  lam : ℚ
  lam_nonnegative : 0 ≤ lam
  U : ℚ
  grid_covers_pi : RatInterval.piHi ≤ U
  N : ℕ
  grid_positive : 0 < N
  node : Fin (N+1) → ℚ
  node_valid : ∀ k, NodeValid (nodeQ U N k) (node k)
  edgeMax : Finset (Fin 11) → ℚ
  sectorMax : Fin 9 → ℚ
  edge_bound : ∀ e ∈ edges R, ∀ k : Fin (N+1),
    edgeUpper (∑ j ∈ e, mu j) (nodeQ U N k) ≤ edgeMax e
  sector_bound : ∀ (i : Fin 9) (k : Fin (N+1)),
    sectorUpper (mu (nextSite i)) lam (nodeQ U N k) (node k) ≤ sectorMax i
  strict : totalUpper R mu lam U N edgeMax sectorMax < RatInterval.piLo

/-- The source finite certificate contradicts the actual geometry. -/
theorem false_of_areaCertificate {c : Fin 11 → Point} {r : ℝ}
    {h : Representative c r} {hr : r < 19/50} {R : Refinement c r}
    (C : Degree3AreaCertificate h hr R) : False :=
  exclude_representative_of_rational_certificate h hr R C.v
    C.mu C.lam C.U C.lam_nonnegative C.grid_covers_pi C.N C.grid_positive
    C.node C.node_valid C.edgeMax C.sectorMax C.edge_bound C.sector_bound C.strict

/-- The exact remaining q0(3,10) obligation: one area-dual certificate for
each actual cover/refinement whose ordered run has length one. -/
structure Q0Degree3AreaInput : Prop where
  certificate : ∀ (c : Fin 11 → Point) (r : ℝ),
    ∀ (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
      (O : OrderedData R), O.run_length.val = 1 →
      Nonempty (Degree3AreaCertificate h hr R)

/-- The q0 degree-three field follows from the area input.  This theorem makes
the unpaid mathematical content explicit; it does not claim that the numeric
certificate has been instantiated. -/
theorem q0_degree3_of_areaInput (H : Q0Degree3AreaInput) : Q0RunExclusion 1 := by
  intro c r h hr R O hrun
  obtain ⟨C⟩ := H.certificate c r h hr R O hrun
  exact false_of_areaCertificate C

/-- Conversely, in the degree-three branch the exact finite graph table is
unconditional.  This connects the area certificate's edge set to the single
source graph rather than to an assumed rotation class. -/
theorem degree_three_table_graph {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card = 0)
    (hd : (neighbors R 9).card = 3 ∨ (neighbors R 10).card = 3) :
    ∃ k : Fin 9, ∃ b : Bool,
      edges R = (ActualOrderedMetricGraphs.degreeThreeTableEdges false 0 1).image
        (labelMap (ActualCanonicalSitePermutation.canonicalPerm k b)) :=
  ActualOrderedMetricGraphs.actual_q0_degree_three_table_graph h hr R hq hd

end N11Formalization.SevenClassQ0Deg3
#check @N11Formalization.SevenClassQ0Deg3.false_of_areaCertificate
#check @N11Formalization.SevenClassQ0Deg3.q0_degree3_of_areaInput
#check @N11Formalization.SevenClassQ0Deg3.degree_three_table_graph
#print axioms N11Formalization.SevenClassQ0Deg3.false_of_areaCertificate
#print axioms N11Formalization.SevenClassQ0Deg3.q0_degree3_of_areaInput
#print axioms N11Formalization.SevenClassQ0Deg3.degree_three_table_graph
