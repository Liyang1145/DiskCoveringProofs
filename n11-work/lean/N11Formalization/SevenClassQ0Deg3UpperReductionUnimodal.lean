import N11Formalization.SevenClassQ0Deg3UpperTables

/-! Lane A: correct finite-peak factorization of the q0 degree-three edge table.

The right-endpoint reduction is invalid because positive edge multipliers make
`edgeUpper` decrease near zero.  The exact table data are nevertheless
single-peaked.  This module factors each all-grid edge bound into an increasing
prefix, a decreasing suffix, and one peak-value check.  It does not assume the
analytic monotonicity obligations; they remain explicit in `EdgeUnimodal`. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal

open MetricAreaRationalCertificate
open SevenClassQ0Deg3UpperTables

/-- Exact grid witnesses from `q0-degree3-piecewise-8.json`. -/
def edgeWitness : Fin 21 → Fin 2049 := ![
  543, 878, 1112, 1064, 1073, 1073, 1064,
  1112, 878, 1489, 1489, 1118, 0, 0, 486,
  389, 411, 406, 411, 389, 486]

def edgeCoeff (i : Fin 21) : ℚ := ∑ j ∈ tableEdges i, mu j

attribute [local simp] edgeUpper nodeQ edgeCoeff tableEdges

def EdgeIncTo (i : Fin 21) : Prop :=
  ∀ k : Fin 2049, k ≤ edgeWitness i →
    edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) ≤
      edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 (edgeWitness i))

def EdgeDecFrom (i : Fin 21) : Prop :=
  ∀ k : Fin 2049, edgeWitness i ≤ k →
    edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) ≤
      edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 (edgeWitness i))

def EdgePeakValid (i : Fin 21) : Prop :=
  edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 (edgeWitness i)) ≤
    edgeMaxAt i

def EdgeUnimodal : Prop :=
  ∀ i : Fin 21, EdgeIncTo i ∧ EdgeDecFrom i ∧ EdgePeakValid i

/-- The two analytic shape obligations, with the 21 peak comparisons kept
separate so they can be discharged by exact rational evaluation. -/
def EdgeMonotone : Prop :=
  ∀ i : Fin 21, EdgeIncTo i ∧ EdgeDecFrom i

/-- A single-peak factorization replaces 21 × 2049 edge checks by the
analytic shape obligations and 21 peak comparisons. -/
theorem edgeValid_of_unimodal (h : EdgeUnimodal) : EdgeValid := by
  intro i k
  obtain ⟨hinc, hdec, hpeak⟩ := h i
  by_cases hk : k ≤ edgeWitness i
  · exact (hinc k hk).trans hpeak
  · exact (hdec k (le_of_lt (lt_of_not_ge hk))).trans hpeak

/-- The 21 peak comparisons recorded by the exact rational audit, split into
separate kernel checks to keep elaboration bounded. -/
theorem edgePeakValid_0 : EdgePeakValid 0 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_1 : EdgePeakValid 1 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_2 : EdgePeakValid 2 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_3 : EdgePeakValid 3 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_4 : EdgePeakValid 4 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_5 : EdgePeakValid 5 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_6 : EdgePeakValid 6 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_7 : EdgePeakValid 7 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_8 : EdgePeakValid 8 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_9 : EdgePeakValid 9 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_10 : EdgePeakValid 10 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_11 : EdgePeakValid 11 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_12 : EdgePeakValid 12 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_13 : EdgePeakValid 13 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_14 : EdgePeakValid 14 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_15 : EdgePeakValid 15 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_16 : EdgePeakValid 16 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_17 : EdgePeakValid 17 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_18 : EdgePeakValid 18 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_19 : EdgePeakValid 19 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

theorem edgePeakValid_20 : EdgePeakValid 20 := by
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    edgeWitness, nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi]

/-- All 21 peaks are exactly the separately checked comparisons above. -/
theorem edgePeakValid_all : ∀ i : Fin 21, EdgePeakValid i := by
  intro i
  fin_cases i <;>
    first
    | exact edgePeakValid_0
    | exact edgePeakValid_1
    | exact edgePeakValid_2
    | exact edgePeakValid_3
    | exact edgePeakValid_4
    | exact edgePeakValid_5
    | exact edgePeakValid_6
    | exact edgePeakValid_7
    | exact edgePeakValid_8
    | exact edgePeakValid_9
    | exact edgePeakValid_10
    | exact edgePeakValid_11
    | exact edgePeakValid_12
    | exact edgePeakValid_13
    | exact edgePeakValid_14
    | exact edgePeakValid_15
    | exact edgePeakValid_16
    | exact edgePeakValid_17
    | exact edgePeakValid_18
    | exact edgePeakValid_19
    | exact edgePeakValid_20

/-- Once the two monotonicity sides are proved for every edge, the peak checks
above pay all 21 × 2049 grid inequalities. -/
theorem edgeValid_of_monotone (h : EdgeMonotone) : EdgeValid :=
  edgeValid_of_unimodal fun i => ⟨(h i).1, (h i).2, edgePeakValid_all i⟩

end N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal
#check @N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal.edgeValid_of_unimodal
#check @N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal.edgeValid_of_monotone
#print axioms N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal.edgeValid_of_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal.edgePeakValid_all
