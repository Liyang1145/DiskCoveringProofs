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

/-- A single-peak factorization replaces 21 × 2049 edge checks by the
analytic shape obligations and 21 peak comparisons. -/
theorem edgeValid_of_unimodal (h : EdgeUnimodal) : EdgeValid := by
  intro i k
  obtain ⟨hinc, hdec, hpeak⟩ := h i
  by_cases hk : k ≤ edgeWitness i
  · exact (hinc k hk).trans hpeak
  · exact (hdec k (le_of_lt (lt_of_not_ge hk))).trans hpeak

end N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal
#check @N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal.edgeValid_of_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal.edgeValid_of_unimodal
