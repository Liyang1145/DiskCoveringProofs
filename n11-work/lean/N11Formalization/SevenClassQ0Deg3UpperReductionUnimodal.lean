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

/-- Exact sums of the corresponding `tableEdges`, emitted as literals so the
21 finite peak checks do not leave an opaque `Finset.sum` in the goal. -/
def edgeCoeff : Fin 21 → ℚ := ![
  (970935700000000000000000000000000000271 / 10000000000000000000000000000000000000000),
  (6430660000000000000000000000000000001523 / 200000000000000000000000000000000000000000),
  (-155461200000000000000000000000000000027 / 8000000000000000000000000000000000000000),
  (-2194982499999999999999999999999999999773 / 250000000000000000000000000000000000000000),
  (-21638199999999999999999999999999999996687 / 2000000000000000000000000000000000000000000),
  (-4327548000000000000000000000000000000147 / 400000000000000000000000000000000000000000),
  (-4389845000000000000000000000000000000091 / 500000000000000000000000000000000000000000),
  (-19432139999999999999999999999999999991001 / 1000000000000000000000000000000000000000000),
  (257230480000000000000000000000000000207 / 8000000000000000000000000000000000000000),
  (-4726257000000000000000000000000000001847 / 50000000000000000000000000000000000000000),
  (-1181564375000000000000000000000000000547 / 12500000000000000000000000000000000000000),
  (-82572800000000000000000000000000000109 / 4000000000000000000000000000000000000000),
  (17097552000000000000000000000000000004361 / 100000000000000000000000000000000000000000),
  (17097551000000000000000000000000000003679 / 100000000000000000000000000000000000000000),
  (848282000000000000000000000000000000193 / 8000000000000000000000000000000000000000),
  (596947800000000000000000000000000000129 / 5000000000000000000000000000000000000000),
  (14585996250000000000000000000000000003551 / 125000000000000000000000000000000000000000),
  (234700780000000000000000000000000000053097 / 2000000000000000000000000000000000000000000),
  (7293012500000000000000000000000000001649 / 62500000000000000000000000000000000000000),
  (59694785000000000000000000000000000013367 / 500000000000000000000000000000000000000000),
  (21207150000000000000000000000000000007113 / 200000000000000000000000000000000000000000)
]

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
  unfold EdgeCheck
  obtain ⟨hinc, hdec, hpeak⟩ := h i
  by_cases hk : k ≤ edgeWitness i
  · exact (hinc k hk).trans hpeak
  · exact (hdec k (le_of_lt (lt_of_not_ge hk))).trans hpeak

/-- The 21 peak comparisons recorded by the exact rational audit, split into
separate kernel checks to keep elaboration bounded. -/
theorem edgePeakValid_0 : EdgePeakValid 0 := by
  unfold EdgePeakValid
  rw [show edgeWitness 0 = (543 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_1 : EdgePeakValid 1 := by
  unfold EdgePeakValid
  rw [show edgeWitness 1 = (878 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_2 : EdgePeakValid 2 := by
  unfold EdgePeakValid
  rw [show edgeWitness 2 = (1112 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_3 : EdgePeakValid 3 := by
  unfold EdgePeakValid
  rw [show edgeWitness 3 = (1064 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_4 : EdgePeakValid 4 := by
  unfold EdgePeakValid
  rw [show edgeWitness 4 = (1073 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_5 : EdgePeakValid 5 := by
  unfold EdgePeakValid
  rw [show edgeWitness 5 = (1073 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_6 : EdgePeakValid 6 := by
  unfold EdgePeakValid
  rw [show edgeWitness 6 = (1064 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_7 : EdgePeakValid 7 := by
  unfold EdgePeakValid
  rw [show edgeWitness 7 = (1112 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_8 : EdgePeakValid 8 := by
  unfold EdgePeakValid
  rw [show edgeWitness 8 = (878 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_9 : EdgePeakValid 9 := by
  unfold EdgePeakValid
  rw [show edgeWitness 9 = (1489 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_10 : EdgePeakValid 10 := by
  unfold EdgePeakValid
  rw [show edgeWitness 10 = (1489 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_11 : EdgePeakValid 11 := by
  unfold EdgePeakValid
  rw [show edgeWitness 11 = (1118 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_12 : EdgePeakValid 12 := by
  unfold EdgePeakValid
  rw [show edgeWitness 12 = (0 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_13 : EdgePeakValid 13 := by
  unfold EdgePeakValid
  rw [show edgeWitness 13 = (0 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_14 : EdgePeakValid 14 := by
  unfold EdgePeakValid
  rw [show edgeWitness 14 = (486 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_15 : EdgePeakValid 15 := by
  unfold EdgePeakValid
  rw [show edgeWitness 15 = (389 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_16 : EdgePeakValid 16 := by
  unfold EdgePeakValid
  rw [show edgeWitness 16 = (411 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_17 : EdgePeakValid 17 := by
  unfold EdgePeakValid
  rw [show edgeWitness 17 = (406 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_18 : EdgePeakValid 18 := by
  unfold EdgePeakValid
  rw [show edgeWitness 18 = (411 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_19 : EdgePeakValid 19 := by
  unfold EdgePeakValid
  rw [show edgeWitness 19 = (389 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

theorem edgePeakValid_20 : EdgePeakValid 20 := by
  unfold EdgePeakValid
  rw [show edgeWitness 20 = (486 : Fin 2049) by decide +kernel]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

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
