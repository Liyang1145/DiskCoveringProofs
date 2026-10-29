import N11Formalization.SevenClassQ0Deg3Bins

/-! Lane A: exact rational endpoint checks for the q0 degree-three node table.

Each proof is a denominator-cleared `norm_num` comparison for one endpoint.
Keeping the eight checks separate makes CI failures local to a table entry. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3EndpointChecks

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins

theorem endpointCheck_0 : EndpointCheck 0 := by
  norm_num [EndpointCheck, capQ, nodeQ, binHi, nodeBinAt,
    sinHiNLag, sinLoNLag, sinTQ, Finset.sum_range_succ]

theorem endpointCheck_1 : EndpointCheck 1 := by
  norm_num [EndpointCheck, capQ, nodeQ, binHi, nodeBinAt,
    sinHiNLag, sinLoNLag, sinTQ, Finset.sum_range_succ]

theorem endpointCheck_2 : EndpointCheck 2 := by
  norm_num [EndpointCheck, capQ, nodeQ, binHi, nodeBinAt,
    sinHiNLag, sinLoNLag, sinTQ, Finset.sum_range_succ]

theorem endpointCheck_3 : EndpointCheck 3 := by
  norm_num [EndpointCheck, capQ, nodeQ, binHi, nodeBinAt,
    sinHiNLag, sinLoNLag, sinTQ, Finset.sum_range_succ]

theorem endpointCheck_4 : EndpointCheck 4 := by
  norm_num [EndpointCheck, capQ, nodeQ, binHi, nodeBinAt,
    sinHiNLag, sinLoNLag, sinTQ, Finset.sum_range_succ]

theorem endpointCheck_5 : EndpointCheck 5 := by
  norm_num [EndpointCheck, capQ, nodeQ, binHi, nodeBinAt,
    sinHiNLag, sinLoNLag, sinTQ, Finset.sum_range_succ]

theorem endpointCheck_6 : EndpointCheck 6 := by
  norm_num [EndpointCheck, capQ, nodeQ, binHi, nodeBinAt,
    sinHiNLag, sinLoNLag, sinTQ, Finset.sum_range_succ]

theorem endpointCheck_7 : EndpointCheck 7 := by
  norm_num [EndpointCheck, capQ, nodeQ, binHi, nodeBinAt,
    sinHiNLag, sinLoNLag, sinTQ, Finset.sum_range_succ]

theorem endpointChecks : ∀ j : Fin 8, EndpointCheck j := by
  intro j
  fin_cases j
  · exact endpointCheck_0
  · exact endpointCheck_1
  · exact endpointCheck_2
  · exact endpointCheck_3
  · exact endpointCheck_4
  · exact endpointCheck_5
  · exact endpointCheck_6
  · exact endpointCheck_7

theorem endpointValid : EndpointValid :=
  endpointValid_of_eight endpointChecks

/-- Every node of the 2048-grid satisfies the degree-three node table. -/
theorem allNodeValid : ∀ k : Fin 2049,
    NodeValid (nodeQ RatInterval.piHi 2048 k) (nodeBin k) :=
  all_node_valid_of_grid_cap capMonotoneOnGrid endpointValid

end N11Formalization.SevenClassQ0Deg3EndpointChecks
#print axioms N11Formalization.SevenClassQ0Deg3EndpointChecks.allNodeValid
