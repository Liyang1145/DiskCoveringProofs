import N11Formalization.MetricAreaRationalCertificate

/-! Lane A: eight-bin node data for the q0 degree-three certificate.

The exact-rational audit in `ops/lanes/A/q0-degree3-piecewise-8.json` assigns
one node value to each of eight equal intervals of `[0, piHi]`.  This module
defines that table and reduces every one of the 2049 `NodeValid` obligations
to two explicitly named finite rational premises.  It does not assume either
premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3Bins

open MetricAreaRationalCertificate

/-- The eight-bin index of a node of the 2048-subdivision of `[0, piHi]`. -/
def binIndex (k : Fin 2049) : Fin 8 :=
  ⟨min 7 (k.val / 256), by omega⟩

/-- The last grid node in a bin (bin 7 includes the endpoint `k = 2048`). -/
def binHi (j : Fin 8) : Fin 2049 :=
  ⟨if j.val = 7 then 2048 else 256 * j.val + 255, by split <;> omega⟩

/-- The exact node values selected by the source interval audit. -/
def nodeBinAt (j : Fin 8) : ℚ :=
  ![239/1250, 239/1250, 133/625, 2721/10000,
    643/2000, 897/2500, 191/500, 1949/5000] j

/-- Piecewise-constant node table on all grid indices. -/
def nodeBin (k : Fin 2049) : ℚ := nodeBinAt (binIndex k)

/-- Unpaid grid reduction: the rational upper sine bracket is monotone at each
grid point up to its bin's right endpoint. -/
def CapMonotoneOnGrid : Prop :=
  ∀ k : Fin 2049, capQ (nodeQ RatInterval.piHi 2048 k) ≤
    capQ (nodeQ RatInterval.piHi 2048 (binHi (binIndex k)))

/-- The eight endpoint checks certified exactly by the Python audit. -/
def EndpointValid : Prop :=
  ∀ j : Fin 8, capQ (nodeQ RatInterval.piHi 2048 (binHi j)) ≤
    sinLoNLag (nodeBinAt j)

/-- One endpoint obligation, exposed separately so the eight rational
comparisons can be discharged independently. -/
def EndpointCheck (j : Fin 8) : Prop :=
  capQ (nodeQ RatInterval.piHi 2048 (binHi j)) ≤ sinLoNLag (nodeBinAt j)

theorem endpointValid_of_eight (h : ∀ j : Fin 8, EndpointCheck j) :
    EndpointValid := h

/-- All eight table entries lie in the admissible node interval. -/
theorem nodeBinAt_mem (j : Fin 8) : 0 ≤ nodeBinAt j ∧ nodeBinAt j ≤ 1 := by
  fin_cases j <;> norm_num [nodeBinAt]

/-- The grid-cap reduction eliminates the 2049-way finite enumeration. -/
theorem node_valid_of_grid_cap (hm : CapMonotoneOnGrid) (he : EndpointValid)
    (k : Fin 2049) :
    NodeValid (nodeQ RatInterval.piHi 2048 k) (nodeBin k) := by
  have ha := nodeBinAt_mem (binIndex k)
  exact ⟨ha.1, ha.2, (hm k).trans (he (binIndex k))⟩

/-- The complete `node_valid` field of the degree-three area certificate,
conditional on the two explicit finite rational obligations. -/
theorem all_node_valid_of_grid_cap (hm : CapMonotoneOnGrid) (he : EndpointValid) :
    ∀ k : Fin 2049, NodeValid (nodeQ RatInterval.piHi 2048 k) (nodeBin k) :=
  fun k => node_valid_of_grid_cap hm he k

end N11Formalization.SevenClassQ0Deg3Bins
#check @N11Formalization.SevenClassQ0Deg3Bins.node_valid_of_grid_cap
#print axioms N11Formalization.SevenClassQ0Deg3Bins.nodeBinAt_mem
