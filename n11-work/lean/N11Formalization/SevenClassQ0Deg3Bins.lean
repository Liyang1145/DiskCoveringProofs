import N11Formalization.MetricAreaRationalCertificate
import N11Formalization.SevenClassQ0Deg3Mono

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
open SevenClassQ0Deg3Mono

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

/-- Rational saturation of the cap at the right end of the grid.  This is the
one remaining rational inequality in the last bin; it is isolated rather than
assumed by the monotonicity theorem below. -/
def PiHiCapSaturated : Prop := capQ RatInterval.piHi = 19 / 50

theorem capQ_piHi_of_upper_one (h : 1 ≤ sinHiNLag (RatInterval.piHi / 2)) :
    PiHiCapSaturated := by
  unfold PiHiCapSaturated capQ
  rw [min_eq_left h, max_eq_right (by norm_num)]
  norm_num

/-- The cap is saturated at `piHi`: the 15-term Taylor upper bracket at
`piHi / 2`, including its positive degree-29 Lagrange remainder, exceeds one.
This is a single denominator-cleared rational comparison, not a grid scan. -/
theorem piHiCapSaturated : PiHiCapSaturated := by
  apply capQ_piHi_of_upper_one
  have hhalf : 0 ≤ RatInterval.piHi / 2 := by norm_num [RatInterval.piHi]
  rw [sinHiNLag, abs_of_nonneg hhalf]
  norm_num [sinTQ, Finset.sum_range_succ, RatInterval.piHi]

/-- Grid monotonicity of `capQ`, conditional only on saturation in the final
bin.  Bins 0--6 lie strictly below `piLo / 2 < Real.pi / 2`; bin 7 is handled
by the universal upper bound `capQ ≤ 19/50`. -/
theorem capMonotoneOnGrid_of_piHiCapSaturated (hsat : PiHiCapSaturated) :
    CapMonotoneOnGrid := by
  intro k
  by_cases h7 : (binIndex k).val = 7
  · have hk7 : binIndex k = ⟨7, by omega⟩ := Fin.ext h7
    have htop : capQ (nodeQ RatInterval.piHi 2048 (binHi (binIndex k))) = 19 / 50 := by
      rw [hk7]
      simpa [PiHiCapSaturated, binHi, nodeQ] using hsat
    rw [htop]
    exact (capQ_bounds (nodeQ RatInterval.piHi 2048 k)).2
  · have hkhi : k.val ≤ (binHi (binIndex k)).val := by
      have hnot : min 7 (k.val / 256) ≠ 7 := by
        simpa [binIndex] using h7
      have hmin : min 7 (k.val / 256) = k.val / 256 := by
        by_cases hle : k.val / 256 ≤ 7
        · exact min_eq_right hle
        · have hlt : 7 < k.val / 256 := by omega
          exact (hnot (min_eq_left hlt.le)).elim
      have hidx : (binIndex k).val = min 7 (k.val / 256) := rfl
      have hbound : k.val ≤ 256 * (binIndex k).val + 255 := by
        rw [hidx, hmin]
        have hmod : k.val % 256 ≤ 255 :=
          Nat.le_of_lt (Nat.mod_lt k.val (n := 256) (by norm_num))
        calc
          k.val = 256 * (k.val / 256) + k.val % 256 :=
            (Nat.div_add_mod k.val 256).symm
          _ ≤ 256 * (k.val / 256) + 255 := Nat.add_le_add_left hmod _
      have hbin : (binHi (binIndex k)).val =
          if (binIndex k).val = 7 then 2048 else 256 * (binIndex k).val + 255 := rfl
      rw [hbin, if_neg h7]
      exact hbound
    have hqle : nodeQ RatInterval.piHi 2048 k ≤
        nodeQ RatInterval.piHi 2048 (binHi (binIndex k)) := by
      unfold nodeQ
      have hkq : (k.val : ℚ) ≤ ((binHi (binIndex k)).val : ℚ) := by
        exact_mod_cast hkhi
      have hpi : 0 ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkq hpi) (by norm_num)
    have hbhi : (binHi (binIndex k)).val ≤ 1791 := by
      have hval : (binHi (binIndex k)).val =
          256 * (binIndex k).val + 255 := by
        simp [binHi, h7]
      rw [hval]
      have hidxlt : (binIndex k).val < 7 := by omega
      omega
    have hnode : nodeQ RatInterval.piHi 2048 (binHi (binIndex k)) ≤
        RatInterval.piHi * 1791 / 2048 := by
      unfold nodeQ
      have hbq : ((binHi (binIndex k)).val : ℚ) ≤ 1791 := by
        exact_mod_cast hbhi
      have hpi : 0 ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbq hpi) (by norm_num)
    have hhalf : nodeQ RatInterval.piHi 2048 (binHi (binIndex k)) / 2 ≤
        RatInterval.piLo / 2 := by
      have hrat : RatInterval.piHi * 1791 / 4096 ≤ RatInterval.piLo / 2 := by
        norm_num [RatInterval.piHi, RatInterval.piLo]
      linarith
    have hb : ((nodeQ RatInterval.piHi 2048 (binHi (binIndex k)) / 2 : ℚ) : ℝ) ≤
        Real.pi / 2 := by
      have hhalfR : ((nodeQ RatInterval.piHi 2048 (binHi (binIndex k)) / 2 : ℚ) : ℝ) ≤
          ((RatInterval.piLo / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hhalf
      exact hhalfR.trans RatInterval.pi_div_two_lo_lt.le
    have ha : 0 ≤ nodeQ RatInterval.piHi 2048 k / 2 := by
      unfold nodeQ
      have hp : 0 ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      positivity
    have hqhalf : nodeQ RatInterval.piHi 2048 k / 2 ≤
        nodeQ RatInterval.piHi 2048 (binHi (binIndex k)) / 2 := by linarith
    exact capQ_mono (sinHiNLag_mono ha hqhalf hb)

/-- Unconditional grid monotonicity of the rational cap. -/
theorem capMonotoneOnGrid : CapMonotoneOnGrid :=
  capMonotoneOnGrid_of_piHiCapSaturated piHiCapSaturated

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
