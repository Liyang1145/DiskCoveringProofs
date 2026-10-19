/- Rational bookkeeping for the WIP nine-switch batch (SharedMomentConcreteSwitchBatch.lean,
   `start0_switch{0..8}_bound`, `start0_switch_total_bound`). Core Lean, values transcribed.
   This is NOT the missing aggregation/bridge theorem (that needs the Mathlib
   `FiniteCanonicalCertificate.switches` structure); it only fixes the arithmetic it must use. -/
namespace DCPN11Core.SwitchArith
def bounds : List Rat :=
  [141/1000000, 7/50000, 141/1000000, 141/1000000, 51029/1000000, 4839/200000,
   141/1000000, 141/1000000, 14023/1000000]
def totalBound : Rat := 22523/250000
/-- The nine per-switch bounds sum EXACTLY to `start0_switch_total_bound`. -/
theorem sum_eq_total : bounds.foldl (· + ·) 0 = totalBound := by decide +kernel
/-- Against the LeafControls threshold 1/2000: switches 0,1,2,3,6,7 are below it; 4,5,8 are not. -/
theorem leafControls_pattern :
    bounds.map (fun b => decide (b ≤ 1/2000)) =
      [true, true, true, true, false, false, true, true, false] := by decide +kernel
/-- 141/1000000 (SwitchBatch's small bound) is strictly below 1/2000. -/
theorem small_lt_leafControls : (141/1000000 : Rat) < 1/2000 := by decide +kernel
end DCPN11Core.SwitchArith
