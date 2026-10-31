import N11Formalization.FrozenCapRationalCore
import Mathlib.Tactic.NormNum

/-! Two-leaf proof-pattern smoke test for generated node-1409 row caps.
Diagnostic only; this does not claim a packet or residual payment. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapRowCap1409Smoke
open N11Formalization.FrozenCapRationalCore
noncomputable section

theorem leaf_0_1 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem leaf_5_4 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

end
end N11Formalization.FrozenCapRowCap1409Smoke
