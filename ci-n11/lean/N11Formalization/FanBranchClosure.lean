/-
n11-formalization — cline-six-20260930 / source-stress — **unbuilt draft, Lead owns the serial slot**.

# `FanBranchClosure` — the branch binding instantiated at the **actual TC fan data**

`Height6` is GREEN (canonical `PinHeightPay`, namespace `PinHeightPayV6`); the generic branch binding
(`PinBranchBind`, canonical namespace) is GREEN.  This file closes the loop on the actual tree objects,
and does **not** import the height file (the height is already paid there):

* `fan_pinOut_eq_arcEnd`: `pinOut (C_k) (C_{k+1}) (Uvec u k) = arcEnd u k` — the tree's `arcEnd` is
  **exactly the outer circle point** of the fan contact (the internal intersection is `Uvec`).  This is
  the checkable form of the Lead's mapping correction.
* `fan_Fout_eq`: the **actual** branch binding — with `P = C_k`, `Q = C_{k+1}`, `U = Uvec u k` (the TC
  pin), `R = u 6` (the radius coordinate) and any hub `Hub` (in `TCSystem.residual` the hubs are
  `hub0 u`, `hub1 u`):
  `‖Hub − arcEnd u k‖² − R² = (‖Hub − Uvec u k‖² − R²) + 4·y·h`.
* `squared_sub_sq_factor`: `‖H − U‖² − R² = (dist H U + R)·(dist H U − R)` — the bridge from the
  **squared** chain (`GradFactorChainV3`, `[S]`) to the actual TC's **length** residual
  (`TCSystem.residual` L96–100, `[L]`).
* `fan_residual_zero_data`: at the root (`dist = u 6`) the squared residual vanishes.

## Level (honest)

proved here: the instantiation at the tree objects and the squared↔length factorization.
**Still a premise, not paid**: `F_out > 0` at the source root (`[I]` external interval artefact only);
`y > 0` (same branch); and the actual-TC stationarity → `sourceB2` row.  No sorry, no custom axiom, no
`native_decide`.
-/

import Mathlib
import N11Formalization.PinBranchBind
import N11Formalization.TCSystem

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.FanBranchClosure

open N11Formalization
open N11Formalization.PinBranchBind

noncomputable section

/-- **The fan contact's outer point is the tree's `arcEnd`**: `pinOut (C_k) (C_{k+1}) (Uvec u k)`
equals `arcEnd u k`, i.e. the TC's `Uvec` is the internal intersection and `arcEnd` the opposite one. -/
theorem fan_pinOut_eq_arcEnd (u : Fin 12 → ℝ) (k : Fin 9) :
    pinOut (ringCenter u k) (ringCenter u (k + 1)) (Uvec u k) = arcEnd u k := by
  rw [pinOut_eq]
  unfold Uvec
  module

/-- **The fan branch binding at the actual TC data.**  With `R = u 6`:
`‖Hub − arcEnd u k‖² − R² = (‖Hub − Uvec u k‖² − R²) + 4 y h`, i.e. the outer residual exceeds the
TC's squared residual by `4 y h` (and equals it exactly when `y = 0`). -/
theorem fan_Fout_eq (u : Fin 12 → ℝ) (k : Fin 9) (Hub : Point) :
    ‖Hub - arcEnd u k‖ ^ 2 - (u 6) ^ 2
      = (‖Hub - Uvec u k‖ ^ 2 - (u 6) ^ 2)
        + 4 * hubCoord (ringCenter u k) (ringCenter u (k + 1)) (Uvec u k) Hub
            * pinHeight (ringCenter u k) (ringCenter u (k + 1)) (Uvec u k) := by
  have h := Fout_eq_Fin_add_yh (ringCenter u k) (ringCenter u (k + 1)) (Uvec u k) Hub (u 6)
  rwa [fan_pinOut_eq_arcEnd u k] at h

/-- **The squared residual factors through the length residual** (the `[S]`→`[L]` bridge):
`‖H − U‖² − R² = (dist H U + R)·(dist H U − R)` — no sign hypothesis. -/
theorem squared_sub_sq_factor (H U : Point) (R : ℝ) :
    ‖H - U‖ ^ 2 - R ^ 2 = (dist H U + R) * (dist H U - R) := by
  rw [dist_eq_norm]
  ring

/-- **At the actual root the fan's squared residual vanishes** as soon as the TC length residual does
(`dist Hub (Uvec u k) = u 6`, which is `TCSystem.residual`'s first four coordinates being zero). -/
theorem fan_residual_zero_data (u : Fin 12 → ℝ) (k : Fin 9) (Hub : Point)
    (hres : dist Hub (Uvec u k) = u 6) :
    ‖Hub - Uvec u k‖ ^ 2 - (u 6) ^ 2 = 0 := by
  rw [dist_eq_norm] at hres
  rw [hres]
  ring

/-- **Length form at the root**: with `dist = R` the outer residual is `F_out = 4 y h`, i.e. the
source's printed length-convention factor is `4y²/F_out = y/h` (see `LengthResidualWrapperV2`). -/
theorem fan_Fout_eq_four_yh (u : Fin 12 → ℝ) (k : Fin 9) (Hub : Point)
    (hres : dist Hub (Uvec u k) = u 6) :
    ‖Hub - arcEnd u k‖ ^ 2 - (u 6) ^ 2
      = 4 * hubCoord (ringCenter u k) (ringCenter u (k + 1)) (Uvec u k) Hub
          * pinHeight (ringCenter u k) (ringCenter u (k + 1)) (Uvec u k) := by
  rw [fan_Fout_eq u k Hub, fan_residual_zero_data u k Hub hres]
  ring

end

end N11Formalization.FanBranchClosure

#print axioms N11Formalization.FanBranchClosure.fan_pinOut_eq_arcEnd
#print axioms N11Formalization.FanBranchClosure.fan_Fout_eq
#print axioms N11Formalization.FanBranchClosure.squared_sub_sq_factor
#print axioms N11Formalization.FanBranchClosure.fan_residual_zero_data
#print axioms N11Formalization.FanBranchClosure.fan_Fout_eq_four_yh
