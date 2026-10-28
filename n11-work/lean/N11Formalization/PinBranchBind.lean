/-
n11-formalization — cline-six-20260930 / source-stress — **unbuilt draft, Lead owns the serial slot**.

# `PinBranchBind` (draft V4, canonical namespace frozen) — branch binding, all gate faults repaired

**Namespace frozen canonical**: this draft declares `namespace N11Formalization.PinBranchBind` (not a
`V3`-suffixed one), so the Lead's canonical copy and every consumer keep the same name.  The file name
stays versioned in `evidence/…/source-stress/` as `PinBranchBindV4.lean`.

Gate-2 faults (log `lead/pin-branch-gate2.log`) also repaired:

* `sub_pinOut` L61/L76: `abel` cannot reconcile the smul coefficients (`-1 • (2 • M)` vs `-2 • M`),
  and the inner-subtraction rewrite is **not** named `sub_sub` in this toolchain — the proof now
  rewrites only with `pinOut_eq` and the doubled midpoint `← hM`, then closes with Mathlib's
  `module` tactic (which handles the scalar coefficients);
* `sameBranch_iff` L126: `pos_of_mul_pos_right` wanted the factors reversed; replaced by
  `nlinarith [hh, h]`.

Gate-1 faults, repaired:

* `pinOut_eq`: the trailing `abel` had **no goals** (the preceding `norm_num` already closed it) —
  removed;
* `sub_pinOut`: `rw [smul_smul]` failed because after `pinOut_eq` there is **no nested smul**; the
  proof now goes through the doubled-midpoint lemma `two_smul_chordMid : 2 • chordMid P Q = P + Q`;
* `Fout_sub_Fin`: the bare `rw [norm_add_sq_real, norm_sub_sq_real]` matched the wrong subterm
  (`H − M` instead of `(A − B)`); now the two instantiations are named (`ha`, `hb`) and rewritten
  explicitly;
* `hinner` (in `Fout_eq_Fin_add_yh` and `sameBranch_iff`): the **degenerate case `U = M`** makes
  `‖U − M‖⁻¹ = 0`, so the cancellation fails; handled by `by_cases` — in the degenerate branch both
  sides vanish, in the other the nonzero norm is cancelled by `field_simp`.

## Level (unchanged)

proved here: the branch-binding algebra in the tree's `Point` (no coordinates, no Fréchet).  Not
proved: the pin-construction relation `h² = R² − a²` (now *paid in general* by `PinHeightPay.lean`),
the root-side `F_out > 0`, `y > 0`, and the circumradius identity.  No sorry, no custom axiom, no
`native_decide`.
-/

import Mathlib
import N11Formalization.ResumeNetwork
import N11Formalization.ResumeLocalIncidence

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.PinBranchBind

open N11Formalization

noncomputable section

/-- The chord midpoint `M = (P + Q)/2`. -/
def chordMid (P Q : Point) : Point := (2 : ℝ)⁻¹ • (P + Q)

/-- The **outer** circle point on the same perpendicular: `U_out = 2M − U`. -/
def pinOut (P Q U : Point) : Point := (2 : ℝ) • chordMid P Q - U

/-- `2 • chordMid P Q = P + Q` (the doubled midpoint). -/
theorem two_smul_chordMid (P Q : Point) : (2 : ℝ) • chordMid P Q = P + Q := by
  unfold chordMid
  rw [smul_smul]
  norm_num

/-- `U_out = P + Q − U` (so `U_out − M = −(U − M)`). -/
theorem pinOut_eq (P Q U : Point) : pinOut P Q U = P + Q - U := by
  unfold pinOut chordMid
  rw [smul_smul]
  norm_num

/-- `H − U_out = (H − M) + (U − M)`.

`abel` cannot reconcile the smul coefficients (`-1 • (2 • M)` vs `-2 • M`), and the inner-subtraction
lemma is not named `sub_sub` here; the most robust route is to rewrite only with `pinOut_eq` and the
doubled midpoint, and let Mathlib's `module` tactic handle the scalar coefficients. -/
theorem sub_pinOut (P Q U H : Point) :
    H - pinOut P Q U = (H - chordMid P Q) + (U - chordMid P Q) := by
  have hM := two_smul_chordMid P Q
  rw [pinOut_eq, ← hM]
  module

/-- `H − U = (H − M) − (U − M)`. -/
theorem sub_pin (P Q U H : Point) :
    H - U = (H - chordMid P Q) - (U - chordMid P Q) := by
  abel

/-- **The coordinate-free branch identity**: the outer residual exceeds the inner one by
`4 ⟪H − M, U − M⟫`. -/
theorem Fout_sub_Fin (P Q U H : Point) :
    ‖H - pinOut P Q U‖ ^ 2 - ‖H - U‖ ^ 2
      = 4 * inner ℝ (H - chordMid P Q) (U - chordMid P Q) := by
  have hout := sub_pinOut P Q U H
  have hin := sub_pin P Q U H
  have ha := norm_add_sq_real (H - chordMid P Q) (U - chordMid P Q)
  have hb := norm_sub_sq_real (H - chordMid P Q) (U - chordMid P Q)
  rw [hout, hin, ha, hb]
  ring

/-- The pin's unit normal `n = (U − M)/‖U − M‖`. -/
def pinNormal (P Q U : Point) : Point := (‖U - chordMid P Q‖)⁻¹ • (U - chordMid P Q)

/-- The pin height `h = ‖U − M‖` (nonnegative by construction). -/
def pinHeight (P Q U : Point) : ℝ := ‖U - chordMid P Q‖

/-- The **signed** hub coordinate `y = ⟪H − M, n⟫` along the pin normal. -/
def hubCoord (P Q U H : Point) : ℝ := inner ℝ (H - chordMid P Q) (pinNormal P Q U)

/-- `h² = ⟪U − M, U − M⟫` — the height is the norm, squared. -/
theorem pinHeight_sq (P Q U : Point) :
    pinHeight P Q U ^ 2 = inner ℝ (U - chordMid P Q) (U - chordMid P Q) := by
  rw [pinHeight, real_inner_self_eq_norm_sq]

/-- **The pull-back identity** `⟪H − M, U − M⟫ = y · h`, valid also in the degenerate case
`U = M` (where both sides vanish). -/
theorem inner_eq_hubCoord_mul_pinHeight (P Q U H : Point) :
    inner ℝ (H - chordMid P Q) (U - chordMid P Q) = hubCoord P Q U H * pinHeight P Q U := by
  by_cases hv : U - chordMid P Q = 0
  · simp [hubCoord, pinNormal, pinHeight, hv]
  · have hnorm : ‖U - chordMid P Q‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact hv
    unfold hubCoord pinNormal pinHeight
    rw [real_inner_smul_right]
    field_simp

/-- **The branch binding**: `F_out = Fin + 4 y h` in the tree's own `Point` (no coordinates). -/
theorem Fout_eq_Fin_add_yh (P Q U H : Point) (R : ℝ) :
    ‖H - pinOut P Q U‖ ^ 2 - R ^ 2
      = (‖H - U‖ ^ 2 - R ^ 2) + 4 * hubCoord P Q U H * pinHeight P Q U := by
  have hinner := inner_eq_hubCoord_mul_pinHeight P Q U H
  have h := Fout_sub_Fin P Q U H
  rw [hinner] at h
  linarith

/-- **Same branch ⟺ `y > 0`**: the hub lies on the pin's side of the chord exactly when the signed
coordinate is positive. -/
theorem sameBranch_iff (P Q U H : Point) (hh : 0 < pinHeight P Q U) :
    0 < hubCoord P Q U H ↔ 0 < inner ℝ (H - chordMid P Q) (U - chordMid P Q) := by
  have hinner := inner_eq_hubCoord_mul_pinHeight P Q U H
  rw [hinner]
  constructor
  · intro hy; exact mul_pos hy hh
  · intro h; nlinarith [hh, h]

end

end N11Formalization.PinBranchBind

#print axioms N11Formalization.PinBranchBind.two_smul_chordMid
#print axioms N11Formalization.PinBranchBind.pinOut_eq
#print axioms N11Formalization.PinBranchBind.sub_pinOut
#print axioms N11Formalization.PinBranchBind.Fout_sub_Fin
#print axioms N11Formalization.PinBranchBind.inner_eq_hubCoord_mul_pinHeight
#print axioms N11Formalization.PinBranchBind.Fout_eq_Fin_add_yh
#print axioms N11Formalization.PinBranchBind.sameBranch_iff
