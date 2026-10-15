/-
n11-formalization — cline-six-20260930 / source-stress — **unbuilt draft, Lead owns the serial slot**.

# `MuRootPositive` — the real-root multiplier positivity, split out (no auxiliary sum)

Per Lead direction: the μ-positivity obligation is sorry-free and does **not** depend on the
orbit-split total, so it is gated as its own file; the auxiliary `sum_muContact` no longer blocks it.

## What this file proves (all from already-green tree material)

* `boxHiCert_multiplier_neg` — the five multiplier slots' certificate-box upper bounds are negative
  (`BoxRstar.lean` L122–134: `−550469521295681015851371/2^82`, …); `fin_cases` + `norm_num`, no new
  interval computation;
* `last5_lt_zero` — `last5 sourceRoot i < 0` for `i : Fin 5`, by the box bound and `sourceRoot_mem`
  (`SourceExactRoot.lean`); `last5` is `N11Formalization.last5` (`TCSystem.lean` L125);
* `muOrbitRoot_pos` — `μ_i = −λ_i > 0` at the actual root (the `hμ` hypothesis is **gone**);
* `musoContactRoot_pos`, `faceWeightRoot_nonneg` — the α-interface's face factor hypothesis at the
  actual root, with only `0 ≤ c a` (the geometric conversion factors) left as input;
* the source-bound tables `ORBIT`/`OSZ` (`phase7` L164–165) with the finite consistency
  `orbit_card` (one `decide`) and `osz_pos`.

## Source binding (verbatim, read 2026-10-01)

`team-current/r20-stress/phase7_interval_cyclic_nu.py` (sha256
`3F810D0BD2143054BD7A6E87FFA6D617B84BC5A0C7CA9E7D49E2EB091C321236`) L164–166, L208:

```
ORBIT = {0: 0, 1: 0, 2: 1, 3: 1, 4: 2, 5: 2, 6: 3, 7: 4, 8: 4}   # contact index -> mu index
OSZ = {0: 2, 1: 2, 2: 2, 3: 1, 4: 2}                            # orbit size of each mu index
MU = [-lam[i] for i in range(5)]                                # mu_i = -lambda_i, straight from the box
...
    mu_c = MU[ORBIT[idx]] / OSZ[ORBIT[idx]]
```

## What remains (not claimed here)

The conversion factors `c_a > 0`, `b_j > 0` (geometry / C897 interval); the ν side
(`SourceNuCycleV10.lean`); the normalization `Σ(μc) + Σ(νb) = 1` (R-component of stationarity); the
orbit-split total (`MuOrbitSum.lean`, auxiliary).
-/

import Mathlib
import N11Formalization.SourceExactRoot
import N11Formalization.TCSystem

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.MuRootPositive

open N11Formalization

noncomputable section

/-- Source `ORBIT` (`phase7` L164): contact slot `↦` multiplier orbit index. -/
def ORBIT (a : Fin 9) : Fin 5 :=
  if a.val = 0 ∨ a.val = 1 then 0
  else if a.val = 2 ∨ a.val = 3 then 1
  else if a.val = 4 ∨ a.val = 5 then 2
  else if a.val = 6 then 3
  else 4

/-- Source `OSZ` (`phase7` L165): orbit size of each multiplier index. -/
def OSZ (i : Fin 5) : ℕ :=
  if i.val = 3 then 1 else 2

/-- **Finite consistency of the two tables**: every orbit has exactly `OSZ i` contacts. -/
theorem orbit_card (i : Fin 5) :
    (Finset.univ.filter (fun a : Fin 9 => ORBIT a = i)).card = OSZ i := by
  fin_cases i <;> decide

/-- The orbit sizes are positive. -/
theorem osz_pos (i : Fin 5) : (0 : ℝ) < (OSZ i : ℝ) := by
  fin_cases i <;> norm_num [OSZ]

/-- The source's `MU = [-lam[i] for i in range(5)]`. -/
def muOrbit (u : Fin 12 → ℝ) (i : Fin 5) : ℝ := -(last5 u i)

/-- The source's split rule `mu_c = MU[ORBIT[idx]] / OSZ[ORBIT[idx]]` (`phase7` L208). -/
def muContact (u : Fin 12 → ℝ) (a : Fin 9) : ℝ := muOrbit u (ORBIT a) / (OSZ (ORBIT a) : ℝ)

/-- The actual root's five orbit-representative multipliers. -/
def muOrbitRoot (i : Fin 5) : ℝ := muOrbit SourceExactRoot.sourceRoot i

/-- The actual root's nine contact multipliers. -/
def muContactRoot (a : Fin 9) : ℝ := muContact SourceExactRoot.sourceRoot a

/-- **The five multiplier slots' box upper bounds are negative** (certificate-box rationals, no new
interval arithmetic). -/
theorem boxHiCert_multiplier_neg (i : Fin 5) :
    (boxHiCert ⟨(i : ℕ) + 7, by omega⟩ : ℝ) < 0 := by
  fin_cases i <;> norm_num [boxHiCert]

/-- **`λ_i < 0` at the actual root**, from `sourceRoot_mem` and the box bounds. -/
theorem last5_lt_zero (i : Fin 5) : last5 SourceExactRoot.sourceRoot i < 0 := by
  have hmem := (SourceExactRoot.sourceRoot_mem).1 ⟨(i : ℕ) + 7, by omega⟩
  have hhi := boxHiCert_multiplier_neg i
  have heq : last5 SourceExactRoot.sourceRoot i
      = SourceExactRoot.sourceRoot ⟨(i : ℕ) + 7, by omega⟩ := by
    simp only [last5]
  rw [heq]
  exact lt_of_le_of_lt hmem.2 hhi

/-- **`μ_i = −λ_i > 0` at the actual root** (the `hμ` premise is gone). -/
theorem muOrbitRoot_pos (i : Fin 5) : 0 < muOrbitRoot i := by
  unfold muOrbitRoot muOrbit
  have h := last5_lt_zero i
  linarith

/-- **Every contact multiplier is positive at the actual root.** -/
theorem muContactRoot_pos (a : Fin 9) : 0 < muContactRoot a := by
  unfold muContactRoot muContact
  exact div_pos (muOrbitRoot_pos (ORBIT a)) (osz_pos (ORBIT a))

/-- **Nonnegativity of a contact multiplier** for a general `u`, from orbit nonnegativity. -/
theorem muContact_nonneg_of (u : Fin 12 → ℝ) (hμ : ∀ i : Fin 5, 0 ≤ muOrbit u i) (a : Fin 9) :
    0 ≤ muContact u a :=
  div_nonneg (hμ (ORBIT a)) (le_of_lt (osz_pos (ORBIT a)))

/-- **Premise eliminated (face block).**  At the actual root the α-interface's face factor
hypothesis holds with **no hypothesis on the multipliers**; only `0 ≤ c a` remains. -/
theorem faceWeightRoot_nonneg (c : Fin 9 → ℝ) (hc : ∀ a : Fin 9, 0 ≤ c a) :
    ∀ a : Fin 9, 0 ≤ muContactRoot a * c a :=
  fun a => mul_nonneg (le_of_lt (muContactRoot_pos a)) (hc a)

end

end N11Formalization.MuRootPositive

#print axioms N11Formalization.MuRootPositive.orbit_card
#print axioms N11Formalization.MuRootPositive.osz_pos
#print axioms N11Formalization.MuRootPositive.boxHiCert_multiplier_neg
#print axioms N11Formalization.MuRootPositive.last5_lt_zero
#print axioms N11Formalization.MuRootPositive.muOrbitRoot_pos
#print axioms N11Formalization.MuRootPositive.muContactRoot_pos
#print axioms N11Formalization.MuRootPositive.faceWeightRoot_nonneg
