/-
DSHPatchTemplateK5.lean -- DSH-PATCH-T0: FULL-INTERFACE CLOSED-LOOP TEMPLATE for ONE sharp patch.

Patch chosen: cluster k=5 of the 16-cluster patch-union cover = patch cells [4935, 4957]
(the two tightest cells), source `cosine_dbm_local920.json`
sha256 6706b42690a1d99d8f49523ff0d7d82fbc688fd64a18b228512acec139aef987.
This patch already carries the most paid prerequisites (its containment layer is
root-integrated via `N11Formalization.Patch120K5Actual`).

FOUR LAYERS, each named explicitly below:
  L1 `CellDomain`            -- the ACTUAL cell geometry domain (12-variable root box
                                `RootRangeBoxFull.InCertBox` + the ACTUAL emitted DBM tree
                                cell rows for cell 4935 or 4957).  No generic-position or
                                symmetry restriction is introduced.
  L2 `containment_*`         -- interval containment with kernel-sound constants: the
                                pinned perturbation sum-of-squares lies in the FROZEN ball
                                q2 <= (729/50000)^2, q <= 729/50000 (exact rationals).
  L3 `mixed_remainder_completion` + `sharp_scalar_gain` + `sharp_gain_of_cell`
                             -- the SHARP energy/lower inequality.  The mixed remainder
                                gets its OWN argument: an exact square-completion IDENTITY
                                with the actual constants (t = 734, K = (99/200)(2/25)+429/50000,
                                C = 179/5000, d/3 = (2/25)/3, mu/2 = 9/10000).  The consumer
                                shape `sharp_gain_of_cell` is CONDITIONAL: its two remaining
                                premises are typed and labelled (see below).
  L4 `patch_gain_energy_slack`
                             -- the patch result applied, in this module, in the exact shape
                                of the upstream energy comparison
                                `q^2/100000 <= V2 (U + disp theta x) - Rstar^2`
                                (real `V2` from `ResumeNetwork`, real `disp` from
                                `FlashLocal`), consumed through the REAL upstream consumer
                                `ResumeCoercivityCertificate.directional_to_local_gain`.

UNITS (checked verbatim): `q2 u y = sum of 8 squares` is SQUARED (length^2-like);
`q u y = Real.sqrt (q2 u y)` is NOT squared; L2 bounds `q` by 729/50000 (non-squared) and
`q2` by (729/50000)^2 (squared); L3/L4 conclude in SQUARED units `q^2/100000 <= E`.
`q_sq_eq_q2` records the exact conversion.

UNPAID / CONDITIONAL premises of `sharp_gain_of_cell` and `patch_gain_energy_slack`
(typed, NOT advertised as unconditional):
  * `hc`   : the mu-coercivity slot `(9/5000) q^2 <= H + 1468 p^2`.
             UNPAID.  It is the output shape of `ResumePinnedCoercivity.pinned_coercivity`
             (congruence dominance on the pinned quotient) instantiated on the ACTUAL
             interval H/G boxes via `ResumeIntervalAugmented.coercivity_of_boxes`.
             The actual N/H interval enclosure is NOT paid anywhere in this project.
  * `hdir` : the actual C920 directional inequality.  UNPAID.  It is the output shape of
             `FlashLocal.directional_lower_actual`, which itself is still conditional on
             `hCcross`, `hfluxAlpha`, `hfDelta`, `hrho`, `hresp` (actual source N/H rows).
No `sorry`, no custom axiom, no `native_decide`, no heartbeat raise in this file.

Scope labels: local[cell 4935/4957 of cluster k=5] / standalone (this module) /
conditional (the two premises above) / consumer = `directional_to_local_gain`.
-/
import N11Formalization.Patch120K5Actual
import N11Formalization.ResumeCoercivityCertificate
import N11Formalization.ResumeNetwork
import N11Formalization.FlashLocalDirectionalBase

set_option autoImplicit false
set_option maxRecDepth 10000

namespace N11Formalization.DSHPatchTemplate.K5

open Finset
open N11Formalization
open N11Formalization.FlashLeafSplit
open N11Formalization.Patch120K5
open N11Formalization.Patch120K5Actual
open N11Formalization.ResumeRelativeScalar

noncomputable section

/-! ## L1. the ACTUAL patch-cell geometry domain -/

/-- **L1.** The actual geometric domain of patch cells 4935 / 4957 of cluster k=5:
the 12-variable root box `RootRangeBoxFull.InCertBox u` together with the ACTUAL emitted
DBM tree cell `Cell (matrix DBMSourceTree.data 4096 c) (tlift y)` for `c = 4935` or `c = 4957`.
The two cells are exactly the two tightest cells of the cluster; no extra hypothesis
(repeated / degenerate / outside centre) is imposed and no symmetry is assumed. -/
def CellDomain (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) : Prop :=
  RootRangeBoxFull.InCertBox u ∧
    (Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (4935 : Fin 5011)) (tlift y) ∨
     Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (4957 : Fin 5011)) (tlift y))

/-- L1 exposes the two cells of the cluster as the domain (no third cell, no symmetry class). -/
theorem cellDomain_iff {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} :
    CellDomain u y ↔
      RootRangeBoxFull.InCertBox u ∧
        (Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (4935 : Fin 5011)) (tlift y) ∨
         Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (4957 : Fin 5011)) (tlift y)) :=
  Iff.rfl

/-! ## L2. interval containment with kernel-sound constants -/

/-- `q2` is a sum of 8 squares: nonnegative. -/
theorem q2_nonneg (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) : 0 ≤ q2 u y := by
  unfold q2
  positivity

/-- `q = sqrt q2` is nonnegative (non-squared units). -/
theorem q_nonneg (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) : 0 ≤ q u y := Real.sqrt_nonneg _

/-- **units check, verbatim**: the squared quantity `q^2` is exactly the sum of squares `q2`. -/
theorem q_sq_eq_q2 (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) : (q u y) ^ 2 = q2 u y := by
  unfold q
  exact Real.sq_sqrt (q2_nonneg u y)

/-- **L2 (squared units).** On the actual patch-cell domain the pinned perturbation
sum-of-squares lies in the frozen ball of radius `729/50000`.  Exact rational constant;
proved from the kernel-checked cluster hull and the emitted tree rows (no float, no
sampling, no C911 pair-weight table). -/
theorem containment_sq_of_domain {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} (h : CellDomain u y) :
    q2 u y ≤ (729 / 50000 : ℝ) ^ 2 := by
  rcases h with ⟨hu, hc | hc⟩
  · exact Patch120K5Actual.q2_le_4935 hu hc
  · exact Patch120K5Actual.q2_le_4957 hu hc

/-- **L2 (non-squared units).** Same containment read in the non-squared coordinate
`q = sqrt q2`; this is exactly the `hr` slot of the scalar gain consumers. -/
theorem containment_nonsq_of_domain {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} (h : CellDomain u y) :
    q u y ≤ (729 / 50000 : ℝ) := by
  rcases h with ⟨hu, hc | hc⟩
  · exact Patch120K5Actual.q_le hu (Or.inl hc)
  · exact Patch120K5Actual.q_le hu (Or.inr hc)

/-! ## L3. the SHARP energy / lower inequality -/

/-- The mixed coefficient constant of the actual C920 directional remainder
(`B*d + A` with `B = 99/200`, `d = 2/25`, `A = 429/50000`). -/
def K5mixed : ℝ := (99 / 200) * (2 / 25) + 429 / 50000

theorem K5mixed_eq : K5mixed = 2409 / 50000 := by norm_num [K5mixed]

/-- **L3-a (the mixed remainder's OWN argument, proved unconditionally).**
Exact square-completion IDENTITY: with the ACTUAL constants, the mixed term
`-1468 * K * p * q^2` is *exactly* the square `734 (p - K q^2)^2` minus the
absorbed quartic `734 K^2 q^4`.  Hence the mixed block needs no separate positivity
premise -- it is an identity, not an inequality, and separate-block positivity is
neither used nor sufficient (see the negative control in the companion probe file). -/
theorem mixed_remainder_completion (q p : ℝ) :
    (9 / 10000 : ℝ) * q ^ 2 + 734 * p ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4
        - 1468 * ((99 / 200) * (2 / 25) + 429 / 50000) * p * q ^ 2
      = (coefficient q) * q ^ 2 + 734 * (p - ((99 / 200) * (2 / 25) + 429 / 50000) * q ^ 2) ^ 2 := by
  unfold coefficient
  ring

/-- The same identity stated with the named mixed constant. -/
theorem mixed_remainder_completion' (q p : ℝ) :
    (9 / 10000 : ℝ) * q ^ 2 + 734 * p ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4
        - 1468 * K5mixed * p * q ^ 2
      = (coefficient q) * q ^ 2 + 734 * (p - K5mixed * q ^ 2) ^ 2 := by
  unfold coefficient K5mixed
  ring

/-- **L3-b.** The sharp coefficient gate at the FROZEN radius: for `q` in the containment
interval the C920 coefficient still beats `1/100000`.  (Kernel-sound exact rationals; this is
`ResumeRelativeScalar.coefficient_gt`, re-exposed as the L3 kernel of this patch.) -/
theorem sharp_coefficient_gate {q : ℝ} (hq : 0 ≤ q) (hr : q ≤ 729 / 50000) :
    (1 / 100000 : ℝ) < coefficient q :=
  coefficient_gt hq hr

/-- **L3-c (sharp scalar inequality, unconditional in `(q,p)`).** Any `(q,p)` with `q` inside
the frozen containment interval satisfies the SHARP gain against the actual mixed remainder
form: `q^2/100000 <= E` whenever the mixed form is `<= E`.  Squared units. -/
theorem sharp_scalar_gain {E q p : ℝ} (hq : 0 ≤ q) (hr : q ≤ 729 / 50000)
    (h : (9 / 10000 : ℝ) * q ^ 2 + 734 * p ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4
      - 1468 * ((99 / 200) * (2 / 25) + 429 / 50000) * p * q ^ 2 ≤ E) :
    q ^ 2 / 100000 ≤ E :=
  ResumeRelativeScalar.local_gain hq hr h

/-- **L3-d (SHARP PATCH INEQUALITY, CONDITIONAL).** The patch sharp gain for the actual
cell domain, through the REAL mu-coercivity consumer
`ResumeCoercivityCertificate.directional_to_local_gain`.

The two premises are CONDITIONAL and typed verbatim; neither is paid anywhere:
  * `hc`   : `(9/5000) q^2 <= H + 1468 p^2`  -- the actual pinned mu-coercivity slot;
  * `hdir` : the actual C920 directional inequality with the actual mixed coefficient
             `1468 * ((99/200)*(2/25) + 429/50000)`.
If either is unavailable the theorem is a conditional statement, NOT an unconditional
sharp lower bound. -/
theorem sharp_gain_of_cell {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} (h : CellDomain u y)
    {E H p : ℝ}
    (hc : (9 / 5000 : ℝ) * (q u y) ^ 2 ≤ H + 1468 * p ^ 2)
    (hdir : H / 2 + 1468 * p ^ 2 - (179 / 5000) * (q u y) ^ 3 - ((2 / 25) / 3) * (q u y) ^ 4
      - 1468 * ((99 / 200) * (2 / 25) + 429 / 50000) * p * (q u y) ^ 2 ≤ E) :
    (q u y) ^ 2 / 100000 ≤ E :=
  ResumeCoercivityCertificate.directional_to_local_gain E H (q u y) p
    (q_nonneg u y) (containment_nonsq_of_domain h) hc hdir

/-- The squared-unit form of L3-d, using the L2 squared containment and the units identity. -/
theorem sharp_gain_of_cell_sq {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} (h : CellDomain u y)
    {E H p : ℝ}
    (hc : (9 / 5000 : ℝ) * (q u y) ^ 2 ≤ H + 1468 * p ^ 2)
    (hdir : H / 2 + 1468 * p ^ 2 - (179 / 5000) * (q u y) ^ 3 - ((2 / 25) / 3) * (q u y) ^ 4
      - 1468 * ((99 / 200) * (2 / 25) + 429 / 50000) * p * (q u y) ^ 2 ≤ E) :
    q2 u y / 100000 ≤ E := by
  rw [← q_sq_eq_q2 u y]
  exact sharp_gain_of_cell h hc hdir

/-! ## L4. the actual upstream consumer application -/

/-- **L4.** The patch result applied, in this module, in the exact shape of the upstream
energy comparison: the gain is measured against the real energy slack
`V2 (U + disp theta x) - Rstar^2` (`V2` from `ResumeNetwork`, `disp` from `FlashLocal`).
This is the conclusion that the root-integrated FlashLocal/Frobenius gain chain feeds on;
the scalar consumer `directional_to_local_gain` is the same real upstream consumer used by
`FlashLocal.local_gain_actual_frobenius`.  Conditional on the same two typed premises. -/
theorem patch_gain_energy_slack {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} (h : CellDomain u y)
    {H p Rstar : ℝ} {U : Fin 9 → Point} (θ x : Fin 9 → ℝ)
    (hc : (9 / 5000 : ℝ) * (q u y) ^ 2 ≤ H + 1468 * p ^ 2)
    (hdir : H / 2 + 1468 * p ^ 2 - (179 / 5000) * (q u y) ^ 3 - ((2 / 25) / 3) * (q u y) ^ 4
      - 1468 * ((99 / 200) * (2 / 25) + 429 / 50000) * p * (q u y) ^ 2
        ≤ ResumeNetwork.V2 (U + FlashLocal.disp θ x) - Rstar ^ 2) :
    (q u y) ^ 2 / 100000 ≤ ResumeNetwork.V2 (U + FlashLocal.disp θ x) - Rstar ^ 2 :=
  sharp_gain_of_cell h hc hdir

/-- **L4 interface (typed, CONDITIONAL).** The patch's L2 containment IS the `hr` slot type of
the real harmonic-leaf consumer `FlashLocal.local_gain_actual_frobenius_leaf_all_box`
(`Real.sqrt (sum i, x i ^ 2) <= 729/50000`), once the GAUGE BRIDGE identifies the patch's
pinned norm `q u y` with the leaf perturbation norm.  The bridge `hbridge` is NOT paid: it
needs the pin plus the gauge rotation `omega = theta_6(y) - theta*_6`, discharged upstream by
`ResumeNetworkIsometry.oracle_isometry` (`V2 (f . U) = V2 U` for a distance-preserving
bijection).  This theorem only types that interface; it is not a proof of the bridge. -/
theorem patch_supplies_leaf_hr_slot {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} (h : CellDomain u y)
    {x : Fin 9 → ℝ} (hbridge : q u y = Real.sqrt (∑ i, x i ^ 2)) :
    Real.sqrt (∑ i, x i ^ 2) ≤ (729 / 50000 : ℝ) := by
  rw [← hbridge]
  exact containment_nonsq_of_domain h

end

end N11Formalization.DSHPatchTemplate.K5

/-! ## Verbatim full types and axiom portraits (for the evidence log) -/

#check @N11Formalization.DSHPatchTemplate.K5.CellDomain
#check @N11Formalization.DSHPatchTemplate.K5.q_sq_eq_q2
#check @N11Formalization.DSHPatchTemplate.K5.containment_sq_of_domain
#check @N11Formalization.DSHPatchTemplate.K5.containment_nonsq_of_domain
#check @N11Formalization.DSHPatchTemplate.K5.mixed_remainder_completion
#check @N11Formalization.DSHPatchTemplate.K5.sharp_coefficient_gate
#check @N11Formalization.DSHPatchTemplate.K5.sharp_scalar_gain
#check @N11Formalization.DSHPatchTemplate.K5.sharp_gain_of_cell
#check @N11Formalization.DSHPatchTemplate.K5.sharp_gain_of_cell_sq
#check @N11Formalization.DSHPatchTemplate.K5.patch_gain_energy_slack
#check @N11Formalization.DSHPatchTemplate.K5.patch_supplies_leaf_hr_slot
#print axioms N11Formalization.DSHPatchTemplate.K5.q2_nonneg
#print axioms N11Formalization.DSHPatchTemplate.K5.q_sq_eq_q2
#print axioms N11Formalization.DSHPatchTemplate.K5.containment_sq_of_domain
#print axioms N11Formalization.DSHPatchTemplate.K5.containment_nonsq_of_domain
#print axioms N11Formalization.DSHPatchTemplate.K5.mixed_remainder_completion
#print axioms N11Formalization.DSHPatchTemplate.K5.mixed_remainder_completion'
#print axioms N11Formalization.DSHPatchTemplate.K5.sharp_coefficient_gate
#print axioms N11Formalization.DSHPatchTemplate.K5.sharp_scalar_gain
#print axioms N11Formalization.DSHPatchTemplate.K5.sharp_gain_of_cell
#print axioms N11Formalization.DSHPatchTemplate.K5.sharp_gain_of_cell_sq
#print axioms N11Formalization.DSHPatchTemplate.K5.patch_gain_energy_slack
#print axioms N11Formalization.DSHPatchTemplate.K5.patch_supplies_leaf_hr_slot
