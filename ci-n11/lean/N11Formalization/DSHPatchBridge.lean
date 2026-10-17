/-
DSHPatchBridge.lean -- DSH-PATCH-BRIDGE: the gauge bridge from patch q-containment to the
pinned displacement norm `√(Σ i, x i²)`, in the shape that pays ALL 120 cells at once.

PROBLEM THIS FILE SOLVES.  The root-imported harmonic-leaf consumer
`FlashLocal.local_gain_actual_frobenius_leaf_all_box` takes as its 7th premise

    hr : Real.sqrt (∑ i, x i ^ 2) ≤ 729 / 50000                                   (*)

for its own chart perturbation `x`.  In `DSHPatchTemplateK5L4.lean` this was left as a typed
CONDITIONAL premise `hbridge : Patch120K5Actual.q u y = Real.sqrt (∑ i, x i ^ 2)`.  Here the
identification is PROVED, so the leaf's `hr` and `hpin` premises are DISCHARGED for any cell
whose pinned containment is paid.

CONTENT (what is proved, and why it is cell-independent):
  1. generic pin/gauge algebra for the pinned deviation `(θ i − θ p) − (β i − β p)`:
     (a) it vanishes at the pin site (`pinDev_pin`);
     (b) it is INVARIANT under a global angle shift ω (`pinDev_gauge`, `pinDev_gauge_sum_sq`) --
         i.e. the gauge `ω = θ_p(y) − θ*_p` never has to be chosen to evaluate the pinned norm,
         which is exactly why (*) is well posed;
     (c) it transports from the RAW-8 pin to the CANONICAL-6 pin with the norm preserved,
         consuming the PAID `ResumePinnedReindex.canonReindex_displacement` and
         `ResumePinnedReindex.sum_canonReindex_sq` (`pinDev_canonReindex`,
         `pinDev_canonReindex_sum_sq`).  This is the "raw 8 ↔ canonical 6" relabeling: a
         relabeling together with the fixed graph incidence map, NOT a cyclic symmetry, and it
         is cited rather than assumed.
  2. the patch instance: the patch's own pinned block `Patch120K5Actual.h u y i` IS the
     canonical-6-pinned deviation of the t-frame cell vector `y` against the source chart
     `chartY u L D` (`pinnedVec_eq_h`); hence `q2 u y = Σ i, (pinnedVec u y i)^2`
     (`pinnedVec_sum_sq`) and the pin holds (`pinnedVec_pin`).
  3. THE BRIDGE: `leaf_hr_of_q2` / `leaf_hr_of_pinned_filter` turn ANY cell's paid containment
     into (*) VERBATIM.  Both are generic in `(u, y)`: no cell, cluster or patch index occurs, so
     they pay all 120 cells at once and the per-cell work stays where it belongs (L2 containment
     of each cluster).
  4. `leaf_gain_with_bridge`: the leaf is applied with `x := pinnedVec u y` and `pidx := 6`, so
     its `hpin` and `hr` are supplied by this file; only the 24 non-x premises remain conditional.

`ResumeNetworkIsometry.oracle_isometry` (`V2 (f ∘ U) = V2 U` for a distance-preserving bijection)
is the upstream statement that makes the POINT-level configuration gauge-invariant, hence the
leaf's V2-side conclusion is gauge-independent.  The NORM side (*) is gauge-invariant by
`pinDev_gauge_sum_sq` and needs no isometry.  Both facts are cited, not assumed.

UNPAID (explicit): the actual source N/H/box families (hNB/hAB/hFB/hCB/hGB/hHB/hrowBox, Cq, η)
and the source identities (hNcol/hNbal/hs/ha/hl/hUeq/hresp/hsym/hρ/hfluxα) -- 24 typed premises;
the per-cell L2 containment of the 118 non-K5 cells (patch-survey's lane); and every
global/topology obligation.  This file is NOT an unconditional sharp lower bound and does not
touch `SourceExactRoot.main_of_lower_bound`.

Scope: local[any patch cell, generic in (u,y)] / standalone + module / `hr` + `hpin`
UNCONDITIONAL given the cell's containment; leaf conclusion CONDITIONAL on the 24 typed premises.
No sorry, no custom axiom, no native_decide, no heartbeat raise.
-/
import N11Formalization.DSHPatchTemplateK5
import N11Formalization.ResumePinnedReindex
import N11Formalization.ResumeNetworkIsometry
import N11Formalization.FlashLocalFrobeniusLeafAllBox

set_option autoImplicit false
set_option maxRecDepth 10000

namespace N11Formalization.DSHPatchBridge

open Finset
open N11Formalization
open N11Formalization.Patch120K5Actual

noncomputable section

/-! ## 1. generic pin / gauge / relabeling algebra -/

/-- Pinned deviation of `θ` against `β` at pin site `p`. -/
def pinDev (θ β : Fin 9 → ℝ) (p : Fin 9) : Fin 9 → ℝ :=
  fun i => (θ i - θ p) - (β i - β p)

/-- The pinned coordinate is exactly zero: the pin lives inside the deviation, it is not a
separate hypothesis. -/
theorem pinDev_pin (θ β : Fin 9 → ℝ) (p : Fin 9) : pinDev θ β p p = 0 := by
  simp [pinDev]

/-- **GAUGE INVARIANCE (rotation ω = θ_p(y) − θ*_p).** A global angle shift added to BOTH the
configuration angles and the source angles cancels in the pinned deviation. -/
theorem pinDev_gauge (θ β : Fin 9 → ℝ) (p : Fin 9) (ω : ℝ) :
    pinDev (fun i => θ i + ω) (fun i => β i + ω) p = pinDev θ β p := by
  funext i
  simp only [pinDev]
  ring

/-- The squared norm in the leaf's `hr` slot is gauge-invariant: no particular `ω` must be chosen
(`ω = θ_6(y) − θ*_6` is only a convenient normalization). -/
theorem pinDev_gauge_sum_sq (θ β : Fin 9 → ℝ) (p : Fin 9) (ω : ℝ) :
    (∑ i, (pinDev (fun i => θ i + ω) (fun i => β i + ω) p i) ^ 2)
      = ∑ i, (pinDev θ β p i) ^ 2 := by
  rw [pinDev_gauge]

/-- Even a ONE-SIDED angle shift of the configuration cancels in the pinned deviation (it is a
difference of differences), so the gauge invariance is not an artefact of shifting both sides.
This is the precise sense in which the leaf's `hr` is about the ROTATED pinned deviation and yet
needs no `ω` to be chosen: every rotation gives the same pinned deviation. -/
theorem pinDev_shift_left (θ β : Fin 9 → ℝ) (p : Fin 9) (ω : ℝ) :
    pinDev (fun i => θ i + ω) β p = pinDev θ β p := by
  funext i
  simp only [pinDev]
  ring

/-- **NEGATIVE CONTROL (the pin site is load-bearing).** Normalizing the deviation at the RAW site
8 does NOT make the CANONICAL-6 coordinate vanish: the wrong pin site is detected, which is
exactly why the raw-8 ↔ canonical-6 relabeling `pinDev_canonReindex` is needed and cannot be
skipped.  (With `θ i = i`, `β = 0`, pin 8: the canonical-6 coordinate is `6 − 8 = −2 ≠ 0`.) -/
theorem wrong_pin_site_not_zero :
    pinDev (fun i : Fin 9 => (i : ℝ)) (fun _ : Fin 9 => 0) 8 6 ≠ 0 := by
  simp only [pinDev]
  norm_num

/-- The same wrong pin site also changes the pinned VECTOR, so it is not merely a relabeling of
the pin coordinate. -/
theorem wrong_pin_site_differs :
    pinDev (fun i : Fin 9 => (i : ℝ)) (fun _ : Fin 9 => 0) 6 0
      ≠ pinDev (fun i : Fin 9 => (i : ℝ)) (fun _ : Fin 9 => 0) 8 0 := by
  simp only [pinDev]
  norm_num

/-- **PIN-SITE RELABELING raw 8 ↔ canonical 6** (consumes the paid
`ResumePinnedReindex.canonReindex_displacement`): a raw-8-pinned deviation IS the
canonical-6-pinned deviation of the relabeled angles. -/
theorem pinDev_canonReindex (θ β : Fin 9 → ℝ) :
    ResumeLocalIncidence.canonReindex (pinDev θ β 8)
      = pinDev (ResumeLocalIncidence.canonReindex θ) (ResumeLocalIncidence.canonReindex β) 6 :=
  funext fun i => ResumeLocalIncidence.canonReindex_displacement θ β i

/-- The relabeling preserves the pinned squared norm (consumes the paid
`ResumePinnedReindex.sum_canonReindex_sq`), so the raw-8 presentation and the canonical-6
presentation yield the SAME `hr` bound. -/
theorem pinDev_canonReindex_sum_sq (θ β : Fin 9 → ℝ) :
    (∑ i, (pinDev (ResumeLocalIncidence.canonReindex θ)
      (ResumeLocalIncidence.canonReindex β) 6 i) ^ 2)
      = ∑ k, (pinDev θ β 8 k) ^ 2 := by
  rw [← pinDev_canonReindex θ β]
  exact ResumeLocalIncidence.sum_canonReindex_sq (pinDev θ β 8)

/-- Dropping the pinned coordinate does not change the pinned squared norm (its term is `0`). -/
theorem pinDev_sum_sq_eq_filter (θ β : Fin 9 → ℝ) (p : Fin 9) :
    (∑ i, (pinDev θ β p i) ^ 2)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin 9 => i ≠ p), (pinDev θ β p i) ^ 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun i : Fin 9 => i ≠ p) (f := fun i => (pinDev θ β p i) ^ 2)]
  have hzero : (∑ i ∈ Finset.univ.filter (fun i : Fin 9 => ¬ i ≠ p),
      (pinDev θ β p i) ^ 2) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hip : i = p := by simpa using (Finset.mem_filter.mp hi).2
    subst hip
    rw [pinDev_pin]
    ring
  rw [hzero, add_zero]

/-! ## 2. the patch instance: `h` IS the canonical-6-pinned deviation -/

/-- The configuration-side angle family of the t-frame cell vector `y`.
`L` and `D` are FULLY QUALIFIED: the project also has an unrelated Fin5×Fin7 `D`
(`Fin 5 → Fin 7 → RatInterval`), so an unqualified `D` silently resolves to the wrong object. -/
def cellAngle (y : Fin 9 → ℝ) : Fin 9 → ℝ :=
  fun i => ResumeGlobal.anchorAngle Patch120K5Actual.L Patch120K5Actual.D y i.val

/-- The source-side angle family of the root box `u` (the source chart). -/
def srcAngle (u : Fin 12 → ℝ) : Fin 9 → ℝ :=
  fun i => ResumeGlobal.anchorAngle Patch120K5Actual.L Patch120K5Actual.D
    (FlashLeafRootChart.chartY u Patch120K5Actual.L Patch120K5Actual.D) i.val

/-- The patch's pinned deviation vector: the canonical-6-pinned anchor-angle deviation of `y`
against the source chart.  This is the exact object whose norm the leaf's `hr` slot bounds. -/
def pinnedVec (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) : Fin 9 → ℝ :=
  pinDev (cellAngle y) (srcAngle u) 6

/-- The patch's own pinned block IS this vector, verbatim (paid
`Patch120K5Actual.h_eq_actual_perturbation`). -/
theorem pinnedVec_eq_h (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) (i : Fin 9) :
    pinnedVec u y i = Patch120K5Actual.h u y i := by
  have h6 : ((6 : Fin 9) : ℕ) = 6 := rfl
  rw [Patch120K5Actual.h_eq_actual_perturbation u y i]
  simp only [pinnedVec, pinDev, cellAngle, srcAngle, h6]

/-- The pin holds for the patch's pinned block (canonical site 6). -/
theorem pinnedVec_pin (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) : pinnedVec u y 6 = 0 := by
  unfold pinnedVec
  exact pinDev_pin _ _ 6

/-- `Σ i, (pinnedVec u y i)^2 = q2 u y`: the patch's containment quantity IS the squared norm in
the leaf's `hr` slot. -/
theorem pinnedVec_sum_sq (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) :
    (∑ i, (pinnedVec u y i) ^ 2) = Patch120K5Actual.q2 u y := by
  have hpt : ∀ i : Fin 9, (pinDev (cellAngle y) (srcAngle u) 6 i) ^ 2
      = (Patch120K5Actual.h u y i) ^ 2 := by
    intro i
    have h1 : pinDev (cellAngle y) (srcAngle u) 6 i = Patch120K5Actual.h u y i := by
      simpa [pinnedVec] using pinnedVec_eq_h u y i
    rw [h1]
  rw [pinnedVec, pinDev_sum_sq_eq_filter]
  rw [Finset.sum_congr rfl (fun i _ => hpt i), ← Patch120K5Actual.q2_eq_pinned_sum]

/-! ## 3. THE BRIDGE: the leaf's `hr` slot, generic in the cell -/

/-- **The bridge (all-cell shape), squared-input entry point.** Any cell whose pinned containment
is paid as `q2 u y ≤ (729/50000)^2` gets the leaf's premise #7 VERBATIM.  Generic in `(u,y)`: no
cell, cluster or patch index occurs, so it pays all 120 cells at once. -/
theorem leaf_hr_of_q2 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hcont : Patch120K5Actual.q2 u y ≤ (729 / 50000 : ℝ) ^ 2) :
    Real.sqrt (∑ i, (pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  rw [pinnedVec_sum_sq u y]
  rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 729 / 50000)]
  exact hcont

/-- **The bridge (all-cell shape), survey-compatible entry point.** Any cell whose containment is
paid in the anchor-angle FILTER form used by the per-cluster patch files
(`Real.sqrt (∑ i ∈ filter (· ≠ 6), (…)^2) ≤ 729/50000`) also gets the leaf's premise #7 verbatim. -/
theorem leaf_hr_of_pinned_filter {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hcont : Real.sqrt (∑ i ∈ Finset.univ.filter (fun i : Fin 9 => i ≠ 6),
      (pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ)) :
    Real.sqrt (∑ i, (pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  have hsum : (∑ i, (pinnedVec u y i) ^ 2)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin 9 => i ≠ 6), (pinnedVec u y i) ^ 2 := by
    simp only [pinnedVec]
    exact pinDev_sum_sq_eq_filter (cellAngle y) (srcAngle u) 6
  rw [hsum]
  exact hcont

/-- The leaf's `hr` slot for the K5 patch cells, unconditional (the K5 containment is root-paid
through `DSHPatchTemplateK5.containment_sq_of_domain`). -/
theorem leaf_hr_K5 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (h : DSHPatchTemplate.K5.CellDomain u y) :
    Real.sqrt (∑ i, (pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  leaf_hr_of_q2 (DSHPatchTemplate.K5.containment_sq_of_domain h)

/-! ## 4. the leaf consumer with `hpin` and `hr` DISCHARGED -/

/-- **Leaf gain with the bridge.** `x` is instantiated as `pinnedVec u y` and `pidx` as the
canonical pin `6`; the leaf's `hpin` and `hr` are supplied by this file.  The 24 remaining
premises are the actual source N/H/box families, typed verbatim, UNPAID. -/
theorem leaf_gain_with_bridge
    {α : ResumeNetwork.Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hcont : Patch120K5Actual.q2 u y ≤ (729 / 50000 : ℝ) ^ 2)
    (θ ρ : Fin 9 → ℝ) {N : ResumeNetwork.Edge → Fin 4 → ℝ}
    {Λα : Fin 9 → Fin 9 → ℝ} {Rstar : ℝ}
    (HB : Fin 8 → Fin 8 → RatInterval) (GB : Fin 8 → Fin 4 → RatInterval)
    (NB : ResumeNetwork.Edge → Fin 4 → RatInterval) (AB : ResumeNetwork.Edge → RatInterval)
    (FB : Fin 4 → Fin 9 → Fin 2 → RatInterval) (CB : Fin 8 → Fin 8 → RatInterval)
    (Cq : Matrix (Fin 8) (Fin 8) ℚ) (η : ℚ)
    (hNcol : ∀ a : Fin 4, ∑ e, N e a = 0)
    (hNbal : ∀ (a : Fin 4) (v : ResumeDirichlet.Free),
      ∑ e, (N e a * ResumeDirichlet.incidence e v) • ResumeDirichlet.edgeVector U C Z e = 0)
    (hs : ∑ e, α e = 1)
    (ha : ∀ v : ResumeDirichlet.Free,
      ∑ e, (α e * ResumeDirichlet.incidence e v) • ResumeDirichlet.edgeVector U C Z e = 0)
    (hl : ∀ e : ResumeNetwork.Edge, α e ≠ 0 → ResumeNetwork.edgeLength U C Z e ^ 2 = Rstar ^ 2)
    (hUeq : ∀ i : Fin 9, U i = circleMap (θ i))
    (hresp : ∀ W : Fin 9 → Point, FlashLocal.Eform Λα W W = ResumeNetwork.dirichletEnergy α W)
    (hsym : ∀ i j : Fin 9, Λα i j = Λα j i)
    (hρ : ∀ i : Fin 9, 0 ≤ ρ i)
    (hfluxα : ∀ i : Fin 9, ResumeAnchorFlux.flux α U C Z i = ρ i • circleMap (θ i))
    (hNB : ∀ (e : ResumeNetwork.Edge) (a : Fin 4), (NB e a).Mem (N e a))
    (hAB : ∀ e : ResumeNetwork.Edge, (AB e).Mem (α e))
    (hFB : ∀ (a : Fin 4) (j : Fin 9) (c : Fin 2),
      (FB a j c).Mem ((ResumeAnchorFlux.flux (fun e => N e a) U C Z j).ofLp c))
    (hCB : ∀ k l : Fin 8,
      (CB k l).Mem (FlashLocal.Cmat Λα θ ((6 : Fin 9).succAbove k) ((6 : Fin 9).succAbove l)))
    (hGB : ∀ (k : Fin 8) (a : Fin 4),
      (GB k a).Mem (FlashLocal.Gmat ResumeAnchorFlux.anchorIncidence
        (ResumeDirichlet.edgeVector U C Z) (fun k => FlashLocal.circleTangent (θ k)) N
        ((6 : Fin 9).succAbove k) a))
    (hHB : ∀ k l : Fin 8,
      (HB k l).Mem (FlashLocal.H0mat Λα ρ (fun k => FlashLocal.circleTangent (θ k))
        ((6 : Fin 9).succAbove k) ((6 : Fin 9).succAbove l)))
    (hα0 : ∀ e : ResumeNetwork.Edge, 0 ≤ (AB e).lo)
    (hgNorm : ∑ k : Fin 8, ∑ a : Fin 4, (GB k a).abs.hi ^ 2 ≤ (15363 / 1000000 : ℚ) ^ 2)
    (hFsqCert : ∑ a : Fin 4, ∑ j : Fin 9, ∑ c : Fin 2,
      (FB a j c).abs.hi ^ 2 ≤ (429 / 50000 : ℚ) ^ 2)
    (hCcert : ∑ k : Fin 8, ∑ l : Fin 8, (CB k l).abs.hi ^ 2 ≤ (179 / 5000 : ℚ) ^ 2)
    (hBcert : ∀ e : ResumeNetwork.Edge,
      RatInterval.sqrtHi (∑ a : Fin 4, (NB e a).abs.hi ^ 2) ≤ (99 / 200) * (AB e).lo)
    (hDcert : ∀ j : Fin 9, (∑ i : Fin 9, ∑ side : Fin 2,
      if ResumeNetwork.anchorIndex i side = j then (AB (Sum.inl (i, side))).hi else (0 : ℚ))
      ≤ 2 / 25)
    (hη : 0 < η)
    (hrowBox : ∀ i : Fin 8, (η + ∑ j : Fin 8, if j = i then (0 : ℚ) else
      (ResumeIntervalMatrix.congruenceBox Cq
        (ResumeIntervalAugmented.augmentedBox HB GB 734 (9 / 5000)) i j).abs.hi)
      ≤ (ResumeIntervalMatrix.congruenceBox Cq
        (ResumeIntervalAugmented.augmentedBox HB GB 734 (9 / 5000)) i i).lo) :
    (∑ i, (pinnedVec u y i) ^ 2) / 100000
      ≤ ResumeNetwork.V2 (U + FlashLocal.disp θ (pinnedVec u y)) - Rstar ^ 2 :=
  FlashLocal.local_gain_actual_frobenius_leaf_all_box
    (α := α) (U := U) (C := C) (Z := Z) θ (pinnedVec u y) ρ (N := N) 6 (Λα := Λα)
    (Rstar := Rstar)
    HB GB NB AB FB CB Cq η
    hNcol hNbal hs ha hl hUeq
    (leaf_hr_of_q2 hcont)
    hresp (pinnedVec_pin u y) hsym hρ hfluxα hNB hAB hFB hCB hGB hHB hα0
    hgNorm hFsqCert hCcert hBcert hDcert hη hrowBox

end

end N11Formalization.DSHPatchBridge

#check @N11Formalization.DSHPatchBridge.pinDev
#check @N11Formalization.DSHPatchBridge.pinDev_pin
#check @N11Formalization.DSHPatchBridge.pinDev_gauge
#check @N11Formalization.DSHPatchBridge.pinDev_gauge_sum_sq
#check @N11Formalization.DSHPatchBridge.pinDev_shift_left
#check @N11Formalization.DSHPatchBridge.wrong_pin_site_not_zero
#check @N11Formalization.DSHPatchBridge.wrong_pin_site_differs
#check @N11Formalization.DSHPatchBridge.pinDev_canonReindex
#check @N11Formalization.DSHPatchBridge.pinDev_canonReindex_sum_sq
#check @N11Formalization.DSHPatchBridge.pinDev_sum_sq_eq_filter
#check @N11Formalization.DSHPatchBridge.pinnedVec
#check @N11Formalization.DSHPatchBridge.pinnedVec_eq_h
#check @N11Formalization.DSHPatchBridge.pinnedVec_pin
#check @N11Formalization.DSHPatchBridge.pinnedVec_sum_sq
#check @N11Formalization.DSHPatchBridge.leaf_hr_of_q2
#check @N11Formalization.DSHPatchBridge.leaf_hr_of_pinned_filter
#check @N11Formalization.DSHPatchBridge.leaf_hr_K5
#check @N11Formalization.DSHPatchBridge.leaf_gain_with_bridge
#print axioms N11Formalization.DSHPatchBridge.pinDev_pin
#print axioms N11Formalization.DSHPatchBridge.pinDev_gauge
#print axioms N11Formalization.DSHPatchBridge.pinDev_gauge_sum_sq
#print axioms N11Formalization.DSHPatchBridge.pinDev_canonReindex
#print axioms N11Formalization.DSHPatchBridge.pinDev_canonReindex_sum_sq
#print axioms N11Formalization.DSHPatchBridge.pinDev_sum_sq_eq_filter
#print axioms N11Formalization.DSHPatchBridge.pinnedVec_eq_h
#print axioms N11Formalization.DSHPatchBridge.pinnedVec_pin
#print axioms N11Formalization.DSHPatchBridge.pinnedVec_sum_sq
#print axioms N11Formalization.DSHPatchBridge.leaf_hr_of_q2
#print axioms N11Formalization.DSHPatchBridge.leaf_hr_of_pinned_filter
#print axioms N11Formalization.DSHPatchBridge.leaf_hr_K5
#print axioms N11Formalization.DSHPatchBridge.leaf_gain_with_bridge