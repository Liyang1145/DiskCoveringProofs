/-
DSHPatchTemplateK5L4.lean -- DSH-PATCH-T0 layer 4: the patch result applied through the
ROOT-IMPORTED upstream consumer `FlashLocal.local_gain_actual_frobenius_leaf_all_box`.

Why this file exists (patch-survey warning, adopted): the K5 corollary
`Patch120K5Actual.local_gain_of_geometric_bound` concludes `q^2/100000 <= E` with `E` a FREE
variable, so on its own it is NOT a layer-4 consumer.  The real upstream consumer is the
harmonic-leaf chain, whose 7th premise is exactly

    hr : Real.sqrt (∑ i, x i ^ 2) <= 729 / 50000

and that is precisely what this patch's L2 containment supplies.  Here the patch DISCHARGES
that one premise, and the conclusion is the genuine energy comparison

    (∑ i, x i ^ 2) / 100000 <= ResumeNetwork.V2 (U + FlashLocal.disp θ x) - Rstar ^ 2.

CONDITIONAL, explicitly: the other 25 premises of the leaf are Codex's frontier (the actual
source N/H/box families hNB/hAB/hFB/hCB/hGB/hHB/hrowBox/Cq/η plus the source identities
hNcol/hNbal/hs/ha/hl/hUeq/hresp/hpin/hsym/hρ/hfluxα).  They are typed here as premises, VERBATIM
from the kernel-printed signature (`evidence/dsh/patches/survey/out/probe2.log` L129+); they are
NOT paid by this patch and NOT invented by it.  The gauge bridge `hbridge` (identifying the
patch's t-frame pinned norm `q u y` with the leaf's rotated perturbation norm) is likewise a
typed conditional premise; upstream it is discharged through the pin plus the gauge rotation
`omega = theta_6(y) - theta*_6` and `ResumeNetworkIsometry.oracle_isometry`.

Scope labels: local[cell 4935/4957 of cluster k=5] / standalone module / CONDITIONAL on the 26
leaf premises / consumer = `FlashLocal.local_gain_actual_frobenius_leaf_all_box` (root-imported).
No sorry, no custom axiom, no native_decide, no heartbeat raise.
-/
import N11Formalization.DSHPatchTemplateK5
import N11Formalization.FlashLocalFrobeniusLeafAllBox

set_option autoImplicit false
set_option maxRecDepth 10000

namespace N11Formalization.DSHPatchTemplate.K5L4

open Finset
open N11Formalization
open N11Formalization.Patch120K5Actual

noncomputable section

/-- **L4 (real consumer application).** The K5 patch supplies the `hr` slot of the root-imported
harmonic-leaf consumer, hence the actual energy comparison for the patch cells.

Premises are split by ownership:
  * `h` (`CellDomain u y`) and `hbridge` are the patch's contribution: L1 domain + L2 containment
    through the gauge bridge;
  * everything from `hNcol` to `hrowBox` is the remaining leaf premise list, VERBATIM types,
    UNPAID (Codex frontier).
The conclusion is the leaf's own conclusion, so this is a real application, not a restatement. -/
theorem patch_gain_leaf_all_box
    {α : ResumeNetwork.Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} (h : K5.CellDomain u y)
    (θ x ρ : Fin 9 → ℝ) {N : ResumeNetwork.Edge → Fin 4 → ℝ} (pidx : Fin 9)
    {Λα : Fin 9 → Fin 9 → ℝ} {Rstar : ℝ}
    (hbridge : Patch120K5Actual.q u y = Real.sqrt (∑ i, x i ^ 2))
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
    (hpin : x pidx = 0)
    (hsym : ∀ i j : Fin 9, Λα i j = Λα j i)
    (hρ : ∀ i : Fin 9, 0 ≤ ρ i)
    (hfluxα : ∀ i : Fin 9, ResumeAnchorFlux.flux α U C Z i = ρ i • circleMap (θ i))
    (hNB : ∀ (e : ResumeNetwork.Edge) (a : Fin 4), (NB e a).Mem (N e a))
    (hAB : ∀ e : ResumeNetwork.Edge, (AB e).Mem (α e))
    (hFB : ∀ (a : Fin 4) (j : Fin 9) (c : Fin 2),
      (FB a j c).Mem ((ResumeAnchorFlux.flux (fun e => N e a) U C Z j).ofLp c))
    (hCB : ∀ k l : Fin 8,
      (CB k l).Mem (FlashLocal.Cmat Λα θ (pidx.succAbove k) (pidx.succAbove l)))
    (hGB : ∀ (k : Fin 8) (a : Fin 4),
      (GB k a).Mem (FlashLocal.Gmat ResumeAnchorFlux.anchorIncidence
        (ResumeDirichlet.edgeVector U C Z) (fun k => FlashLocal.circleTangent (θ k)) N
        (pidx.succAbove k) a))
    (hHB : ∀ k l : Fin 8,
      (HB k l).Mem (FlashLocal.H0mat Λα ρ (fun k => FlashLocal.circleTangent (θ k))
        (pidx.succAbove k) (pidx.succAbove l)))
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
    (∑ i, x i ^ 2) / 100000
      ≤ ResumeNetwork.V2 (U + FlashLocal.disp θ x) - Rstar ^ 2 :=
  FlashLocal.local_gain_actual_frobenius_leaf_all_box
    (α := α) (U := U) (C := C) (Z := Z) θ x ρ (N := N) pidx (Λα := Λα) (Rstar := Rstar)
    HB GB NB AB FB CB Cq η
    hNcol hNbal hs ha hl hUeq
    (K5.patch_supplies_leaf_hr_slot h hbridge)
    hresp hpin hsym hρ hfluxα hNB hAB hFB hCB hGB hHB hα0
    hgNorm hFsqCert hCcert hBcert hDcert hη hrowBox

end

end N11Formalization.DSHPatchTemplate.K5L4

#check @N11Formalization.DSHPatchTemplate.K5L4.patch_gain_leaf_all_box
#print axioms N11Formalization.DSHPatchTemplate.K5L4.patch_gain_leaf_all_box