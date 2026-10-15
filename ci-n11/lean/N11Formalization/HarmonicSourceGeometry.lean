/-
n11-formalization — cline-six / harmonic-response (2026-10-01) — **unbuilt draft (new filename)**.

STATUS: NOT KERNEL-CHECKED.  Lead owns the serial gate.

## Obligation (Lead 2026-10-01)

The **actual geometry force consumer** — not the harmonic-coefficient version.  Needs:
  * the geometric identity `hEV` (`edgeVector` along `edgeMap` = the source edge vector);
  * the source's `srcB2` force rows in their actual 40-coordinate form;
and it must produce the canonical free-node balance `actual_free_balance`, then the harmonic `H`
(through the already-green C1628), never assuming `H` or identifying it with the centres.

## Contents

§1 `srcVec` (the source edge vector `X_V − X_W` as a `Point`, from `SourceN2.srcD2`) and
   `geom_balance_iff_b2_rows`: the **40 actual `srcB2` force rows** (per free row and coordinate)
   vanish iff the source free-node vector balance `∀ w, srcRowSum α u w = 0` holds
   (`srcRowSum α u w = ∑_s (α (edgeMap s) · srcInc s w) • srcVec u s`).  This is the point where the
   actual B2 force is consumed (row = incidence × edge-vector coordinate).
§2 `point_sum_edgeMap_reindex`: the `Point`-valued reindexing of an `Edge`-sum along `edgeMap`
   (α vanishing on the six slack face edges).
§3 `canonical_free_balance_of_source_geom`: the source free-node vector balance plus `hEV` give the
   canonical `∀ v : Free, ∑_e (α_e · incidence e v) • edgeVector (canonAnchors u) (canonCenters u)
   (canonFaceZ u) e = 0`.
§4 `exists_lift_of_source_geom`: the consumer: a balanced `H` exists whose lift minimises for every
   boundary datum and reproduces the actual anchor flux and weighted energy
   (`HarmonicReproduceActualV2.exists_lift_reproducing_actual`).

Dependencies (modules, to be built by the Lead): `N11Formalization.SourceN2` (green),
`N11Formalization.LocalSharpAuxZ` (green), `N11Formalization.HarmonicReproduceActualV2` (green),
`N11Formalization.HarmonicSourceTransport` (gate-green source, being module-copied).
The two first-pass proof blocks of `HarmonicSourceGeometry.lean` (§1 row identity, §2 coordinate
manipulation) are carried here; they remain the risk points and are marked inline.

Not claimed: actual α / stationarity derivation of the B2 rows (source-stress), the geometric
identity `hEV` itself (local-sharp T-side), `hflux`/radiality, Schur = Gram.  No sorry / custom
axiom / native_decide.
-/
import Mathlib
import N11Formalization.SourceN2
import N11Formalization.LocalSharpAuxZ
import N11Formalization.FlashLeafRootNetwork
import N11Formalization.HarmonicSourceTransport
import N11Formalization.HarmonicReproduceActualV2
import N11Formalization.ResumeLocalIncidence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace N11Formalization.HarmonicSourceGeometryV2

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeDirichlet
open N11Formalization.ResumeHarmonic
open N11Formalization.ResumeResponseGram
open N11Formalization.ResumeAnchorFlux
open N11Formalization.ResumeLocalIncidence
open N11Formalization.ResumeGlobal
open N11Formalization.SourceN2
open N11Formalization.LocalSharpAuxZ
open N11Formalization.FlashRootNetwork
open N11Formalization.HarmonicSourceTransport

/-- The source edge vector `X_V − X_W` as a point: the actual difference of the two source vertices
(structural; no `Fin 2 → ℝ` coercion). -/
noncomputable def srcEdgeVec (u : Fin 12 → ℝ) (s : SourceEdge) : Point :=
  srcX2 u (srcEdgeV2 (srcFlat s)) - srcX2 u (srcEdgeW2 (srcFlat s))

/-- Its coordinates are exactly `srcD2`. -/
theorem srcEdgeVec_ofLp (u : Fin 12 → ℝ) (s : SourceEdge) (c : Fin 2) :
    (srcEdgeVec u s).ofLp c = srcD2 u (srcFlat s) c := by
  simp only [srcEdgeVec, srcD2, PiLp.sub_apply]

/-- Free row and coordinate ↦ the actual `srcB2` force row `2*(node − 9) + c`. -/
def rowIdx (w : SrcFree) (c : Fin 2) : Fin 41 :=
  ⟨2 * ((srcNode29 w : ℕ) - 9) + (c : ℕ), by
    have h : (srcNode29 w : ℕ) < 29 := (srcNode29 w).isLt
    have hc : (c : ℕ) < 2 := c.isLt
    omega⟩

/-- Nat divisor fact for the actual B2 row index (independent of any geometry). -/
theorem rowIdx_div (w : SrcFree) (c : Fin 2) :
    ((rowIdx w c : Fin 41) : ℕ) / 2 = (srcNode29 w : ℕ) - 9 := by
  simp only [rowIdx, Fin.val_mk]
  omega

/-- Nat remainder fact for the actual B2 row index. -/
theorem rowIdx_mod (w : SrcFree) (c : Fin 2) :
    ((rowIdx w c : Fin 41) : ℕ) % 2 = (c : ℕ) := by
  simp only [rowIdx, Fin.val_mk]
  fin_cases c <;> omega

/-- The row is never the mass row. -/
theorem rowIdx_ne_mass (w : SrcFree) (c : Fin 2) : ((rowIdx w c : Fin 41) : ℕ) ≠ 40 := by
  have h1 := rowIdx_div w c
  have h2 : (srcNode29 w : ℕ) - 9 ≤ 19 := by
    have h : (srcNode29 w : ℕ) < 29 := (srcNode29 w).isLt
    omega
  have hc : (c : ℕ) < 2 := c.isLt
  omega
/-- srcIncZ with **Nat-valued** conditions (so that it matches srcB2's internal ↑(srcEdgeV2 ·)
form after owIdx_div). -/
theorem srcIncZ_nat (s : SourceEdge) (w : SrcFree) :
    (srcIncZ s w : ℝ)
      = (if (srcEdgeV2 (srcFlat s) : ℕ) = (srcNode29 w : ℕ) then 1 else 0)
        + (if (srcEdgeW2 (srcFlat s) : ℕ) = (srcNode29 w : ℕ) then -1 else 0) := by
  simp only [srcIncZ]
  by_cases h1 : (srcEdgeV2 (srcFlat s) : ℕ) = (srcNode29 w : ℕ)
  · have h1' : srcEdgeV2 (srcFlat s) = srcNode29 w := Fin.ext h1
    by_cases h2 : (srcEdgeW2 (srcFlat s) : ℕ) = (srcNode29 w : ℕ)
    · have h2' : srcEdgeW2 (srcFlat s) = srcNode29 w := Fin.ext h2
      simp only [h1, h2, h1', h2', if_true]
      norm_num
    · have h2' : ¬ (srcEdgeW2 (srcFlat s) = srcNode29 w) := fun hh => h2 (congrArg Fin.val hh)
      simp only [h1, h2, h1', h2', if_true, if_false]
      norm_num
  · have h1' : ¬ (srcEdgeV2 (srcFlat s) = srcNode29 w) := fun hh => h1 (congrArg Fin.val hh)
    by_cases h2 : (srcEdgeW2 (srcFlat s) : ℕ) = (srcNode29 w : ℕ)
    · have h2' : srcEdgeW2 (srcFlat s) = srcNode29 w := Fin.ext h2
      simp only [h1, h2, h1', h2', if_true, if_false]
      norm_num
    · have h2' : ¬ (srcEdgeW2 (srcFlat s) = srcNode29 w) := fun hh => h2 (congrArg Fin.val hh)
      simp only [h1, h2, h1', h2', if_true, if_false]
      norm_num
/-- **The actual B2 row is the source incidence times the edge-vector coordinate.** -/
theorem srcB2_row_eq (u : Fin 12 → ℝ) (w : SrcFree) (c : Fin 2) (s : SourceEdge) :
    srcB2 u (rowIdx w c) (srcFlat s) = srcIncZ s w * srcD2 u (srcFlat s) c := by
  have hdiv := rowIdx_div w c
  have hmod := rowIdx_mod w c
  have hne := rowIdx_ne_mass w c
  have h9 : 9 + ((srcNode29 w : ℕ) - 9) = (srcNode29 w : ℕ) := by
    rcases w with j | g <;> simp only [srcNode29, Fin.val_mk] <;> omega
  rw [srcIncZ_nat]
  simp only [srcB2, hne, if_false, hdiv, hmod, h9, srcD2]
  by_cases h1 : (srcEdgeV2 (srcFlat s) : ℕ) = (srcNode29 w : ℕ) <;>
    by_cases h2 : (srcEdgeW2 (srcFlat s) : ℕ) = (srcNode29 w : ℕ) <;>
    simp_all <;> ring

/-- The source free-node vector balance. -/
noncomputable def srcRowSum (α : Edge → ℝ) (u : Fin 12 → ℝ) (w : SrcFree) : Point :=
  ∑ s : SourceEdge, (α (edgeMap s) * (srcIncZ s w : ℝ)) • srcEdgeVec u s

/-- **The 40 actual `srcB2` force rows vanish iff the source free-node vector balance holds.** -/
theorem geom_balance_iff_b2_rows {α : Edge → ℝ} {u : Fin 12 → ℝ} :
    (∀ w : SrcFree, ∀ c : Fin 2,
        ∑ s : SourceEdge, srcB2 u (rowIdx w c) (srcFlat s) * α (edgeMap s) = 0)
      ↔ (∀ w : SrcFree, srcRowSum α u w = 0) := by
  constructor
  · intro h w
    apply PiLp.ext
    intro c
    have hc := h w c
    have hcoord : (srcRowSum α u w) c
        = ∑ s : SourceEdge, srcB2 u (rowIdx w c) (srcFlat s) * α (edgeMap s) := by
      simp only [srcRowSum, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, srcEdgeVec_ofLp]
      exact Finset.sum_congr rfl (fun s _ => by rw [srcB2_row_eq]; ring)
    rw [hcoord, hc]; simp
  · intro h w c
    have hw := congrFun (congrArg (fun p : Point => p.ofLp) (h w)) c
    rw [srcRowSum] at hw
    have hcoord : (∑ s : SourceEdge, (α (edgeMap s) * (srcIncZ s w : ℝ)) • srcEdgeVec u s) c
        = ∑ s : SourceEdge, srcB2 u (rowIdx w c) (srcFlat s) * α (edgeMap s) := by
      simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, srcEdgeVec_ofLp]
      exact Finset.sum_congr rfl (fun s _ => by rw [srcB2_row_eq]; ring)
    rw [hcoord] at hw
    simpa using hw

/-- `Point`-valued reindexing of an `Edge`-sum along `edgeMap`. -/
theorem point_sum_edgeMap_reindex {α : Edge → ℝ} {F : Edge → Point}
    (hzero : ∀ e : Edge, e ∉ Finset.univ.image edgeMap → α e = 0) :
    (∑ e : Edge, α e • F e) = ∑ s : SourceEdge, α (edgeMap s) • F (edgeMap s) := by
  rw [← Finset.sum_image (s := (Finset.univ : Finset SourceEdge)) (g := edgeMap)
    (f := fun e : Edge => α e • F e) (fun x _ y _ h => edgeMap_injective h)]
  exact (Finset.sum_subset (Finset.subset_univ _)
    (fun e _ he => by rw [hzero e he, zero_smul])).symm

/-- **The canonical free-node balance from the source geometric balance.**  `hEV` is the geometric
identity along `edgeMap` (local-sharp's T-side `edgeVector_edgeMap`, wired with
`Zc := canonFaceZ u`, `Z := sourceAuxZ u`, `hZ := canonFaceZ_active u`). -/
theorem canonical_free_balance_of_source_geom {α : Edge → ℝ} {u : Fin 12 → ℝ}
    (hzero : ∀ k : Fin 3, α (.inr (5, k)) = 0 ∧ α (.inr (7, k)) = 0)
    (hEV : ∀ s : SourceEdge,
      edgeVector (canonAnchors u) (canonCenters u) (canonFaceZ u) (edgeMap s)
        = srcEdgeVec u s)
    (hsrc : ∀ w : SrcFree, srcRowSum α u w = 0) :
    ∀ v : Free,
      ∑ e : Edge, (α e * incidence e v)
        • edgeVector (canonAnchors u) (canonCenters u) (canonFaceZ u) e = 0 := by
  classical
  have hz : ∀ e : Edge, e ∉ Finset.univ.image edgeMap → α e = 0 :=
    zero_off_image_of_slack hzero
  have hunused : ∀ e : Edge, α e ≠ 0 → ∀ v : Free,
      (∀ w : SrcFree, srcNode w ≠ v) → incidence e v = 0 := by
    intro e hae v hv
    rcases unused_iff_slack v hv with rfl | rfl <;> rcases e with ⟨i, s⟩ | ⟨f, k⟩
    · simp [incidence]
    · by_cases hf : f = 5
      · subst hf; exact absurd (hzero k).1 hae
      · have h2 : ¬ ((Sum.inr 5 : Free) = Sum.inr f) := fun hh => hf (Sum.inr.inj hh).symm
        simp only [incidence, Sum.inr_ne_inl, h2, if_false, sub_zero]
    · simp [incidence]
    · by_cases hf : f = 7
      · subst hf; exact absurd (hzero k).2 hae
      · have h2 : ¬ ((Sum.inr 7 : Free) = Sum.inr f) := fun hh => hf (Sum.inr.inj hh).symm
        simp only [incidence, Sum.inr_ne_inl, h2, if_false, sub_zero]
  intro v
  by_cases hv : ∃ w : SrcFree, srcNode w = v
  · obtain ⟨w, rfl⟩ := hv
    have hreindex := point_sum_edgeMap_reindex (α := α)
      (F := fun e => incidence e (srcNode w)
        • edgeVector (canonAnchors u) (canonCenters u) (canonFaceZ u) e) hz
    simp only [← smul_smul]
    rw [hreindex]
    have hstep : (∑ s : SourceEdge, α (edgeMap s)
          • (incidence (edgeMap s) (srcNode w)
            • edgeVector (canonAnchors u) (canonCenters u) (canonFaceZ u) (edgeMap s)))
        = ∑ s : SourceEdge, (α (edgeMap s) * (srcIncZ s w : ℝ)) • srcEdgeVec u s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [incidence_edgeMap_eq_srcInc, hEV]
      rw [← smul_smul]
      simp only [srcInc]
    rw [hstep]
    exact hsrc w
  · have hv' : ∀ w : SrcFree, srcNode w ≠ v := by
      intro w hw; exact hv ⟨w, hw⟩
    apply Finset.sum_eq_zero
    intro e _
    by_cases hae : α e = 0
    · simp [hae]
    · rw [hunused e hae v hv', mul_zero, zero_smul]

/-- **Consumer.**  The actual source geometric balance (the 40 `srcB2` force rows) at the canonical
geometry yields a balanced `H` whose lift minimises for every boundary datum and reproduces the
actual anchor flux and weighted energy. -/
theorem exists_lift_of_source_geom {α : Edge → ℝ} {u : Fin 12 → ℝ}
    (hα : ∀ e : Edge, 0 ≤ α e)
    (hzero : ∀ k : Fin 3, α (.inr (5, k)) = 0 ∧ α (.inr (7, k)) = 0)
    (hEV : ∀ s : SourceEdge,
      edgeVector (canonAnchors u) (canonCenters u) (canonFaceZ u) (edgeMap s)
        = srcEdgeVec u s)
    (hrows : ∀ w : SrcFree, ∀ c : Fin 2,
        ∑ s : SourceEdge, srcB2 u (rowIdx w c) (srcFlat s) * α (edgeMap s) = 0) :
    ∃ H : Free → Fin 9 → ℝ,
      (∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0) ∧
      (∀ W : Fin 9 → Point,
        energy α W (fun i => lift H W (.inl i)) (fun f => lift H W (.inr f))
          = dirichletEnergy α W) ∧
      (∀ i, flux α (canonAnchors u)
          (fun i => lift H (canonAnchors u) (.inl i))
          (fun f => lift H (canonAnchors u) (.inr f)) i
        = flux α (canonAnchors u) (canonCenters u) (canonFaceZ u) i) ∧
      energy α (canonAnchors u)
        (fun i => lift H (canonAnchors u) (.inl i))
        (fun f => lift H (canonAnchors u) (.inr f))
        = energy α (canonAnchors u) (canonCenters u) (canonFaceZ u) := by
  have hsrc : ∀ w : SrcFree, srcRowSum α u w = 0 :=
    (geom_balance_iff_b2_rows).mp hrows
  exact HarmonicReproduceActualV2.exists_lift_reproducing_actual
    (α := α) (U := canonAnchors u) (C := canonCenters u) (Z := canonFaceZ u) hα
    (canonical_free_balance_of_source_geom hzero hEV hsrc)

end N11Formalization.HarmonicSourceGeometryV2

#print axioms N11Formalization.HarmonicSourceGeometryV2.srcB2_row_eq
#print axioms N11Formalization.HarmonicSourceGeometryV2.canonical_free_balance_of_source_geom
#print axioms N11Formalization.HarmonicSourceGeometryV2.exists_lift_of_source_geom
