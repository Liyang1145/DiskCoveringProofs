/-
n11-formalization — cline-six / harmonic-response (2026-10-01) — **unbuilt draft (new filename)**.

STATUS: NOT KERNEL-CHECKED.  Lead owns the serial gate.  Imports the green modules
`N11Formalization.SourceN2` (local-sharp, correct `sourceFaces` Fin 11 / 41×45 rebuild) and
`N11Formalization.HarmonicUnusedExtension` (this member's V3, gate3-green).

## Obligation (Lead 2026-10-01)

45 → 51 **actual mapping transport**: bind the source N2 free-node force rows (20 rows over the 45
edges) to the canonical small/incidence system, so that the canonical 22-row `hbal` and the
`response`-independence of the two slack auxiliaries follow from a **source-side** balance — no
re-proof of the generic extension layer, and **no** use of the deprecated
`FlashLocalFrobeniusSourceN.srcB` (its `srcFaceSite` collapses hub slots 9/10 under `Fin 9`).
The source's *actual* α force balance (the geometric `srcB2 · α = 0` rows and its derivation from
actual stationarity) stays a premise of the source-stress line; this file supplies the mapping.

## Contents

§1 row binding (all index-level claims decidable, proved by `decide`):
   `SrcFree := Fin 11 ⊕ Fin 9` (11 centres + 9 face auxiliaries, the 20 source free rows);
   `srcNode : SrcFree → Free`, `inl j ↦ inl (rawToCanon j)`, `inr f ↦ inr (faceMap f)`;
   `srcNode29`, `srcFlat`; `srcIncZ` — the source edge's free-node incidence, built from
   `SourceN2.srcEdgeV2`/`srcEdgeW2` (the source's own data, not the canonical one) — and its real
   form `srcInc`; the integer mirror `canonIncZ` of the canonical `incidence` with cast lemma
   `canonIncZ_cast`; `srcNode_injective`; `unused_iff_slack` (the two rows outside the image are
   exactly `inr 5`, `inr 7`);
   **`incidence_edgeMap_eq_srcInc`** — the genuine row binding
   `incidence (edgeMap s) (srcNode w) = srcInc s w`.

§2 `sum_edge_eq_sum_sourceEdge`: if α vanishes on the six canonical face edges outside the image of
   `edgeMap` (faces 5 and 7), every `Edge`-sum of α-weighted terms equals the `SourceEdge`-sum along
   `edgeMap` (`edgeMap_image`, `edgeMap_injective`); `zero_off_image_of_slack` is the "faces 5/7"
   form of that hypothesis.

§3 `src_balance_to_canonical`: a source-side 20-row balance
   `∀ w j, ∑_{s : SourceEdge} (α (edgeMap s) · srcInc s w) · srcCoeff hs s j = 0`,
   `srcCoeff hs s j = anchorIncidence (edgeMap s) j + ∑_z srcInc s z · hs z j`, yields for **every**
   extension `H` of `hs` along `srcNode`:
   * the canonical `hbal`: `∀ v j, ∑_e (α e · incidence e v) · coeff H e j = 0`;
   * `response α (coeff H) = srcGram α (srcCoeff hs)` — the two slack rows are invisible.
   Proof = §1 + §2 + the gate3-green abstract layer (`balanced_extend_of_unused`,
   `gram_extend_eq`) + `NetworkSchurBinding.coeff_eq`.

Not claimed: the actual α (source-stress), the geometric `srcB2 · α = 0` derivation, `hflux`/
radiality, Schur = Gram source binding.  No sorry / custom axiom / native_decide.
-/
import Mathlib
import N11Formalization.SourceN2
import N11Formalization.HarmonicUnusedExtension
import N11Formalization.ResumeLocalIncidence
import N11Formalization.NetworkSchurBinding
import N11Formalization.ResumeResponseGram
import N11Formalization.ResumeAnchorFlux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace N11Formalization.HarmonicSourceTransport

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeDirichlet
open N11Formalization.ResumeHarmonic
open N11Formalization.ResumeResponseGram
open N11Formalization.ResumeAnchorFlux
open N11Formalization.ResumeLocalIncidence
open N11Formalization.SourceN2
open N11Formalization.ResumeGlobal
open N11Formalization.LaplacianSchurBridge
open N11Formalization.HarmonicUnusedExtension

/-! ## §1 row binding -/

/-- The 20 source free rows: 11 centres (`centersOfRoot`, source nodes `9 + j`) ⊕ 9 face
auxiliaries (`srcZ2`, source nodes `20 + f`). -/
abbrev SrcFree := Fin 11 ⊕ Fin 9

/-- Source free row ↦ canonical free row. -/
def srcNode : SrcFree → Free
  | Sum.inl j => Sum.inl (rawToCanon j)
  | Sum.inr f => Sum.inr (faceMap f)

/-- Source free row ↦ source node number (9..28) in `SourceN2`'s 29-point layout. -/
def srcNode29 : SrcFree → Fin 29
  | Sum.inl j => ⟨9 + (j : ℕ), by omega⟩
  | Sum.inr f => ⟨20 + (f : ℕ), by omega⟩

/-- `SourceEdge` ↦ the flat 45-edge index of `SourceN2`. -/
def srcFlat : SourceEdge → Fin 45
  | Sum.inl (k, s) => spokeFlat k s
  | Sum.inr (f, t) => faceFlatEdge f t

/-- Source free-node incidence of edge `s` (integer valued), built from `SourceN2`'s own endpoints
(`srcEdgeV2`/`srcEdgeW2`, flat-indexed by `srcFlat`) — no use of the deprecated `srcB`. -/
def srcIncZ (s : SourceEdge) (w : SrcFree) : ℤ :=
  (if srcEdgeV2 (srcFlat s) = srcNode29 w then 1 else 0)
    + (if srcEdgeW2 (srcFlat s) = srcNode29 w then -1 else 0)

/-- Real-valued source free-node incidence. -/
def srcInc (s : SourceEdge) (w : SrcFree) : ℝ := (srcIncZ s w : ℝ)

/-- Integer mirror of the canonical `incidence`, with the same `if`-conditions (the proof
components of `Fin` are definitionally irrelevant). -/
def canonIncZ : Edge → Free → ℤ
  | .inl (i, _), v => if v = Sum.inl ⟨i.val, by omega⟩ then 1 else 0
  | .inr (f, k), v => (if v = Sum.inl (face f k) then 1 else 0) - (if v = Sum.inr f then 1 else 0)

theorem cast_ite_int (c : Prop) [Decidable c] (a b : ℤ) :
    (((if c then a else b : ℤ)) : ℝ) = if c then (a : ℝ) else (b : ℝ) := by
  by_cases h : c <;> simp [h]

theorem canonIncZ_cast (e : Edge) (v : Free) :
    ((canonIncZ e v : ℤ) : ℝ) = incidence e v := by
  rcases e with ⟨i, s⟩ | ⟨f, k⟩
  · simp only [canonIncZ, incidence, cast_ite_int, Int.cast_one, Int.cast_zero]
  · simp only [canonIncZ, incidence, Int.cast_sub, cast_ite_int, Int.cast_one, Int.cast_zero]

theorem srcNode_injective : Function.Injective srcNode := by decide

/-- The canonical mirror of the source incidence along `edgeMap` and `srcNode` (kernel computation
over the 45 × 20 index pairs). -/
theorem canonIncZ_edgeMap_eq_srcIncZ :
    ∀ (s : SourceEdge) (w : SrcFree), canonIncZ (edgeMap s) (srcNode w) = srcIncZ s w := by
  decide

/-- **The genuine row binding**: the canonical incidence along `edgeMap` equals the source's own
free-node incidence, under the 20 → 22 correspondence `srcNode`. -/
theorem incidence_edgeMap_eq_srcInc (s : SourceEdge) (w : SrcFree) :
    incidence (edgeMap s) (srcNode w) = srcInc s w := by
  calc incidence (edgeMap s) (srcNode w)
      = ((canonIncZ (edgeMap s) (srcNode w) : ℤ) : ℝ) := (canonIncZ_cast _ _).symm
    _ = ((srcIncZ s w : ℤ) : ℝ) := by rw [canonIncZ_edgeMap_eq_srcIncZ]
    _ = srcInc s w := rfl
/-- The rows outside `srcNode`'s image are exactly the two slack auxiliaries 5 and 7. -/
theorem unused_iff_slack (v : Free) (hv : ∀ w : SrcFree, srcNode w ≠ v) :
    v = Sum.inr 5 ∨ v = Sum.inr 7 := by
  rcases v with i | f
  · exfalso
    have h : ∃ j : Fin 11, rawToCanon j = i := by fin_cases i <;> decide
    obtain ⟨j, hj⟩ := h
    exact hv (Sum.inl j) (by simp only [srcNode, hj])
  · by_contra h
    push_neg at h
    have h' : ∃ g : Fin 9, faceMap g = f := by
      revert h
      fin_cases f <;> decide
    obtain ⟨g, hg⟩ := h'
    exact hv (Sum.inr g) (by simp only [srcNode, hg])

/-! ## §2 reindexing the `Edge`-sum along `edgeMap` -/

/-- If α vanishes off the image of `edgeMap`, an `Edge`-sum reindexes to the `SourceEdge`-sum. -/
theorem sum_edge_eq_sum_sourceEdge {α : Edge → ℝ} {F : Edge → ℝ}
    (hzero : ∀ e : Edge, e ∉ Finset.univ.image edgeMap → α e = 0) :
    (∑ e : Edge, α e * F e) = ∑ s : SourceEdge, α (edgeMap s) * F (edgeMap s) := by
  rw [← Finset.sum_image (s := (Finset.univ : Finset SourceEdge)) (g := edgeMap)
    (f := fun e : Edge => α e * F e)
    (fun x _ y _ h => edgeMap_injective h)]
  exact (Finset.sum_subset (Finset.subset_univ _)
    (fun e _ he => by rw [hzero e he, zero_mul])).symm

/-- The α-vanishing hypothesis in the "faces 5 and 7" form. -/
theorem zero_off_image_of_slack {α : Edge → ℝ}
    (hzero : ∀ k : Fin 3, α (.inr (5, k)) = 0 ∧ α (.inr (7, k)) = 0) :
    ∀ e : Edge, e ∉ Finset.univ.image edgeMap → α e = 0 := by
  intro e he
  have hnot : ¬ ∃ s : SourceEdge, edgeMap s = e := by
    intro h
    obtain ⟨s, hs⟩ := h
    exact he (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, hs⟩)
  rcases e with ⟨i, s⟩ | ⟨f, k⟩
  · exact absurd ((edgeMap_image (.inl (i, s))).mpr trivial) hnot
  · have hf : ¬ (f ≠ 5 ∧ f ≠ 7) := fun h => hnot ((edgeMap_image (.inr (f, k))).mpr h)
    by_cases h5 : f = 5
    · subst h5; exact (hzero k).1
    · have h7 : f = 7 := by
        by_contra h7
        exact hf ⟨h5, h7⟩
      subst h7; exact (hzero k).2

/-! ## §3 the transport -/

/-- The source-side coefficient row: canonical anchor incidence along `edgeMap` plus the source
free-node part. -/
noncomputable def srcCoeff (hs : SrcFree → Fin 9 → ℝ) (s : SourceEdge) (j : Fin 9) : ℝ :=
  anchorIncidence (edgeMap s) j + ∑ z : SrcFree, srcInc s z * hs z j

/-- The source-side Gram (over the 45 source edges, pushed along `edgeMap`). -/
noncomputable def srcGram (α : Edge → ℝ) (K : SourceEdge → Fin 9 → ℝ) (i j : Fin 9) : ℝ :=
  ∑ s : SourceEdge, α (edgeMap s) * K s i * K s j

/-- The abstract small coefficient along `srcNode` is the source coefficient on `edgeMap`. -/
theorem activeCoeff_eq_srcCoeff (hs : SrcFree → Fin 9 → ℝ) (s : SourceEdge) (j : Fin 9) :
    edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs (edgeMap s) j
      = srcCoeff hs s j := by
  simp only [edgeCoeff, activeBlock, srcCoeff]
  congr 1
  exact Finset.sum_congr rfl (fun z _ => by rw [incidence_edgeMap_eq_srcInc])

/-- `gram` of the canonical coefficient is `response` of `coeff`. -/
theorem gram_canon_eq_response_coeff {α : Edge → ℝ} (H : Free → Fin 9 → ℝ) (i j : Fin 9) :
    gram α (edgeCoeff incidence anchorIncidence H) i j = response α (coeff H) i j := by
  simp only [gram, response]
  exact Finset.sum_congr rfl
    (fun e _ => by rw [NetworkSchurBinding.coeff_eq H e i, NetworkSchurBinding.coeff_eq H e j])

theorem gram_small_eq_srcGram {α : Edge → ℝ} {hs : SrcFree → Fin 9 → ℝ}
    (hzero : ∀ e : Edge, e ∉ Finset.univ.image edgeMap → α e = 0) (i j : Fin 9) :
    gram α (edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs) i j
      = srcGram α (srcCoeff hs) i j := by
  simp only [gram, srcGram]
  calc (∑ e : Edge, (α e * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e i)
        * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e j)
      = ∑ e : Edge, α e * (edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e i
          * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e j) :=
        Finset.sum_congr rfl (fun e _ => by ring)
    _ = ∑ s : SourceEdge, α (edgeMap s)
          * (edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs (edgeMap s) i
            * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs (edgeMap s) j) :=
        sum_edge_eq_sum_sourceEdge (α := α) (F := fun e =>
          edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e i
            * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e j) hzero
    _ = ∑ s : SourceEdge, (α (edgeMap s) * srcCoeff hs s i) * srcCoeff hs s j :=
        Finset.sum_congr rfl (fun s _ => by
          rw [activeCoeff_eq_srcCoeff hs s i, activeCoeff_eq_srcCoeff hs s j]
          ring)

/-- **The mapping transport.**  A source-side balance on the 20 free rows (with the source's own
incidence `srcInc`, specified against `srcEdgeV2`/`srcEdgeW2`) gives, for every extension `H` of the
20-row field `hs` along `srcNode`, the canonical 22-row `hbal` and the response identity — in
particular the response is independent of the two slack-auxiliary rows. -/
theorem src_balance_to_canonical {α : Edge → ℝ} {hs : SrcFree → Fin 9 → ℝ}
    (hzero : ∀ k : Fin 3, α (.inr (5, k)) = 0 ∧ α (.inr (7, k)) = 0)
    (hsrc : ∀ w j, ∑ s : SourceEdge, (α (edgeMap s) * srcInc s w) * srcCoeff hs s j = 0)
    {H : Free → Fin 9 → ℝ} (hH : ∀ w j, H (srcNode w) j = hs w j) :
    (∀ v j, ∑ e : Edge, (α e * incidence e v) * coeff H e j = 0) ∧
      (∀ i j, response α (coeff H) i j = srcGram α (srcCoeff hs) i j) := by
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
  have hbal_s : Balanced α (activeBlock incidence srcNode) anchorIncidence hs := by
    intro w j
    have hterm : ∀ e : Edge, (α e * activeBlock incidence srcNode e w)
        * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e j
        = α e * (incidence e (srcNode w)
          * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e j) := by
      intro e
      simp only [activeBlock]
      ring
    calc (∑ e : Edge, (α e * activeBlock incidence srcNode e w)
          * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e j)
        = ∑ e : Edge, α e * (incidence e (srcNode w)
            * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e j) :=
          Finset.sum_congr rfl (fun e _ => hterm e)
      _ = ∑ s : SourceEdge, α (edgeMap s) * (incidence (edgeMap s) (srcNode w)
            * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs (edgeMap s) j) :=
          sum_edge_eq_sum_sourceEdge (α := α) (F := fun e => incidence e (srcNode w)
            * edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs e j) hz
      _ = ∑ s : SourceEdge, (α (edgeMap s) * srcInc s w) * srcCoeff hs s j :=
          Finset.sum_congr rfl (fun s _ => by
            rw [activeCoeff_eq_srcCoeff hs s j, incidence_edgeMap_eq_srcInc]
            ring)
      _ = 0 := hsrc w j
  have hBal : Balanced α incidence anchorIncidence H :=
    balanced_extend_of_unused srcNode_injective hunused hbal_s hH
  constructor
  · intro v j
    have hb := hBal v j
    simpa only [NetworkSchurBinding.coeff_eq H] using hb
  · intro i j
    calc response α (coeff H) i j
        = gram α (edgeCoeff incidence anchorIncidence H) i j :=
          (gram_canon_eq_response_coeff H i j).symm
      _ = gram α (edgeCoeff (activeBlock incidence srcNode) anchorIncidence hs) i j :=
          gram_extend_eq (a := anchorIncidence) srcNode_injective hunused hH i j
      _ = srcGram α (srcCoeff hs) i j := gram_small_eq_srcGram hz i j

end N11Formalization.HarmonicSourceTransport

#print axioms N11Formalization.HarmonicSourceTransport.incidence_edgeMap_eq_srcInc
#print axioms N11Formalization.HarmonicSourceTransport.src_balance_to_canonical

set_option pp.explicit true
set_option pp.universes false

#check @N11Formalization.HarmonicSourceTransport.incidence_edgeMap_eq_srcInc
#check @N11Formalization.HarmonicSourceTransport.src_balance_to_canonical
