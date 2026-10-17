/-
n11-formalization — cline-six / harmonic-response (2026-10-01) — **unbuilt draft (new filename V3)**.

STATUS: NOT KERNEL-CHECKED.  Lead owns the serial gate.

Gate history.  V2 (sha 164C44A8BD02B523A99607A8EF6518CCF73468B5F09B879EC250ACFAF5740F16, archived
byte-exactly as `HarmonicUnusedExtension.V2.lean`) was gated once, red
(`lead/unused-extension-gate2.log`), with exactly ONE error site: L257, the second conjunct of
`canonical_hbal_of_small`.  The goal there is `response α (coeff H) i j = response α (smallCoeffC h)
i j`, i.e. after unfolding it carries `coeff H e i`, `coeff H e j`; the simp set of V2 used
`NetworkSchurBinding.coeff_eq H` in the direction `edgeCoeff … ↦ coeff H`, so `hg` unfolded to the
`anchorIncidence + ∑ incidence · H` form while the goal kept `coeff H` — type mismatch.  V3 uses
the REVERSE direction `← NetworkSchurBinding.coeff_eq H`, which rewrites the goal's `coeff H e j`
to `edgeCoeff incidence anchorIncidence H e j`; both sides then unfold to the same normal form.
(For contrast the first conjunct uses the forward direction, correctly, because there the
hypothesis `hBal v j` is already in `edgeCoeff` form and the goal in `coeff` form.)
No statement, hypothesis or conclusion changed by this fix.

Gate history (V1).  V1 (live path `HarmonicUnusedExtension.lean`, sha
AE6F6B15E31816D71F259F01CADB859509F3525BA62FAA9034AFFAB1FDBA008C, archived byte-exactly as
`HarmonicUnusedExtension.V1.lean`) was gated once, red (`lead/unused-extension-gate1.log`), with
exactly three error sites and no others:
  * `faceMap_not_image` L167 (x9): `fin_cases f <;> decide` — `decide` decides only the goal and
    never reads the local hypothesis `hf`; fixed here by `revert hf` first, so `decide` sees the
    whole closed proposition `(∀ g, faceMap g ≠ f) → f = 5 ∨ f = 7` in each of the 11 cases;
  * `incidence_unused_eq_zero` L185: the witness proof `by rw [hg]` had goal
    `activeCanon (Sum.inr g) = Sum.inr f` (no syntactic occurrence of `faceMap g`); fixed by
    `show Sum.inr (faceMap g) = Sum.inr f` before the rewrite;
  * `canonical_hbal_of_small` L218: the implicit anchor map `a` of `gram_extend_eq` cannot be
    inferred from the explicit arguments; fixed by `(a := anchorIncidence)`.
`linter.unusedSectionVars` is also switched off (V1 emitted the "omit [Fintype E] [Fintype J]"
note).  No statement, hypothesis or conclusion changed by those fixes.

Structural obligation (Lead 2026-10-01): the generic exact-matrix theorem for the elimination /
extension between the source "small" free-node system (20 rows) and the canonical 22-row free
system, the two extra rows being the zero-slack auxiliaries (faces 5, 7).

## Contents

§1 abstract layer (over the Lead-green module `LaplacianSchurBridge`, NOT reproved):
   `activeBlock B active e w = B e (active w)` is the restriction of the large incidence to the
   active rows.  With `active : Vs → Vl` injective and every non-active node having zero incidence
   on every edge with α ≠ 0:
   * `edgeCoeff_extend_eq` — on each edge with α ≠ 0 the large edge-coefficient equals the small
     one, for ANY extension `H` of `h` (`H (active w) = h w`): the non-active rows drop out of the
     incidence sum;
   * `balanced_extend_of_unused` — a small balanced solve extends to a large balanced solve,
     with arbitrary values on the unused rows;
   * `gram_extend_eq` — the Gram/response of the large coefficient matrix equals the Gram of the
     small one: it is INDEPENDENT of the unused rows.

§2 concrete canonical instantiation:
   `activeCanon : Fin 11 ⊕ Fin 9 → Free`, `inl i ↦ inl i`, `inr f ↦ inr (faceMap f)` (the
   source's 11 centres + 9 face centres into the canonical 22 rows).  `faceMap_not_image` shows
   the unused rows are exactly `inr 5`, `inr 7`; `incidence_unused_eq_zero` shows they have zero
   incidence on every edge with α ≠ 0 provided α vanishes on the six slack face edges of faces 5
   and 7 (the source's weighted zero omissions).
   `canonical_hbal_of_small` combines both: a balance on the 20 active rows (with the restricted
   incidence and the small coefficient) gives C1540's `hbal` for the canonical 22-row coefficient
   matrix, and the canonical `response α (coeff H)` equals the response of the 20-row object —
   for every extension of `h`.

Reused, not reproved: `LaplacianSchurBridge` blocks/`Balanced`/`gram`, and
`NetworkSchurBinding.coeff_eq` (the Lead-green bridge `edgeCoeff incidence anchorIncidence H =
coeff H`, with the live chain's `ResumeAnchorFlux.anchorIncidence` convention).
`HarmonicLiftExistence.response_eq_of_hbal` (balanced-representative independence) is NOT invoked
here because §1 proves the sharper statement directly.
NOT done here (source-stress / local-sharp interface): transporting the source's 45-edge
`srcB`/balance along `ResumeLocalIncidence.edgeMap` into the 20-row `activeBlock` balance, and the
actual α construction.  `ResumeLocalIncidence.edgeMap_image` says exactly which six canonical face
edges (faces 5, 7) are omitted; the `hzero` hypothesis below is that those six carry α = 0.

Interface data received from local-sharp (2026-10-01, kernel-green on their side, C1603/C1608):
the injective `ResumeLocalIncidence.edgeMap` with image = all 51 edges minus the six face edges of
faces 5 and 7; free nodes source `(Fin 11) ⊕ (Fin 9)` -> canonical `(Fin 11) ⊕ (Fin 11)` with the
two extra rows exactly faces 5 and 7; the exact maps `faceMap = ![9,10,8,0,1,2,3,4,6]`,
`siteMap k = k - 2`, `rawOfRing`, `rawToCanon`; the aux-point identities
`canonFaceZ u (faceMap f) = sourceAuxZ u f`, and the length transport
`FlashRootNetwork.edgeLength_edgeMap_eq_sourceLength`.  THIS FILE reads none of those objects
except `faceMap` (via `activeCanon`); in particular it does not read `srcB`.

WARNING (from local-sharp, affects any instantiation of `hbal_small`):
`FlashLocalFrobeniusSourceN.srcFaceSite : Fin 27 → Fin 9` has its literals 9/10 folded mod into
0/1, so 11 of its 27 slots are wrong; `srcZ`, `srcEdgeV` and the 27 face-edge columns of `srcB` are
polluted (125 entries, max|Δ| ≈ 1.21), while `srcB u 0 0` and the `T` rows are unaffected.  The
20-row balance fed to `hbal_small` must therefore be rebuilt from the corrected `sourceFaces`
(Fin 11 values, as in `ResumeLocalIncidence.sourceFaces` / `faceMap_exact`), or wait for the source
table fix — do NOT take those face columns from the polluted `srcB`.

No sorry / custom axiom / native_decide.
-/
import Mathlib
import N11Formalization.LaplacianSchurBridge
import N11Formalization.NetworkSchurBinding
import N11Formalization.ResumeNetwork
import N11Formalization.ResumeDirichlet
import N11Formalization.ResumeHarmonic
import N11Formalization.ResumeResponseGram
import N11Formalization.ResumeAnchorFlux
import N11Formalization.ResumeLocalIncidence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace N11Formalization.HarmonicUnusedExtension

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeDirichlet
open N11Formalization.ResumeHarmonic
open N11Formalization.ResumeResponseGram
open N11Formalization.ResumeAnchorFlux
open N11Formalization.ResumeLocalIncidence
open N11Formalization.LaplacianSchurBridge
open N11Formalization.NetworkSchurBinding

/-! ## §1 abstract extension / elimination -/

variable {E Vl Vs J : Type*} [Fintype E] [Fintype Vl] [Fintype Vs] [Fintype J] [DecidableEq Vl]

/-- The small incidence block: the large incidence restricted to the active rows. -/
def activeBlock (B : E → Vl → ℝ) (active : Vs → Vl) : E → Vs → ℝ :=
  fun e w => B e (active w)

/-- **Edge-coefficient transfer.**  On an edge with α ≠ 0, the large expansion of any extension of
`h` equals the small expansion, because the non-active rows have zero incidence there. -/
theorem edgeCoeff_extend_eq {α : E → ℝ} {B : E → Vl → ℝ} {a : E → J → ℝ} {active : Vs → Vl}
    (hactive : Function.Injective active)
    (hunused : ∀ e, α e ≠ 0 → ∀ v : Vl, (∀ w : Vs, active w ≠ v) → B e v = 0)
    {h : Vs → J → ℝ} {H : Vl → J → ℝ} (hH : ∀ w j, H (active w) j = h w j)
    {e : E} {j : J} (hae : α e ≠ 0) :
    edgeCoeff B a H e j = edgeCoeff (activeBlock B active) a h e j := by
  simp only [edgeCoeff, activeBlock]
  congr 1
  have hzero : ∀ v ∈ (Finset.univ : Finset Vl), v ∉ Finset.univ.image active →
      B e v * H v j = 0 := by
    intro v _ hv
    have hva : ∀ w : Vs, active w ≠ v := by
      intro w hw
      exact hv (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, hw⟩)
    rw [hunused e hae v hva, zero_mul]
  calc ∑ v : Vl, B e v * H v j
      = ∑ v ∈ (Finset.univ : Finset Vl), B e v * H v j := rfl
    _ = ∑ v ∈ (Finset.univ.image active), B e v * H v j :=
          (Finset.sum_subset (Finset.subset_univ _) hzero).symm
    _ = ∑ w : Vs, B e (active w) * H (active w) j := by
          rw [Finset.sum_image]
          intro x _ y _ hxy
          exact hactive hxy
    _ = ∑ w : Vs, B e (active w) * h w j := by
          apply Finset.sum_congr rfl
          intro w _
          rw [hH w j]

/-- **Extension of a small balanced solve.**  If `h` balances the active rows (with the restricted
incidence and the small coefficient), then ANY extension `H` of `h` balances the full system. -/
theorem balanced_extend_of_unused {α : E → ℝ} {B : E → Vl → ℝ} {a : E → J → ℝ} {active : Vs → Vl}
    (hactive : Function.Injective active)
    (hunused : ∀ e, α e ≠ 0 → ∀ v : Vl, (∀ w : Vs, active w ≠ v) → B e v = 0)
    {h : Vs → J → ℝ} (hbal_s : Balanced α (activeBlock B active) a h)
    {H : Vl → J → ℝ} (hH : ∀ w j, H (active w) j = h w j) :
    Balanced α B a H := by
  intro v j
  by_cases hv : ∃ w : Vs, active w = v
  · obtain ⟨w, rfl⟩ := hv
    calc ∑ e, (α e * B e (active w)) * edgeCoeff B a H e j
        = ∑ e, (α e * B e (active w)) * edgeCoeff (activeBlock B active) a h e j := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases hae : α e = 0
          · simp [hae]
          · rw [edgeCoeff_extend_eq hactive hunused hH hae]
      _ = 0 := hbal_s w j
  · have hv' : ∀ w : Vs, active w ≠ v := by
      intro w hw
      exact hv ⟨w, hw⟩
    apply Finset.sum_eq_zero
    intro e _
    by_cases hae : α e = 0
    · simp [hae]
    · rw [hunused e hae v hv', mul_zero, zero_mul]

/-- **Gram independence of the unused rows.**  The Gram of the large coefficient matrix equals the
Gram of the small one; in particular two extensions of the same `h` have the same response. -/
theorem gram_extend_eq {α : E → ℝ} {B : E → Vl → ℝ} {a : E → J → ℝ} {active : Vs → Vl}
    (hactive : Function.Injective active)
    (hunused : ∀ e, α e ≠ 0 → ∀ v : Vl, (∀ w : Vs, active w ≠ v) → B e v = 0)
    {h : Vs → J → ℝ} {H : Vl → J → ℝ} (hH : ∀ w j, H (active w) j = h w j) (i j : J) :
    gram α (edgeCoeff B a H) i j = gram α (edgeCoeff (activeBlock B active) a h) i j := by
  simp only [gram]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hae : α e = 0
  · simp [hae]
  · rw [edgeCoeff_extend_eq (j := i) hactive hunused hH hae,
      edgeCoeff_extend_eq (j := j) hactive hunused hH hae]

/-! ## §2 concrete canonical instantiation (20 source rows → 22 canonical rows) -/

/-- The source's 20 free rows inside the canonical 22: centres into sites, face centres into the
face auxiliaries `inr (faceMap f)` (faces 5 and 7 are omitted by `faceMap`). -/
def activeCanon : (Fin 11 ⊕ Fin 9) → Free
  | Sum.inl i => Sum.inl i
  | Sum.inr f => Sum.inr (faceMap f)

theorem activeCanon_injective : Function.Injective activeCanon := by decide

/-- The rows outside the image of `activeCanon` are exactly the two slack auxiliaries 5 and 7.
The hypothesis is put back into the goal before case-splitting, so that `decide` sees the whole
closed proposition (it does not use local hypotheses). -/
theorem faceMap_not_image (f : Fin 11) (hf : ∀ g : Fin 9, faceMap g ≠ f) :
    f = 5 ∨ f = 7 := by
  revert hf
  fin_cases f <;> decide

/-- **The canonical small coefficient** on 20 rows (`coeff` with the incidence restricted to the
active rows). -/
noncomputable def smallCoeffC (h : (Fin 11 ⊕ Fin 9) → Fin 9 → ℝ) (e : Edge) (j : Fin 9) : ℝ :=
  anchorIncidence e j + ∑ z : Fin 11 ⊕ Fin 9, incidence e (activeCanon z) * h z j

/-- Zero incidence of the two slack auxiliaries on every edge with α ≠ 0, assuming α vanishes on
the six face edges of faces 5 and 7. -/
theorem incidence_unused_eq_zero {α : Edge → ℝ}
    (hzero : ∀ f : Fin 11, (f = 5 ∨ f = 7) → ∀ k : Fin 3, α (.inr (f, k)) = 0)
    {e : Edge} (hae : α e ≠ 0) {v : Free}
    (hv : ∀ w : Fin 11 ⊕ Fin 9, activeCanon w ≠ v) : incidence e v = 0 := by
  rcases v with i | f
  · exact absurd rfl (hv (Sum.inl i))
  · rcases e with ⟨k, s⟩ | ⟨f', k⟩
    · simp [incidence, Sum.inr_ne_inl]
    · have hf : f = 5 ∨ f = 7 :=
        faceMap_not_image f (fun g hg => hv (Sum.inr g) (by
          show Sum.inr (faceMap g) = Sum.inr f
          rw [hg]))
      by_cases h : f = f'
      · have hz : α (.inr (f', k)) = 0 := by
          rw [← h]
          exact hzero f hf k
        exact absurd hz hae
      · simp [incidence, h, Sum.inr_ne_inl]

/-- **Canonical extension theorem.**  If α vanishes on the six slack face edges (faces 5 and 7)
and `h` balances the 20 active rows with the canonical restricted incidence and `smallCoeffC`,
then every extension `H` of `h` to the 22 canonical rows satisfies C1540's `hbal`, and the
canonical response `response α (coeff H)` equals the response of the 20-row coefficient matrix —
independently of the two slack-auxiliary values. -/
theorem canonical_hbal_of_small {α : Edge → ℝ}
    (hzero : ∀ f : Fin 11, (f = 5 ∨ f = 7) → ∀ k : Fin 3, α (.inr (f, k)) = 0)
    {h : (Fin 11 ⊕ Fin 9) → Fin 9 → ℝ}
    (hbal_small : ∀ w j, ∑ e, (α e * incidence e (activeCanon w)) * smallCoeffC h e j = 0)
    {H : Free → Fin 9 → ℝ} (hH : ∀ w j, H (activeCanon w) j = h w j) :
    (∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0) ∧
      (∀ i j, response α (coeff H) i j = response α (smallCoeffC h) i j) := by
  have hunused : ∀ e, α e ≠ 0 → ∀ v : Free,
      (∀ w : Fin 11 ⊕ Fin 9, activeCanon w ≠ v) → incidence e v = 0 :=
    fun e hae v hv => incidence_unused_eq_zero hzero hae hv
  have hbal_s : Balanced α (activeBlock incidence activeCanon) anchorIncidence h := by
    intro w j
    exact hbal_small w j
  have hBal : Balanced α incidence anchorIncidence H :=
    balanced_extend_of_unused activeCanon_injective hunused hbal_s hH
  constructor
  · intro v j
    have hb := hBal v j
    simpa only [NetworkSchurBinding.coeff_eq H] using hb
  · intro i j
    have hg := gram_extend_eq (a := anchorIncidence) activeCanon_injective hunused hH i j
    -- gate2 (V2, L257) fixed: the goal carries `coeff H`, whose unfolded form never appears in
    -- `hg`, so the bridge must be used in the direction `coeff H e j ↦ edgeCoeff … e j`
    -- (`← NetworkSchurBinding.coeff_eq H`); then both sides unfold to the same normal form.
    simpa only [gram, response, edgeCoeff, activeBlock, smallCoeffC,
      ← NetworkSchurBinding.coeff_eq H] using hg

end N11Formalization.HarmonicUnusedExtension

#print axioms N11Formalization.HarmonicUnusedExtension.edgeCoeff_extend_eq
#print axioms N11Formalization.HarmonicUnusedExtension.balanced_extend_of_unused
#print axioms N11Formalization.HarmonicUnusedExtension.gram_extend_eq
#print axioms N11Formalization.HarmonicUnusedExtension.canonical_hbal_of_small

set_option pp.explicit true
set_option pp.universes false

#check @N11Formalization.HarmonicUnusedExtension.balanced_extend_of_unused
#check @N11Formalization.HarmonicUnusedExtension.canonical_hbal_of_small
