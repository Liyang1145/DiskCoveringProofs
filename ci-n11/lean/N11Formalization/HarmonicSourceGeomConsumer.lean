/-
n11-formalization — restart-20261001 / harmonic — **FROZEN DRAFT, NOT kernel-checked**.

Write scope: `evidence/restart-20261001/harmonic/` only.  Lead owns the serial gate; nothing here
counts as `proved` until Lead's gate log reads `exit 0 / 0 error / 0 warning / sorryAx = 0` bound to
this file's sha256.

## What this file is

Supersedes `evidence/cline-six-20260930/harmonic-response/HarmonicSourceGeomConsumer.lean`
(sha256 `4D455F1F9BC529E24FD972C7A66783075F25A9D348F8D8B8DFEBA6B7853D8AA9` — the recorded
"thin wrapper 4D455F1F…"), whose gate
`evidence/cline-six-20260930/lead/source-geom-consumer-gate1.log` was **exit 1 with three errors**.

No green definition is deleted, renamed or rewritten.  Used as-is, byte-for-byte:

| module | sha256 | role |
|---|---|---|
| `HarmonicSourceGeometry.lean` (V9, ns `HarmonicSourceGeometryV2`) | `70A7FA2BE66B6E8A146A4607ABD5DEE1FBBD424EEF3EC655F8A1F4A6D004EF39` | geometry consumer (carries `hEV` as an hypothesis) |
| `SourceN2GeomFlat.lean` | `B54C2D807CBD61C8C6C22F5536AB378ABCC13E2E10C29D61B66D923F1C23DC7C` | `hEV_srcEdge` (C1659), `srcEdgeOf_srcFlat`, `srcFlat` |
| `SourceN2GeomEdge.lean` | `EEDC171E8166D29542638D7616F1A6A6154F1153A590AFF11C6B02DF78B781E1` | flat-45 `srcEdgeVec` |
| `HarmonicSourceTransport.lean` | `3F9BB7A142E683452D932D2CADFDD8C7AC3E0A849065C5BE938B47A31D865C0F` | `SrcFree`, `srcNode29`, `srcFlat` |
| `SourceN2.lean` | `65AD189D15C1CFF914244EF482B1F2A49A621F8F4C2B6F307FEFB95940C791A9` | `srcB2` (41×45) |

### The three gate1 errors and their fixes

1. `L62:42` — `HarmonicSourceGeometryV2.srcEdgeVec` is a function of a **`SourceEdge`**
   (`HarmonicSourceGeometry.lean:70`), *not* of a `Fin 45`; so the old bridge
   `… u e = SourceN2GeomEdge.srcEdgeVec u e` with `e : Fin 45` is ill-typed.  Correct bridge (§1),
   exactly as specified:
   `∀ s : SourceEdge, HarmonicSourceGeometryV2.srcEdgeVec u s
    = SourceN2GeomEdge.srcEdgeVec u (srcFlat s)`,
   proved by `rfl` after the two-constructor split: both bodies are
   `srcX2 u (srcEdgeV2 ·) − srcX2 u (srcEdgeW2 ·)` over the *same* `srcFlat`.
2. `L75:46` — the same type error inside `hEV_discharged` (`srcFlat s : Fin 45` fed where a
   `SourceEdge` was expected).  Fixed in §2 by `srcEdgeVec_eq` together with `srcFlat_eq` (the
   transport and geometry-flat `srcFlat`s are definitionally the same map), then
   `SourceN2GeomFlat.hEV_srcEdge`.
3. `L87:35` — `rowIdx` was used unqualified while it lives in namespace
   `N11Formalization.HarmonicSourceGeometryV2`.  Fixed by **full qualification**
   (`HarmonicSourceGeometryV2.rowIdx`).  This file deliberately does **not** `open` that namespace,
   so no other declaration of the geometry module leaks in unqualified.

## Contents

§1 `srcFlat_eq`, `srcEdgeVec_eq` — the two definitional bridges.
§2 `hEV_discharged` — the geometric identity in exactly the shape
   `canonical_free_balance_of_source_geom` consumes, obtained from the kernel-green
   `SourceN2GeomFlat.hEV_srcEdge`.
§3 `exists_lift_of_source_B2force` — the thin consumer, **no `hEV` premise**.
§4 `rowLift`, `rowLift_ne_mass`, `rowIdx40`, `rowIdx40_inl_val` / `rowIdx40_inr_val`,
   `rowIdx40_injective`, `rowIdx40_surjective`, `rowIdx40_bijective`, `rowLift_rowIdx40`,
   `b2_rows_iff_fin40` — the kernel binding showing the enumeration `rowIdx` covers the source's
   **original `Fin 40` non-mass rows of `srcB2`** exactly once.  Deliberately **not** a second
   existence theorem: the `Fin 40` form of the consumer is one line,
   `exists_lift_of_source_B2force hα hzero ((b2_rows_iff_fin40).mp hrows40)`.

## Full type of the consumer (every premise explicit; no implicit binder beyond `α`, `u`)

For `α : Edge → ℝ` and `u : Fin 12 → ℝ`:

* `hα    : ∀ e : Edge, 0 ≤ α e` — nonnegative stress;
* `hzero : ∀ k : Fin 3, α (.inr (5, k)) = 0 ∧ α (.inr (7, k)) = 0` — α vanishes on the six slack
  face edges (faces 5 and 7);
* `hrows : ∀ w : SrcFree, ∀ c : Fin 2,
    ∑ s : SourceEdge, srcB2 u (HarmonicSourceGeometryV2.rowIdx w c) (srcFlat s) * α (edgeMap s) = 0`
  — the 40 actual `srcB2` force rows at the actual root; by §4 *equivalent* to the source's original
  enumeration `∀ i : Fin 40, ∑ s, srcB2 u (rowLift i) (srcFlat s) * α (edgeMap s) = 0`
  (`(b2_rows_iff_fin40).mp` / `.mpr`);

⊢ `∃ H : Free → Fin 9 → ℝ` such that

  1. `∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0` — balanced;
  2. `∀ W : Fin 9 → Point, energy α W (fun i => lift H W (.inl i)) (fun f => lift H W (.inr f))
     = dirichletEnergy α W` — minimises for **every** boundary datum;
  3. `∀ i, flux α (canonAnchors u) (lift…) i
     = flux α (canonAnchors u) (canonCenters u) (canonFaceZ u) i` — reproduces the actual anchor flux;
  4. `energy α (canonAnchors u) (lift…) = energy α (canonAnchors u) (canonCenters u) (canonFaceZ u)`
     — reproduces the actual weighted energy.

`H` is *produced* (kernel-green `HarmonicReproduceActualV2.exists_lift_reproducing_actual`, reached
via `HarmonicSourceGeometryV2.exists_lift_of_source_geom`); it is never assumed and is **never**
identified with the centres' coordinates.

## Not claimed

* the actual `α` and its derivation from the actual root's stationarity / KKT: `hα`, `hzero`, `hrows`
  remain **premises** here and are not derived in this file;
* `hflux` / radiality, `Schur = Gram`, attainment, any lower bound, and the original
  **unrestricted n = 11** target (still a gap);
* "`H` equals the centre/hub coordinates" in any form.

No `sorry` / custom axiom / `native_decide`.
-/

import Mathlib
import N11Formalization.SourceN2
import N11Formalization.SourceN2GeomFlat
import N11Formalization.SourceN2GeomEdge
import N11Formalization.HarmonicSourceGeometry
import N11Formalization.HarmonicSourceTransport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace N11Formalization.HarmonicSourceGeomConsumer

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeDirichlet
open N11Formalization.ResumeHarmonic
open N11Formalization.ResumeAnchorFlux
open N11Formalization.ResumeLocalIncidence
open N11Formalization.FlashRootNetwork
open N11Formalization.LocalSharpAuxZ
open N11Formalization.SourceN2
open N11Formalization.HarmonicSourceTransport

/-! ## §1 definitional bridges -/

/-- The transport's `srcFlat` and the geometry-flat module's `srcFlat` are the **same map**:
`(k, s) ↦ spokeFlat k s` on the spokes and `(j, t) ↦ faceFlatEdge j t` on the face edges (the flat
module writes those two `Fin 45` literals out; the `Fin` proof components are definitionally
irrelevant).  No green definition is touched. -/
theorem srcFlat_eq (s : SourceEdge) :
    SourceN2GeomFlat.srcFlat s = srcFlat s := by
  rcases s with ⟨k, s'⟩ | ⟨j, t⟩ <;> rfl

/-- **The bridge gate1 got wrong.**  The geometry module's `srcEdgeVec` is indexed by a
`SourceEdge`; the flat module's is indexed by `Fin 45`.  They agree after `srcFlat`.  Proof is `rfl`
in both cases: the bodies are literally the same expression once the index is identified. -/
theorem srcEdgeVec_eq (u : Fin 12 → ℝ) (s : SourceEdge) :
    HarmonicSourceGeometryV2.srcEdgeVec u s
      = SourceN2GeomEdge.srcEdgeVec u (srcFlat s) := by
  rcases s with ⟨k, s'⟩ | ⟨j, t⟩ <;> rfl

/-! ## §2 the geometric identity, discharged -/

/-- **`hEV` discharged**: the geometric identity in exactly the shape used by
`HarmonicSourceGeometryV2.canonical_free_balance_of_source_geom`, obtained from the kernel-green
`SourceN2GeomFlat.hEV_srcEdge` (C1659) through `srcEdgeVec_eq` and `srcFlat_eq`.  No `hEV` premise
survives.  (Owner of the geometry side: local-sharp; this file only wires it.) -/
theorem hEV_discharged (u : Fin 12 → ℝ) (s : SourceEdge) :
    edgeVector (canonAnchors u) (canonCenters u) (canonFaceZ u) (edgeMap s)
      = HarmonicSourceGeometryV2.srcEdgeVec u s := by
  rw [srcEdgeVec_eq u s, ← srcFlat_eq s]
  exact (SourceN2GeomFlat.hEV_srcEdge u s).symm

/-! ## §3 the thin B2force consumer (no `hEV` premise) -/

/-- **Source-B2force consumer.**  Nonnegative `α` vanishing on the six slack face edges (faces 5
and 7), plus the **40 actual `srcB2` force rows** at the actual root, give a balanced `H` whose lift
minimises for **every** boundary datum and reproduces the actual anchor flux and weighted energy.

Relative to `HarmonicSourceGeometryV2.exists_lift_of_source_geom` the only change is that its `hEV`
hypothesis is discharged (§2).  `H` is produced by the kernel-green C1628 chain — not assumed, and
not identified with the centres' coordinates. -/
theorem exists_lift_of_source_B2force {α : Edge → ℝ} {u : Fin 12 → ℝ}
    (hα : ∀ e : Edge, 0 ≤ α e)
    (hzero : ∀ k : Fin 3, α (.inr (5, k)) = 0 ∧ α (.inr (7, k)) = 0)
    (hrows : ∀ w : SrcFree, ∀ c : Fin 2,
        ∑ s : SourceEdge, srcB2 u (HarmonicSourceGeometryV2.rowIdx w c) (srcFlat s)
          * α (edgeMap s) = 0) :
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
        = energy α (canonAnchors u) (canonCenters u) (canonFaceZ u) :=
  HarmonicSourceGeometryV2.exists_lift_of_source_geom hα hzero (hEV_discharged u) hrows

/-! ## §4 binding the enumeration `rowIdx` to the source's original 40 rows

`srcB2 : Fin 41 → Fin 45 → ℝ` has 41 rows: rows `2*(node − 9) + c` for the twenty free nodes
`9 … 28` — namely `2j + c` (`j < 11`, the centres) and `22 + 2f + c` (`f < 9`, the face auxiliaries),
i.e. rows `0 … 39` — plus the mass row `40` (identically `1`).  The geometry consumer indexes the
force rows by `SrcFree × Fin 2` through `rowIdx`.  Below, the same rows are re-indexed by the
source's own `Fin 40` and the enumeration is proved **injective and surjective**: the 40 rows it
names are the source's 40 non-mass rows, each exactly once, and row `40` is never named.

The value lemmas are proved by unfolding `rowIdx` / `srcNode29` on constructor arguments plus
`omega` (the same instrument the green `rowIdx_div` / `rowIdx_mod` / `rowIdx_ne_mass` use), so
`rowIdx` and `srcB2` are never re-derived here. -/

/-- The source's original `srcB2` rows `0 … 39`, as elements of `Fin 41`. -/
def rowLift (i : Fin 40) : Fin 41 := ⟨(i : ℕ), by omega⟩

/-- `rowLift` never names the mass row `40`. -/
theorem rowLift_ne_mass (i : Fin 40) : ((rowLift i : Fin 41) : ℕ) ≠ 40 := by
  have hi : (i : ℕ) < 40 := i.isLt
  simp only [rowLift, Fin.val_mk]
  omega

/-- The enumeration `rowIdx`, its (non-mass) row number read as an element of the source's own
`Fin 40`.  Both obligations are non-geometric: the ambient bound `rowIdx … < 41` and the green
`rowIdx_ne_mass`. -/
def rowIdx40 (w : SrcFree) (c : Fin 2) : Fin 40 :=
  ⟨((HarmonicSourceGeometryV2.rowIdx w c : Fin 41) : ℕ), by
    have hne : ((HarmonicSourceGeometryV2.rowIdx w c : Fin 41) : ℕ) ≠ 40 :=
      HarmonicSourceGeometryV2.rowIdx_ne_mass w c
    have hlt : ((HarmonicSourceGeometryV2.rowIdx w c : Fin 41) : ℕ) < 41 :=
      (HarmonicSourceGeometryV2.rowIdx w c : Fin 41).isLt
    omega⟩

/-- Row value on the eleven centre rows: `2j + c`. -/
theorem rowIdx40_inl_val (j : Fin 11) (c : Fin 2) :
    ((rowIdx40 (Sum.inl j) c : Fin 40) : ℕ) = 2 * (j : ℕ) + (c : ℕ) := by
  simp only [rowIdx40, HarmonicSourceGeometryV2.rowIdx, srcNode29, Fin.val_mk]
  omega

/-- Row value on the nine face-auxiliary rows: `22 + 2f + c`. -/
theorem rowIdx40_inr_val (f : Fin 9) (c : Fin 2) :
    ((rowIdx40 (Sum.inr f) c : Fin 40) : ℕ) = 22 + 2 * (f : ℕ) + (c : ℕ) := by
  simp only [rowIdx40, HarmonicSourceGeometryV2.rowIdx, srcNode29, Fin.val_mk]
  omega

/-- `rowLift` and the enumeration agree on the row: the `Fin 40` row number of `rowIdx` **is** its
`Fin 41` row number, so `rowLift` puts the two indexings on the same source row.  This is what lets
the two hypothesis shapes be interchanged. -/
theorem rowLift_rowIdx40 (w : SrcFree) (c : Fin 2) :
    rowLift (rowIdx40 w c) = HarmonicSourceGeometryV2.rowIdx w c := by
  apply Fin.ext
  rfl

/-- **No two of the 40 enumeration entries name the same source row.**  The two halves are separated
by `2 * 10 + 1 = 21 < 22`. -/
theorem rowIdx40_injective :
    Function.Injective (fun x : SrcFree × Fin 2 => rowIdx40 x.1 x.2) := by
  rintro ⟨w, c⟩ ⟨w', c'⟩ h
  have hc : (c : ℕ) < 2 := c.isLt
  have hc' : (c' : ℕ) < 2 := c'.isLt
  have hv : ((rowIdx40 w c : Fin 40) : ℕ) = ((rowIdx40 w' c' : Fin 40) : ℕ) :=
    congrArg Fin.val h
  rcases w with j | f <;> rcases w' with j' | f'
  · have hj : (j : ℕ) < 11 := j.isLt
    have hj' : (j' : ℕ) < 11 := j'.isLt
    rw [rowIdx40_inl_val, rowIdx40_inl_val] at hv
    have hjj : j = j' := Fin.ext (by omega)
    have hcc : c = c' := Fin.ext (by omega)
    rw [hjj, hcc]
  · have hj : (j : ℕ) < 11 := j.isLt
    have hf' : (f' : ℕ) < 9 := f'.isLt
    rw [rowIdx40_inl_val, rowIdx40_inr_val] at hv
    exfalso
    omega
  · have hf : (f : ℕ) < 9 := f.isLt
    have hj' : (j' : ℕ) < 11 := j'.isLt
    rw [rowIdx40_inr_val, rowIdx40_inl_val] at hv
    exfalso
    omega
  · have hf : (f : ℕ) < 9 := f.isLt
    have hf' : (f' : ℕ) < 9 := f'.isLt
    rw [rowIdx40_inr_val, rowIdx40_inr_val] at hv
    have hff : f = f' := Fin.ext (by omega)
    have hcc : c = c' := Fin.ext (by omega)
    rw [hff, hcc]

/-- **Every one of the 40 source rows is named by the enumeration** — explicit preimage by quotient
and remainder by `2` in each half (`0 … 21` from the centres, `22 … 39` from the auxiliaries). -/
theorem rowIdx40_surjective :
    Function.Surjective (fun x : SrcFree × Fin 2 => rowIdx40 x.1 x.2) := by
  intro i
  have hi : (i : ℕ) < 40 := i.isLt
  by_cases h : (i : ℕ) < 22
  · refine ⟨(Sum.inl ⟨(i : ℕ) / 2, by omega⟩, ⟨(i : ℕ) % 2, by omega⟩), ?_⟩
    apply Fin.ext
    rw [rowIdx40_inl_val]
    simp only [Fin.val_mk]
    omega
  · have hge : 22 ≤ (i : ℕ) := by omega
    refine ⟨(Sum.inr ⟨((i : ℕ) - 22) / 2, by omega⟩, ⟨((i : ℕ) - 22) % 2, by omega⟩), ?_⟩
    apply Fin.ext
    rw [rowIdx40_inr_val]
    simp only [Fin.val_mk]
    omega

/-- **The enumeration is a bijection onto the source's original 40 rows.** -/
theorem rowIdx40_bijective :
    Function.Bijective (fun x : SrcFree × Fin 2 => rowIdx40 x.1 x.2) :=
  ⟨rowIdx40_injective, rowIdx40_surjective⟩

/-- **The binding.**  The source's original 40 `srcB2` force rows (`∀ i : Fin 40`) vanish **iff**
the `SrcFree × Fin 2` shape consumed by §3 vanishes.  Nothing is reproved: this is
`rowIdx40_surjective` (for ⇐) and `rowLift_rowIdx40` (for ⇒) transported through the sum. -/
theorem b2_rows_iff_fin40 {α : Edge → ℝ} {u : Fin 12 → ℝ} :
    (∀ i : Fin 40,
        ∑ s : SourceEdge, srcB2 u (rowLift i) (srcFlat s) * α (edgeMap s) = 0)
      ↔ (∀ w : SrcFree, ∀ c : Fin 2,
          ∑ s : SourceEdge, srcB2 u (HarmonicSourceGeometryV2.rowIdx w c) (srcFlat s)
            * α (edgeMap s) = 0) := by
  constructor
  · intro h w c
    have hw := h (rowIdx40 w c)
    rwa [rowLift_rowIdx40 w c] at hw
  · intro h i
    obtain ⟨⟨w, c⟩, hwc⟩ := rowIdx40_surjective i
    have hwc' : rowIdx40 w c = i := hwc
    rw [← hwc', rowLift_rowIdx40 w c]
    exact h w c

end N11Formalization.HarmonicSourceGeomConsumer

#print axioms N11Formalization.HarmonicSourceGeomConsumer.srcFlat_eq
#print axioms N11Formalization.HarmonicSourceGeomConsumer.srcEdgeVec_eq
#print axioms N11Formalization.HarmonicSourceGeomConsumer.hEV_discharged
#print axioms N11Formalization.HarmonicSourceGeomConsumer.exists_lift_of_source_B2force
#print axioms N11Formalization.HarmonicSourceGeomConsumer.rowIdx40_bijective
#print axioms N11Formalization.HarmonicSourceGeomConsumer.b2_rows_iff_fin40

