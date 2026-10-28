/-
n11-formalization — resume-attainment (Lead 2026-09-30) — **unbuilt draft**.

# `SourceAlphaOf` — concrete source stress `alphaOf` from μ/ν/η/β + positive-network reindex

## Naming map (index-displacement guard: the two source notes use OPPOSITE letters)

| role | this file | `TC-TO-PHYSICAL-KKT-LIFT.md` | `FIXED-SWITCH-SOC-REDUCTION.md` §5 / `FIXED-SWITCH-SHARPNESS…` §2 |
|---|---|---|---|
| face multipliers (9) | `mu` | μ = −λ (orbit split) | ν_f |
| tie multipliers (9) | `nu` | ν (odd-cycle output, `OddCycleStress.nuOf w`) | μ_i |
| face conversion | `c` | c_i = 4 y_i² / F_out,i > 0 | (folded into ν_f) |
| tie conversion | `b` | b_j = a_{R,j} + a_{R,j+1} > 0 | (folded into μ_i) |
| tie split | `eta` | — | η = s_d/(s_d − s_c) |
| face barycentrics | `beta` | — | β_{f s}, Σ_s β_{f s} = 1 |

Physical weights: face = `mu·c` (`faceWeight`), tie = `nu·b` (`tieWeight`).  This is TC-LIFT L39;
SHARPNESS's normalized μ_i/ν_f are exactly these physical weights.

## Edges (source list ↔ `SourceEdge` ↔ formal `Edge`)

`SourceEdge = (Fin 9 × Fin 2) ⊕ (Fin 9 × Fin 3)` (45 = 18 spokes + 27 active-face edges):
* `.inl (k,0)` = source edge `(9+k, k)`     : centre C_k — anchor U_k;
* `.inl (k,1)` = source edge `(9+(k+1)%9,k)`: centre C_{k+1} — anchor U_k;
* `.inr (j,v)` = source edge `(9+sourceFaces j v, 20+j)`: centre — face-j circumcentre.
Formal graph `ResumeNetwork.Edge = (Fin 9 × Fin 2) ⊕ (Fin 11 × Fin 3)`; canonical faces 5 and 7 are
the two slack faces and are **not** in the image of `ResumeLocalIncidence.edgeMap` (existing lemma
`edgeMap_image`).  Tie orientation: the split `eta k` is attached to the `c = C_k` side (source §5
labels the tie between `c,d` at `U`; this file pins that reading with the calibrated identity below).

## What this file contains

* `faceWeight`, `tieWeight` — physical weights from multipliers and conversions;
* `alphaOf` — the concrete 45-value stress from `(mu, nu, c, b, eta, beta)`;
* `alphaEdge` — zero extension to the 51-edge formal graph along `edgeMap` (the C909
  positive-network reindex), with `alphaEdge_edgeMap`, `alphaEdge_of_not_mem`, `alphaEdge_slack`;
* one **calibrated actual edge identity** (`alphaEdge_calibration_spoke_zero`: source list position 0
  = spoke C_0–U_0 ↔ canonical `.inl (7,1)`, value `tieWeight nu b 0 * eta 0`) and its face analogue;
  the remaining 43/45 cases are deliberately NOT expanded;
* `PositiveCarrying` and `ForceInterface` — the UNPAID positivity / force interfaces, retained
  explicitly and assumed nowhere.

## Reused generic proofs (NOT reproduced here)

* `ResumeHarmonic.balance_of_columns` : scalar balance ⇒ vector balance (for any `α : Edge → ℝ`);
* `ResumeHarmonicResponse.response_identity` : `hresp` from `hα` + scalar balance;
* `ResumeHarmonic.harmonic_energy_le_oracle` : `α` + `H` + balance ⇒ oracle lower bound;
* (outside this file) `ResumeHarmonicExtension.response_identity`, `SourceSchurGramResume.response_eq_schur`.
`alphaEdge` is literally the `α : Edge → ℝ` input of all of them.

## Source paths / hashes

* `team-current/lead/interval_network_envelope.py` sha256
  `5E76A529D436344A629991A95A43B04FF06C7D5FAF32E2DBE210B750E5074B83` (edges L28–30; B/T L47–54; solve L64–66)
* `team-current/lead/FIXED-SWITCH-SOC-REDUCTION.md` sha256
  `F78AD87A7DD210930F525546B863517FB987B674EBCAD34EB704B5A8CB584789` (§5 μ/ν/β/η lift)
* `team-current/lead/FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md` sha256
  `A9EA5C488906480D422373B8B70393B24FBA39F87395531683BDE3E2332D5C68` (§2 45 carrying edges, radiality)
* `lean/N11Formalization/ResumeLocalIncidence.lean` sha256
  `5E61DBEF8F141A8965524E08508EE799280632D2418B8F3433E8CFF83433BFD8` (`edgeMap`/`edgeMap_image`/`faceMap_exact`/`sourceLength_eq`)
* C909 (claim, `proved-interval`): 18 endpoint edges + 27 active-triangle edges positive, 6 slack zero.

## Status

UNBUILT (Lead owns the serial slot).  The `u`-level wiring is
`alphaOf u := alphaOf (muOf u) (nuOf (wOf u)) (cOf u) (bOf u) (etaOf u) (betaOf u)`; the five source
maps `muOf/wOf/cOf/bOf/etaOf/betaOf` are still UNPAID and are therefore NOT faked here.
-/
import Mathlib
import N11Formalization.ResumeLocalIncidence
import N11Formalization.ResumeNetwork
import N11Formalization.ResumeDirichlet
import N11Formalization.ResumeAnchorFlux
import N11Formalization.ResumeHarmonicResponse

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.SourceAlphaOf

open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeDirichlet
open N11Formalization.ResumeLocalIncidence

noncomputable section

/-- TC-LIFT face multipliers `mu = -lambda` times the face conversion `c`; equals SHARPNESS's
normalized face weight `nu_f`. -/
def faceWeight (mu c : Fin 9 → ℝ) : Fin 9 → ℝ := fun j => mu j * c j

/-- TC-LIFT tie multipliers `nu` (the odd-cycle output) times the tie conversion `b`; equals
SHARPNESS's normalized tie weight `mu_i`. -/
def tieWeight (nu b : Fin 9 → ℝ) : Fin 9 → ℝ := fun j => nu j * b j

/-- **The concrete source stress `alphaOf`** on the 45 carrying edges (full type per spoke/face
index): tie split `eta` on the two spokes of each anchor, face barycentrics `beta` on the three
edges of each active face. -/
def alphaOf (mu nu c b eta : Fin 9 → ℝ) (beta : Fin 9 → Fin 3 → ℝ) : SourceEdge → ℝ
  | .inl (k, s) => tieWeight nu b k * (if s = 0 then eta k else 1 - eta k)
  | .inr (j, v) => faceWeight mu c j * beta j v

/-! ## §1 index-explicit value lemmas (spoke k=0 side / spoke k=1 side / face) -/

theorem alphaOf_spoke_zero (mu nu c b eta : Fin 9 → ℝ) (beta : Fin 9 → Fin 3 → ℝ) (k : Fin 9) :
    alphaOf mu nu c b eta beta (.inl (k, (0 : Fin 2))) = tieWeight nu b k * eta k := by
  simp [alphaOf, tieWeight]

theorem alphaOf_spoke_one (mu nu c b eta : Fin 9 → ℝ) (beta : Fin 9 → Fin 3 → ℝ) (k : Fin 9) :
    alphaOf mu nu c b eta beta (.inl (k, (1 : Fin 2))) = tieWeight nu b k * (1 - eta k) := by
  have h : ¬ ((1 : Fin 2) = 0) := by decide
  simp only [alphaOf, if_neg h]

theorem alphaOf_face (mu nu c b eta : Fin 9 → ℝ) (beta : Fin 9 → Fin 3 → ℝ) (j : Fin 9) (v : Fin 3) :
    alphaOf mu nu c b eta beta (.inr (j, v)) = faceWeight mu c j * beta j v := by
  simp only [alphaOf]

/-! ## §2 positive-network reindex to the formal 51-edge graph -/

/-- The C909 positive carrying network reindexed along `ResumeLocalIncidence.edgeMap`: the value on
the (unique) preimage of a formal edge, and `0` on the six slack edges (canonical faces 5 and 7). -/
noncomputable def alphaEdge (α : SourceEdge → ℝ) : Edge → ℝ :=
  fun e => if h : ∃ s : SourceEdge, edgeMap s = e then α (Classical.choose h) else 0

/-- **Fundamental reindex identity**: on the image of `edgeMap` the extension agrees with the
source stress (uses the existing injectivity lemma). -/
theorem alphaEdge_edgeMap (α : SourceEdge → ℝ) (s : SourceEdge) :
    alphaEdge α (edgeMap s) = α s := by
  classical
  unfold alphaEdge
  split_ifs with h
  · have hs : Classical.choose h = s :=
      edgeMap_injective (Classical.choose_spec h)
    rw [hs]
  · exact False.elim (h ⟨s, rfl⟩)

/-- Off the image (`h`) the extension is `0`. -/
theorem alphaEdge_of_not_mem (α : SourceEdge → ℝ) {e : Edge}
    (h : ¬ ∃ s : SourceEdge, edgeMap s = e) : alphaEdge α e = 0 := by
  simp only [alphaEdge, dif_neg h]

/-- **The six slack edges carry zero stress** (canonical faces 5 and 7; uses `edgeMap_image`). -/
theorem alphaEdge_slack (α : SourceEdge → ℝ) {f : Fin 11} (hf : f = 5 ∨ f = 7) (v : Fin 3) :
    alphaEdge α (.inr (f, v)) = 0 := by
  have hno : ¬ ∃ s : SourceEdge, edgeMap s = (.inr (f, v) : Edge) := by
    rintro ⟨s, hs⟩
    have him := (edgeMap_image (.inr (f, v))).1 ⟨s, hs⟩
    rcases hf with rfl | rfl
    · exact him.1 rfl
    · exact him.2 rfl
  exact alphaEdge_of_not_mem α hno

theorem alphaEdge_slack_five (α : SourceEdge → ℝ) (v : Fin 3) :
    alphaEdge α (.inr ((5 : Fin 11), v)) = 0 :=
  alphaEdge_slack α (Or.inl rfl) v

theorem alphaEdge_slack_seven (α : SourceEdge → ℝ) (v : Fin 3) :
    alphaEdge α (.inr ((7 : Fin 11), v)) = 0 :=
  alphaEdge_slack α (Or.inr rfl) v

/-! ## §3 one calibrated actual edge identity per class (no 44/45 enumeration) -/

/-- Index guard (spoke): source list position 0 is `(9+0, 0)` = spoke C_0–U_0 = `.inl (0,0)`;
it lands at canonical `.inl (7,1)` (canonical labels: centre `siteMap 0 = 7`, anchor `7`). -/
theorem edgeMap_spoke_zero :
    edgeMap ((.inl ((0 : Fin 9), (0 : Fin 2))) : SourceEdge)
      = (Sum.inl (((7 : Fin 9), (1 : Fin 2))) : Edge) := by decide

/-- **Calibrated actual edge identity (spoke)** — source list position 0 carries the value
`tieWeight nu b 0 * eta 0` in the formal graph at `.inl (7,1)`. -/
theorem alphaEdge_calibration_spoke_zero (mu nu c b eta : Fin 9 → ℝ) (beta : Fin 9 → Fin 3 → ℝ) :
    alphaEdge (alphaOf mu nu c b eta beta) (Sum.inl (((7 : Fin 9), (1 : Fin 2))) : Edge)
      = tieWeight nu b 0 * eta 0 := by
  rw [← edgeMap_spoke_zero, alphaEdge_edgeMap, alphaOf_spoke_zero]

/-- Index guard (face): source face 0 vertex 0 = `.inr (0,0)`; `faceMap 0 = 9`. -/
theorem edgeMap_face_zero :
    edgeMap ((.inr ((0 : Fin 9), (0 : Fin 3))) : SourceEdge)
      = (Sum.inr (((9 : Fin 11), (0 : Fin 3))) : Edge) := by decide

/-- **Calibrated actual edge identity (face)** — source face 0, vertex 0 carries
`faceWeight mu c 0 * beta 0 0` at canonical `.inr (9,0)`. -/
theorem alphaEdge_calibration_face_zero (mu nu c b eta : Fin 9 → ℝ) (beta : Fin 9 → Fin 3 → ℝ) :
    alphaEdge (alphaOf mu nu c b eta beta) (Sum.inr (((9 : Fin 11), (0 : Fin 3))) : Edge)
      = faceWeight mu c 0 * beta 0 0 := by
  rw [← edgeMap_face_zero, alphaEdge_edgeMap, alphaOf_face]

/-! ## §4 positivity transport and unpaid interfaces -/

/-- Positivity of every source carrying edge from explicit factor signs. This is only a
parameterized algebraic consumer; it does not construct factors at the TC root. -/
theorem alphaOf_pos_of
    (mu nu c b eta : Fin 9 → ℝ) (beta : Fin 9 → Fin 3 → ℝ)
    (hface : ∀ j, 0 < mu j * c j)
    (htie : ∀ j, 0 < nu j * b j)
    (heta : ∀ j, 0 < eta j ∧ eta j < 1)
    (hbeta : ∀ j v, 0 < beta j v) :
    ∀ s : SourceEdge, 0 < alphaOf mu nu c b eta beta s := by
  intro s
  rcases s with ⟨k, q⟩ | ⟨j, v⟩
  · fin_cases q
    · simp only [alphaOf, ite_true]
      exact mul_pos (htie k) (heta k).1
    · have hq : ¬ ((1 : Fin 2) = 0) := by decide
      simp only [alphaOf, hq]
      exact mul_pos (htie k) (sub_pos.mpr (heta k).2)
  · simp only [alphaOf]
    exact mul_pos (hface j) (hbeta j v)

/-- Nonnegativity of every source carrying edge from nonnegative factor signs. -/
theorem alphaOf_nonneg_of
    (mu nu c b eta : Fin 9 → ℝ) (beta : Fin 9 → Fin 3 → ℝ)
    (hface : ∀ j, 0 ≤ mu j * c j)
    (htie : ∀ j, 0 ≤ nu j * b j)
    (heta : ∀ j, 0 ≤ eta j ∧ eta j ≤ 1)
    (hbeta : ∀ j v, 0 ≤ beta j v) :
    ∀ s : SourceEdge, 0 ≤ alphaOf mu nu c b eta beta s := by
  intro s
  rcases s with ⟨k, q⟩ | ⟨j, v⟩
  · fin_cases q
    · simp only [alphaOf]
      exact mul_nonneg (htie k) (heta k).1
    · have hq : ¬ ((1 : Fin 2) = 0) := by decide
      simp only [alphaOf, hq]
      exact mul_nonneg (htie k) (sub_nonneg.mpr (heta k).2)
  · simp only [alphaOf]
    exact mul_nonneg (hface j) (hbeta j v)

/-- The zero extension is nonnegative whenever the source carrying stress is nonnegative. -/
theorem alphaEdge_nonneg_of (α : SourceEdge → ℝ)
    (hα : ∀ s, 0 ≤ α s) : ∀ e : Edge, 0 ≤ alphaEdge α e := by
  intro e
  classical
  unfold alphaEdge
  split_ifs with h
  · exact hα _
  · exact le_rfl

/-! Root-level positivity, force balance and flux remain explicit unpaid interfaces. -/

/-- **UNPAID** (C897/C909 interval at the exact root): every carrying edge stress is positive. -/
def PositiveCarrying (α : SourceEdge → ℝ) : Prop := ∀ s : SourceEdge, 0 < α s

/-- **UNPAID** (C909 force interface): zero divergence at every free node and a strictly outward
radial anchor load, for the actual geometry.  This is the source-side content of C1540's
`hbal`/`hflux`; it is not proved here. -/
def ForceInterface (α : Edge → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point) : Prop :=
  (∀ v : Free, ∑ e : Edge, (α e * incidence e v) • edgeVector U C Z e = 0) ∧
    (∀ i : Fin 9, ∃ ρ : ℝ, 0 < ρ ∧ ResumeAnchorFlux.flux α U C Z i = ρ • U i)

end

end N11Formalization.SourceAlphaOf

#print axioms N11Formalization.SourceAlphaOf.alphaOf_spoke_zero
#print axioms N11Formalization.SourceAlphaOf.alphaOf_spoke_one
#print axioms N11Formalization.SourceAlphaOf.alphaOf_face
#print axioms N11Formalization.SourceAlphaOf.alphaEdge_edgeMap
#print axioms N11Formalization.SourceAlphaOf.alphaEdge_of_not_mem
#print axioms N11Formalization.SourceAlphaOf.alphaEdge_slack
#print axioms N11Formalization.SourceAlphaOf.edgeMap_spoke_zero
#print axioms N11Formalization.SourceAlphaOf.alphaEdge_calibration_spoke_zero
#print axioms N11Formalization.SourceAlphaOf.edgeMap_face_zero
#print axioms N11Formalization.SourceAlphaOf.alphaEdge_calibration_face_zero

set_option pp.explicit true
set_option pp.universes false

#check @N11Formalization.SourceAlphaOf.alphaOf
#check @N11Formalization.SourceAlphaOf.alphaEdge
#check @N11Formalization.SourceAlphaOf.alphaEdge_calibration_spoke_zero
#check @N11Formalization.SourceAlphaOf.alphaEdge_slack
-- Reused generic proofs (no duplication here):
#check @N11Formalization.ResumeHarmonic.balance_of_columns
#check @N11Formalization.ResumeHarmonicResponse.response_identity
#check @N11Formalization.ResumeHarmonic.harmonic_energy_le_oracle
#check @N11Formalization.ResumeAnchorFlux.flux
