/-
n11-formalization — cline-six / harmonic-response (2026-09-30) — **V6, unbuilt draft**.

STATUS (byte-level evidence): gate1 on V1 (`…V1.lean`, sha BAF08EAA…): `rw [h2, zero_add] at h1`
recursion.  gate2 on V3 (`…V3.lean`, sha 6601C1AF…): L137:75 inside `hd`'s `congrArg` chain.
gate3 on V4 (`…V4.lean`, sha 01E353DC2FD3811FA63D001F630678388A315565D556035DAC6A010D9B5FB89A):
L133:26, max recursion depth while elaborating the term-mode `neg_eq_zero.mp (…)` — i.e. the
failure is defeq/typeclass work on the huge `Point`-valued sums, not the lambda form and not the
`hquad` simpa (which gate3 did not flag).  V6 therefore extracts SCALAR COORDINATES first:
`ext k`; `congrArg (fun p : Point => p k)` on h1/h2 (small lambda); `simp only
[PiLp.add_apply, PiLp.zero_apply]`; then `linarith` in ℝ.  No arithmetic is done on vectors.
No declaration, hypothesis or conclusion changed; scope comments (A1–A3 errata) retained;
`hquad` left untouched per Lead instruction (no concrete error reported there).

Scope: (a) the PER-EDGE zero-force geometry identity: any two zero-force configurations with the
same stress and boundary datum have equal edge vectors on every edge with α ≠ 0 (no connectivity,
no positivity of α on carrying edges, no pointwise statement about the source's centers (C,Z), and
no actual α instantiated); (b) a REAL consumer on the live leaf chain
(`FlashLocal.local_gain_actual_frobenius_leaf`) with the response/geometry interface discharged.

## What this file proves

§1 `arcEnd_eq_circleMap_rawAnchorAngle`
    The actual root anchor geometry `arcEnd u` IS the circle-map geometry `circleMap ∘
    rawAnchorAngle u` (definitional through `ResumeAnchorAngles.arcEnd_eq_rawAnchorAngle`), so
    the leaf chain's `hUeq` premise is a theorem at the actual root geometry.

§2 `edgeVector_eq_of_balance`, `flux_eq_of_balance`, `edgeLength_eq_of_balance`,
   `energy_eq_of_balance`
    **Zero-force configurations agree on every carrying edge (per-edge, α ≠ 0).**  Any two
    zero-force configurations with the same boundary datum and the same nonnegative stress have
    identical edge vectors — hence identical edge lengths, anchor fluxes and energies — on every
    edge with α ≠ 0.  This is a pure per-edge statement: it does NOT claim that the zero-stress
    freedom is exactly the source's two slack auxiliaries, does NOT claim the lift reproduces the
    source configuration pointwise, and instantiates no actual α; those would need carrying
    connectivity and α > 0 on the carrying edges.  (`ha` is the consumers' free-node force
    balance; it is the stationarity of the Dirichlet energy, so this is a genuine convexity
    statement, not a definition.)
    Proof: the difference d of two balanced configurations satisfies the linearised balance
    `A d = 0`, hence `∑_e α_e ‖edgeVector 0 d_e‖² = 0` by `ResumeDirichlet.cross_term_zero_of_balance`;
    nonnegative terms force `edgeVector 0 d_e = 0` on every α ≠ 0 edge.

§3 `response_premises_gram`
    The response triple of the consumers for the actual Gram `Λα := response α (coeff H)`:
    `hresp` from `hα + hbal`; **`hsym`/`hpsd` need only `hα`** (Gram form), which is strictly
    weaker than the shared-premise derivation in `SourceHInterfaceResume` (whose `hpsd` used
    `hbal` as well).

§4 `local_gain_leaf_source_response`
    The live leaf consumer, with `U := arcEnd u`, `θ := rawAnchorAngle u`,
    `Λα := response α (coeff H)`: `hresp`, `hsym`, `hpsd`, `hUeq` are no longer premises and
    `hfluxα` is stated on the ACTUAL root anchors (`flux α (arcEnd u) C Z i = ρ i • arcEnd u i`).
    Residual premises: source stress α ≥ 0 (source-stress), one balanced harmonic `H` with `hbal`
    (its existence is a theorem for every α ≥ 0 in the companion draft `HarmonicLiftExistence`,
    and the response matrix is independent of the representative), the actual geometry C/Z, the
    stress mapping N, and the numeric/interval certificates.

## Not claimed

No actual α construction, no radial flux identity, no Schur = Gram, no attainment / lower bound,
no root / shared edits.  `u : Fin 12 → ℝ` is arbitrary in every statement, so the exact source
root (`SourceExactRoot.sourceRoot`, once target-built) instantiates it with no extra work.
No sorry / custom axiom / native_decide.
-/
import Mathlib
import N11Formalization.FlashLocalFrobeniusLeaf
import N11Formalization.ResumeHarmonicResponse
import N11Formalization.ResumeResponseProperties
import N11Formalization.ResumeStressComparison
import N11Formalization.ResumeAnchorAngles
import N11Formalization.Geometry.ArcCovering

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.HarmonicResponseConsumer

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeDirichlet
open N11Formalization.ResumeHarmonic
open N11Formalization.ResumeResponseGram
open N11Formalization.ResumeAnchorFlux
open N11Formalization.ResumeStressComparison
open N11Formalization.FlashLocal

/-! ## §1 the actual root anchor geometry is the circle geometry -/

/-- The actual root anchor geometry `arcEnd u` is the circle map of the raw anchor angles.
This discharges the leaf chain's `hUeq` premise at the actual root. -/
theorem arcEnd_eq_circleMap_rawAnchorAngle (u : Fin 12 → ℝ) (i : Fin 9) :
    arcEnd u i = circleMap (rawAnchorAngle u i) := by
  rw [arcEnd_eq_rawAnchorAngle]
  rfl

/-! ## §2 source root geometry = harmonic lift on every carrying edge -/

/-- **Zero-force configurations with the same stress and boundary datum have equal edge vectors
on every edge with α ≠ 0.**  (Per-edge statement; the free block may be singular.  No
connectivity, no pointwise uniqueness of the configurations and no claim about slack auxiliaries
is made.) -/
theorem edgeVector_eq_of_balance {α : Edge → ℝ} {U : Fin 9 → Point}
    {C₁ Z₁ C₂ Z₂ : Fin 11 → Point}
    (hα : ∀ e, 0 ≤ α e)
    (h₁ : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C₁ Z₁ e = 0)
    (h₂ : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C₂ Z₂ e = 0) :
    ∀ e, α e ≠ 0 → edgeVector U C₁ Z₁ e = edgeVector U C₂ Z₂ e := by
  classical
  set dC : Fin 11 → Point := C₁ - C₂ with hdC
  set dZ : Fin 11 → Point := Z₁ - Z₂ with hdZ
  have hCdC : C₂ + dC = C₁ := by
    rw [hdC]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  have hZdZ : Z₂ + dZ = Z₁ := by
    rw [hdZ]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  have hsplit : ∀ e, edgeVector U C₁ Z₁ e
      = edgeVector U C₂ Z₂ e + edgeVector (fun _ : Fin 9 => (0 : Point)) dC dZ e := by
    intro e
    have h := edgeVector_shift (U := U) (C := C₂) (Z := Z₂) (dC := dC) (dZ := dZ) e
    rwa [hCdC, hZdZ] at h
  have hd : ∀ v : Free,
      ∑ e, (α e * incidence e v) • edgeVector (fun _ : Fin 9 => (0 : Point)) dC dZ e = 0 := by
    intro v
    have h1 := h₁ v
    have h2 := h₂ v
    simp only [hsplit, smul_add, Finset.sum_add_distrib] at h1
    -- Scalar-coordinate extraction: no defeq/typeclass work on the huge Point-valued sums.
    -- The lambda `p ↦ p k` is small; all arithmetic is then in ℝ.
    apply PiLp.ext
    intro k
    simp only [PiLp.zero_apply]
    have h1c := congrArg (fun p : Point => p k) h1
    have h2c := congrArg (fun p : Point => p k) h2
    simp only [PiLp.add_apply, PiLp.zero_apply] at h1c
    simp only [PiLp.zero_apply] at h2c
    linarith
  have hquad : ∑ e, α e * ‖edgeVector (fun _ : Fin 9 => (0 : Point)) dC dZ e‖ ^ 2 = 0 := by
    have h := cross_term_zero_of_balance α incidence
      (edgeVector (fun _ : Fin 9 => (0 : Point)) dC dZ) hd (Sum.elim dC dZ)
    simpa only [incidence_apply, real_inner_self_eq_norm_sq] using h
  have hterm : ∀ e, α e * ‖edgeVector (fun _ : Fin 9 => (0 : Point)) dC dZ e‖ ^ 2 = 0 := fun e =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => mul_nonneg (hα e) (sq_nonneg _))).mp hquad e
      (Finset.mem_univ e)
  intro e hae
  have hz := hterm e
  have hnorm : ‖edgeVector (fun _ : Fin 9 => (0 : Point)) dC dZ e‖ = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hae
    · have h2 : ‖edgeVector (fun _ : Fin 9 => (0 : Point)) dC dZ e‖
          * ‖edgeVector (fun _ : Fin 9 => (0 : Point)) dC dZ e‖ = 0 := by
        simpa [pow_two] using h
      exact mul_self_eq_zero.mp h2
  have hvec : edgeVector (fun _ : Fin 9 => (0 : Point)) dC dZ e = 0 := norm_eq_zero.mp hnorm
  rw [hsplit e, hvec, add_zero]

/-- **The source's anchor flux is reproduced by the harmonic lift**: a zero-force configuration
with stress α has the same anchor flux as any other zero-force configuration with the same
boundary datum. -/
theorem flux_eq_of_balance {α : Edge → ℝ} {U : Fin 9 → Point}
    {C₁ Z₁ C₂ Z₂ : Fin 11 → Point}
    (hα : ∀ e, 0 ≤ α e)
    (h₁ : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C₁ Z₁ e = 0)
    (h₂ : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C₂ Z₂ e = 0) :
    ∀ i, flux α U C₁ Z₁ i = flux α U C₂ Z₂ i := by
  intro i
  have hedge := edgeVector_eq_of_balance hα h₁ h₂
  unfold flux
  apply Finset.sum_congr rfl
  intro e _
  by_cases hae : α e = 0
  · simp [hae]
  · rw [hedge e hae]

/-- **Edge lengths are reproduced by the harmonic lift** on every edge with α ≠ 0. -/
theorem edgeLength_eq_of_balance {α : Edge → ℝ} {U : Fin 9 → Point}
    {C₁ Z₁ C₂ Z₂ : Fin 11 → Point}
    (hα : ∀ e, 0 ≤ α e)
    (h₁ : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C₁ Z₁ e = 0)
    (h₂ : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C₂ Z₂ e = 0) :
    ∀ e, α e ≠ 0 → edgeLength U C₁ Z₁ e = edgeLength U C₂ Z₂ e := by
  intro e hae
  have hedge := edgeVector_eq_of_balance hα h₁ h₂ e hae
  rw [edgeLength_eq_norm, edgeLength_eq_norm, hedge]

/-- **The weighted energy is reproduced by the harmonic lift** (zero-stress edges contribute 0
either way). -/
theorem energy_eq_of_balance {α : Edge → ℝ} {U : Fin 9 → Point}
    {C₁ Z₁ C₂ Z₂ : Fin 11 → Point}
    (hα : ∀ e, 0 ≤ α e)
    (h₁ : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C₁ Z₁ e = 0)
    (h₂ : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C₂ Z₂ e = 0) :
    energy α U C₁ Z₁ = energy α U C₂ Z₂ := by
  have hedge := edgeLength_eq_of_balance hα h₁ h₂
  unfold energy
  apply Finset.sum_congr rfl
  intro e _
  by_cases hae : α e = 0
  · simp [hae]
  · rw [hedge e hae]

/-! ## §3 response triple for the actual Gram (weaker hypotheses than the shared-premise form) -/

/-- Response-side premise triple for `Λα := response α (coeff H)`:
`hresp` needs `hα + hbal`; `hsym`/`hpsd` need only `hα` (both are Gram facts, no balance used). -/
theorem response_premises_gram (α : Edge → ℝ) (H : Free → Fin 9 → ℝ)
    (hα : ∀ e, 0 ≤ α e)
    (hbal : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0) :
    (∀ W : Fin 9 → Point, Eform (response α (coeff H)) W W = dirichletEnergy α W) ∧
      (∀ i j : Fin 9, response α (coeff H) i j = response α (coeff H) j i) ∧
      (∀ W : Fin 9 → Point, 0 ≤ Eform (response α (coeff H)) W W) :=
  ⟨fun W => ResumeHarmonicResponse.response_identity α H hα hbal W,
    fun i j => ResumeResponseProperties.response_symm α (coeff H) i j,
    fun W => ResumeResponseProperties.response_psd α (coeff H) hα W⟩

/-! ## §4 real consumer: the live leaf chain at the actual root geometry -/

/-- **Leaf consumer with the response side discharged and the actual root geometry wired in.**

Same conclusion as `FlashLocal.local_gain_actual_frobenius_leaf` with `U := arcEnd u`,
`θ := rawAnchorAngle u`, `Λα := response α (coeff H)`; the premises `hresp`, `hsym`, `hpsd`
and `hUeq` are gone, and `hfluxα` is stated on the actual root anchors
(`flux α (arcEnd u) C Z i = ρ i • arcEnd u i`). -/
theorem local_gain_leaf_source_response
    (u : Fin 12 → ℝ) {α : Edge → ℝ} {C Z : Fin 11 → Point}
    (x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ} (pidx : Fin 9) {Rstar : ℝ}
    (C8 : Matrix (Fin 8) (Fin 8) ℝ) (B8 : Fin 8 → Fin 8 → RatInterval) (η : ℚ)
    (hα : ∀ e, 0 ≤ α e) (H : Free → Fin 9 → ℝ)
    (hbal : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0)
    (hgFrob : ∑ k : Fin 8, ∑ a, (Gmat anchorIncidence (edgeVector (fun k => arcEnd u k) C Z)
        (fun k => circleTangent (rawAnchorAngle u k)) N (pidx.succAbove k) a) ^ 2
        ≤ (15363 / 1000000 : ℝ) ^ 2)
    (hrow : ∀ e, Real.sqrt (∑ a, (N e a) ^ 2) ≤ (99 / 200) * α e)
    (hNcol : ∀ a, ∑ e, N e a = 0)
    (hNbal : ∀ a v, ∑ e, (N e a * incidence e v) • edgeVector (fun k => arcEnd u k) C Z e = 0)
    (hs : ∑ e, α e = 1)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector (fun k => arcEnd u k) C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength (fun k => arcEnd u k) C Z e ^ 2 = Rstar ^ 2)
    (hdiag : ∀ j, anchorWeight α j ≤ 2 / 25)
    (hr : Real.sqrt (∑ i, x i ^ 2) ≤ 729 / 50000)
    (hpin : x pidx = 0)
    (hCfrob : ∑ i, ∑ j, (if i = pidx ∨ j = pidx then 0 else
        Cmat (response α (coeff H)) (fun k => rawAnchorAngle u k) i j) ^ 2
        ≤ (179 / 5000 : ℝ) ^ 2)
    (hFsq : ∑ a, (frob (flux (fun e => N e a) (fun k => arcEnd u k) C Z)) ^ 2
        ≤ (429 / 50000 : ℝ) ^ 2)
    (hρ : ∀ i, 0 ≤ ρ i)
    (hfluxα : ∀ i, flux α (fun k => arcEnd u k) C Z i = ρ i • arcEnd u i)
    (hη : 0 < η)
    (hmem : ∀ i j, RatInterval.Mem (B8 i j)
        (actualGram pidx (response α (coeff H)) ρ (fun k => rawAnchorAngle u k) N
          (fun k => arcEnd u k) C Z C8 i j))
    (hintrow : ∀ i, η + (∑ j, if j = i then 0 else (B8 i j).abs.hi) ≤ (B8 i i).lo) :
    (∑ i, x i ^ 2) / 100000
      ≤ V2 (fun k => arcEnd u k + disp (fun k => rawAnchorAngle u k) x k) - Rstar ^ 2 := by
  have hUeq : ∀ i, (fun k => arcEnd u k) i
      = circleMap ((fun k => rawAnchorAngle u k) i) :=
    fun i => arcEnd_eq_circleMap_rawAnchorAngle u i
  have hresp : ∀ W : Fin 9 → Point,
      Eform (response α (coeff H)) W W = dirichletEnergy α W :=
    fun W => ResumeHarmonicResponse.response_identity α H hα hbal W
  have hsym : ∀ i j, response α (coeff H) i j = response α (coeff H) j i :=
    fun i j => ResumeResponseProperties.response_symm α (coeff H) i j
  have hpsd : ∀ W : Fin 9 → Point, 0 ≤ Eform (response α (coeff H)) W W :=
    fun W => ResumeResponseProperties.response_psd α (coeff H) hα W
  have hfluxα' : ∀ i, flux α (fun k => arcEnd u k) C Z i
      = ρ i • circleMap (rawAnchorAngle u i) := by
    intro i
    rw [hfluxα i, arcEnd_eq_circleMap_rawAnchorAngle]
  exact local_gain_actual_frobenius_leaf (α := α) (U := fun k => arcEnd u k) (C := C) (Z := Z)
    (θ := fun k => rawAnchorAngle u k) x ρ (N := N) (Rstar := Rstar) pidx
    (Λα := response α (coeff H)) C8 B8 η hα hgFrob hrow hNcol hNbal hs ha hl hUeq hdiag hr
    hresp hpin hsym hpsd hCfrob hFsq hρ hfluxα' hη hmem hintrow

end N11Formalization.HarmonicResponseConsumer

#print axioms N11Formalization.HarmonicResponseConsumer.arcEnd_eq_circleMap_rawAnchorAngle
#print axioms N11Formalization.HarmonicResponseConsumer.edgeVector_eq_of_balance
#print axioms N11Formalization.HarmonicResponseConsumer.flux_eq_of_balance
#print axioms N11Formalization.HarmonicResponseConsumer.edgeLength_eq_of_balance
#print axioms N11Formalization.HarmonicResponseConsumer.energy_eq_of_balance
#print axioms N11Formalization.HarmonicResponseConsumer.response_premises_gram
#print axioms N11Formalization.HarmonicResponseConsumer.local_gain_leaf_source_response

set_option pp.explicit true
set_option pp.universes false

#check @N11Formalization.HarmonicResponseConsumer.edgeVector_eq_of_balance
#check @N11Formalization.HarmonicResponseConsumer.local_gain_leaf_source_response
