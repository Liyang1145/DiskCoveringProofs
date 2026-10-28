/-
n11-formalization — cline-six / harmonic-response (2026-09-30) — **V3, gate2-fixed draft**.

STATUS: gate2 compiled V2 (sha256 8304D2231739EE334A7456FF7DFE0C35B5F42DCC59A51143348BA3ECED45E118,
preserved as `HarmonicLiftExistence.V2.lean`) with exactly ONE error — a redundant trailing `ring`
at L251:22 ("No goals to be solved": the preceding `rw [hc_eq e]` had already closed the goal) —
and with all seven `#print axioms` already reporting the standard axioms
`[propext, Classical.choice, Quot.sound]`.  V3 deletes that one stray tactic; declarations,
hypotheses and proofs are otherwise byte-identical to V2.  V3 itself awaits its own serial gate
(source bytes changed).

History (comments only): V1 (gate1 exit1) is preserved as `HarmonicLiftExistence.V1.lean`
(sha256 2C637360241DD2539253A5BFFDD7112C2119ED6362D67DCB098DCD43D0DBB570); the V1 → V2 pass
applied only these tactic/notation fixes, with no proposition change:
  * bare `⟪,⟫` notation replaced by explicit `inner ℝ ...` (three sites; the notation is scoped
    and was not open, which produced the L110 "expected token" error and the `sorryAx`
    cascade in `horth`/`hstat`);
  * `map_smul'`: added `RingHom.id_apply` to the simp set (goal kept `(RingHom.id ℝ) c`);
  * `harmonic_columns_exist`: replaced the wrong-direction `rw` by an explicit sum-equality
    proved termwise with `ring`;
  * `coeff_eq_of_hbal.hc_eq`: added `mul_sub` + `Finset.sum_sub_distrib` before `ring`;
  * `coeff_eq_of_hbal.hquad`: the `hswap` calc was restructured so each `simp_rw [Finset.mul_sum]`
    sees the intended side only (V1 rewrote both sides and then failed to find the pattern);
  * `hterm`: `(…).mp hquad` returns `∀ i ∈ univ, …`; wrapped as a function of `e`;
  * closing step: `rw [← hc]` was replaced by the explicit `hce : c e₀ = …` bridge;
  * `anchorIncidence_bridge`: dropped the redundant `norm_num` in the first branch (the `rw`
    already closed the goal; V1 reported "No goals to be solved").

Scope (unchanged): the harmonic-lift EXISTENCE side of the source-H interface — the direction
that `SourceHInterfaceResume`/C1540 leaves as a premise (`hbal`).

§1 `exists_ls_stationary_minimizer` — least-squares normal equations exist for any finite
   weighted edge functional with α ≥ 0, via orthogonal projection onto the range of the
   √α-weighted incidence map; no inverse, no positive-definiteness, singular free blocks allowed.
§2 `harmonic_columns_exist`, `harmonic_lift_exists` — for every α ≥ 0 there is `H` with C1540's
   `hbal`, and its lift attains the Dirichlet minimum for every boundary datum.
§3 `coeff_eq_of_hbal`, `response_eq_of_hbal` — the response/Gram matrix is independent of the
   chosen balanced `H` (only positive-weight edges matter).
§4 `energy_lift_eq_Eform` — the lifted geometry's Dirichlet energy equals the formal response
   form `Eform (response α (coeff H)) U U`.  NOTE: this is the energy of the LIFT, not a claim
   that the source's actual centers/Z equal the lift.  The related geometric identity (zero-force
   configurations agree per edge, only where α ≠ 0; no connectivity, no pointwise centers claim)
   is `HarmonicResponseConsumer.edgeVector_eq_of_balance`.
§5 `anchorIncidence_bridge` — the two `anchorIncidence` conventions are propositionally, not
   definitionally, equal.

Not claimed: no actual α construction, no radial flux identity, no Schur = Gram, no attainment /
lower bound, no root or shared edits.  No sorry / custom axiom / native_decide.
-/
import Mathlib
import N11Formalization.ResumeNetwork
import N11Formalization.ResumeDirichlet
import N11Formalization.ResumeHarmonic
import N11Formalization.ResumeResponseGram
import N11Formalization.ResumeResponseProperties
import N11Formalization.ResumeAnchorFlux
import N11Formalization.FlashResponseHessianFlux

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.HarmonicLiftExistence

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeDirichlet
open N11Formalization.ResumeHarmonic
open N11Formalization.ResumeResponseGram
open N11Formalization.ResumeAnchorFlux (anchorIncidence flux)
open N11Formalization.FlashLocal

/-! ## §1 least-squares normal equations exist (nonnegative weights, singular allowed) -/

/-- For any finite edge system, any linear edge functional `B : Edge → V → ℝ` and any `α ≥ 0`,
the normal equations of `h ↦ ∑_e α_e (β_e + ∑_w B_ew h_w)^2` admit a solution, and that solution
is a global minimizer of that weighted sum of squares.  Proof: orthogonal projection of `-β'`
onto `LinearMap.range` of the √α-weighted incidence map; the free block is never inverted and may
be singular. -/
theorem exists_ls_stationary_minimizer {V : Type*} [Fintype V]
    (B : Edge → V → ℝ) (β α : Edge → ℝ) (hα : ∀ e, 0 ≤ α e) :
    ∃ h : V → ℝ,
      (∀ v, ∑ e, α e * (β e + ∑ w, B e w * h w) * B e v = 0) ∧
      (∀ y : V → ℝ, ∑ e, α e * (β e + ∑ w, B e w * h w) ^ 2
        ≤ ∑ e, α e * (β e + ∑ w, B e w * y w) ^ 2) := by
  classical
  let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ Edge :=
    { toFun := fun x => WithLp.toLp 2 (fun e => Real.sqrt (α e) * ∑ w, B e w * x w)
      map_add' := by
        intro x y
        ext e
        simp only [PiLp.add_apply, WithLp.ofLp_toLp, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext e
        simp only [PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul, RingHom.id_apply]
        have hsum : (∑ w, B e w * (c * x w)) = c * ∑ w, B e w * x w := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [hsum]
        ring }
  let β' : EuclideanSpace ℝ Edge := WithLp.toLp 2 (fun e => Real.sqrt (α e) * β e)
  let K : Submodule ℝ (EuclideanSpace ℝ Edge) := LinearMap.range T
  haveI : FiniteDimensional ℝ ↥K := LinearMap.finiteDimensional_range T
  haveI : CompleteSpace ↥K := FiniteDimensional.complete ℝ ↥K
  haveI : K.HasOrthogonalProjection := inferInstance
  let p : EuclideanSpace ℝ Edge := K.starProjection (-β')
  have hpK : p ∈ K := K.starProjection_apply_mem (-β')
  have hpR : p ∈ LinearMap.range T := hpK
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hpR
  have horth : ∀ w ∈ K, inner ℝ ((-β') - p) w = 0 :=
    fun w hw => K.starProjection_inner_eq_zero (-β') w hw
  have hstat : ∀ d : EuclideanSpace ℝ V, inner ℝ (p + β') (T d) = 0 := by
    intro d
    have h := horth (T d) (LinearMap.mem_range_self T d)
    have hneg : p + β' = -((-β') - p) := by abel
    rw [hneg, inner_neg_left, h, neg_zero]
  have hA : ∀ e, (T x + β') e = Real.sqrt (α e) * (β e + ∑ w, B e w * x w) := by
    intro e
    change Real.sqrt (α e) * (∑ w, B e w * x w) + Real.sqrt (α e) * β e
      = Real.sqrt (α e) * (β e + ∑ w, B e w * x w)
    ring
  have hnorm : ∀ y : EuclideanSpace ℝ V,
      ‖T y + β'‖ * ‖T y + β'‖ = ∑ e, α e * (β e + ∑ w, B e w * y w) ^ 2 := by
    intro y
    rw [← sq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro e _
    have h1 : (T y + β') e = Real.sqrt (α e) * (β e + ∑ w, B e w * y w) := by
      change Real.sqrt (α e) * (∑ w, B e w * y w) + Real.sqrt (α e) * β e
        = Real.sqrt (α e) * (β e + ∑ w, B e w * y w)
      ring
    rw [h1, mul_pow, Real.sq_sqrt (hα e)]
  have hmin : ∀ y : EuclideanSpace ℝ V,
      ‖p + β'‖ * ‖p + β'‖ ≤ ‖T y + β'‖ * ‖T y + β'‖ := by
    intro y
    have hzero : inner ℝ (T y - p) (p + β') = 0 := by
      have h := horth (T y - p) (K.sub_mem (LinearMap.mem_range_self T y) hpK)
      have hneg : p + β' = -((-β') - p) := by abel
      rw [real_inner_comm, hneg, inner_neg_left, h, neg_zero]
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (T y - p) (p + β') hzero
    rw [show (T y - p) + (p + β') = T y + β' by abel] at hpy
    have hnn : 0 ≤ ‖T y - p‖ * ‖T y - p‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith
  have hminSum : ∀ Y : EuclideanSpace ℝ V,
      (∑ e, α e * (β e + ∑ w, B e w * x w) ^ 2)
        ≤ ∑ e, α e * (β e + ∑ w, B e w * Y w) ^ 2 := by
    intro Y
    have h := hmin Y
    rw [← hx] at h
    rw [hnorm x, hnorm Y] at h
    exact h
  refine ⟨fun w => x w, ?_, ?_⟩
  · intro v
    have hd := hstat (EuclideanSpace.single v (1 : ℝ))
    rw [← hx] at hd
    rw [PiLp.inner_apply] at hd
    simp only [Real.inner_apply] at hd
    have hB : ∀ e, (T (EuclideanSpace.single v (1 : ℝ))) e = Real.sqrt (α e) * B e v := by
      intro e
      change Real.sqrt (α e) * (∑ w, B e w * (EuclideanSpace.single v (1 : ℝ)) w)
        = Real.sqrt (α e) * B e v
      rw [Finset.sum_eq_single v]
      · simp [EuclideanSpace.single_apply]
      · intro w _ hwv
        simp [EuclideanSpace.single_apply, hwv]
      · intro hv
        exact absurd (Finset.mem_univ v) hv
    simp only [hA, hB] at hd
    have hterm : ∀ e, (Real.sqrt (α e) * (β e + ∑ w, B e w * x w)) * (Real.sqrt (α e) * B e v)
        = α e * (β e + ∑ w, B e w * x w) * B e v := by
      intro e
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (hα e)]
      ring
    rw [Finset.sum_congr rfl (fun e _ => hterm e)] at hd
    simpa using hd
  · intro y
    simpa using hminSum (WithLp.toLp 2 y)

/-! ## §2 existence of balanced harmonic columns and of the minimizing lift -/

/-- **`hbal` is satisfiable for every nonnegative stress**: there is a scalar matrix `H` whose
columns are the free-node harmonic extensions of the nine boundary indicators.  Column `j` is
obtained from §1 with `β := anchorIncidence · j` and `B := incidence`, then `coeff_eq` converts
the normal equation into `hbal`. -/
theorem harmonic_columns_exist (α : Edge → ℝ) (hα : ∀ e, 0 ≤ α e) :
    ∃ H : Free → Fin 9 → ℝ, ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0 := by
  have hex : ∀ j : Fin 9, ∃ h : Free → ℝ,
      ∀ v, ∑ e, α e * (FlashResponseHessianFlux.anchorIncidence e j
        + ∑ w, incidence e w * h w) * incidence e v = 0 := fun j =>
    (exists_ls_stationary_minimizer (V := Free) (fun e v => incidence e v)
      (fun e => FlashResponseHessianFlux.anchorIncidence e j) α hα).imp
      (fun h hh => hh.1)
  choose h hspec using hex
  refine ⟨fun v j => h j v, ?_⟩
  intro v j
  simp_rw [FlashResponseHessianFlux.coeff_eq]
  have hgoal := hspec j v
  have hsum : ∑ e, (α e * incidence e v)
        * (FlashResponseHessianFlux.anchorIncidence e j + ∑ w, incidence e w * h j w)
      = ∑ e, α e * (FlashResponseHessianFlux.anchorIncidence e j
          + ∑ w, incidence e w * h j w) * incidence e v :=
    Finset.sum_congr rfl (fun e _ => by ring)
  rw [hsum]
  exact hgoal

/-- **The harmonic lift exists and minimizes for every boundary datum**: a balanced `H` whose
lift `(lift H U ∘ inl, lift H U ∘ inr)` attains the Dirichlet minimum for every `U`.  This is the
concrete realisation of the source's free-node equilibrium + `H = -L_ff⁻¹L_fa`. -/
theorem harmonic_lift_exists (α : Edge → ℝ) (hα : ∀ e, 0 ≤ α e) :
    ∃ H : Free → Fin 9 → ℝ,
      (∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0) ∧
      (∀ U : Fin 9 → Point,
        energy α U (fun i => lift H U (.inl i)) (fun f => lift H U (.inr f))
          = dirichletEnergy α U) := by
  obtain ⟨H, hH⟩ := harmonic_columns_exist α hα
  refine ⟨H, hH, fun U => ?_⟩
  exact (dirichlet_eq_of_node_balance (α := α) (U := U)
    (fun i => lift H U (.inl i)) (fun f => lift H U (.inr f)) hα
    (fun v => balance_of_columns α H hH U v)).symm

/-! ## §3 the response matrix does not depend on the chosen harmonic lift -/

/-- **Positive-weight edge coefficients are independent of the balanced lift.**  For any two
`H, H'` satisfying `hbal`, the coefficient matrices coincide on every edge with α ≠ 0. -/
theorem coeff_eq_of_hbal (α : Edge → ℝ) (hα : ∀ e, 0 ≤ α e)
    {H H' : Free → Fin 9 → ℝ}
    (hH : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0)
    (hH' : ∀ v j, ∑ e, (α e * incidence e v) * coeff H' e j = 0) :
    ∀ e j, α e ≠ 0 → coeff H e j = coeff H' e j := by
  classical
  intro e₀ j hae₀
  set d : Free → ℝ := fun v => H v j - H' v j with hd
  set c : Edge → ℝ := fun e => coeff H e j - coeff H' e j with hc
  have hc_eq : ∀ e, c e = ∑ v : Free, incidence e v * d v := by
    intro e
    have h1 := FlashResponseHessianFlux.coeff_eq H e j
    have h2 := FlashResponseHessianFlux.coeff_eq H' e j
    simp only [hc, hd, mul_sub]
    rw [h1, h2, Finset.sum_sub_distrib]
    ring
  have hzero : ∀ v : Free, ∑ e, (α e * incidence e v) * c e = 0 := by
    intro v
    have h1 := hH v j
    have h2 := hH' v j
    simp only [hc, mul_sub, Finset.sum_sub_distrib]
    rw [h1, h2, sub_zero]
  have hquad : ∑ e, α e * c e ^ 2 = 0 := by
    have hswap : ∑ e, α e * c e ^ 2
        = ∑ v : Free, d v * ∑ e, (α e * incidence e v) * c e := by
      calc ∑ e, α e * c e ^ 2
          = ∑ e, α e * c e * (∑ v, incidence e v * d v) := by
              apply Finset.sum_congr rfl
              intro e _
              calc α e * c e ^ 2 = α e * c e * c e := by ring
                _ = α e * c e * (∑ v, incidence e v * d v) := by
                      rw [hc_eq e]
        _ = ∑ e, ∑ v, α e * c e * (incidence e v * d v) := by
              simp_rw [Finset.mul_sum]
        _ = ∑ v, ∑ e, α e * c e * (incidence e v * d v) := Finset.sum_comm
        _ = ∑ v, d v * ∑ e, (α e * incidence e v) * c e := by
              apply Finset.sum_congr rfl
              intro v _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e _
              ring
    rw [hswap]
    simp [hzero]
  have hterm : ∀ e, α e * c e ^ 2 = 0 := fun e =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => mul_nonneg (hα e) (sq_nonneg _))).mp hquad e
      (Finset.mem_univ e)
  rcases mul_eq_zero.mp (hterm e₀) with h | h
  · exact absurd h hae₀
  · have hcc : c e₀ * c e₀ = 0 := by simpa [pow_two] using h
    have hc0 : c e₀ = 0 := mul_self_eq_zero.mp hcc
    have hce : c e₀ = coeff H e₀ j - coeff H' e₀ j := by rw [hc]
    have hsub : coeff H e₀ j - coeff H' e₀ j = 0 := by
      rw [← hce]
      exact hc0
    exact sub_eq_zero.mp hsub

/-- **The response/Gram matrix is independent of the balanced lift**: the source's Λ object
`response α (coeff H)` is the same for every solution `H` of `hbal`. -/
theorem response_eq_of_hbal (α : Edge → ℝ) (hα : ∀ e, 0 ≤ α e)
    {H H' : Free → Fin 9 → ℝ}
    (hH : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0)
    (hH' : ∀ v j, ∑ e, (α e * incidence e v) * coeff H' e j = 0) :
    ∀ i j, response α (coeff H) i j = response α (coeff H') i j := by
  intro i j
  have hpt := coeff_eq_of_hbal α hα hH hH'
  unfold response
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases hae : α e = 0
  · simp [hae]
  · rw [hpt e i hae, hpt e j hae]

/-! ## §4 the response form is the geometric energy of the lift -/

/-- **Geometry identity (energy form)**: for any coefficient matrix `H`, the Dirichlet energy of
the lifted geometry `(lift H U ∘ inl, lift H U ∘ inr)` equals the formal response quadratic form
`Eform (response α (coeff H)) U U`.  Instantiated at the boundary datum `U := arcEnd u` this says
`coeff H` is the exact coordinate representation of that datum as used by the energy.  It does NOT
say the source's actual centers/Z equal the lift; the per-edge geometric identity (only where
α ≠ 0, no connectivity, no pointwise claim) is
`HarmonicResponseConsumer.edgeVector_eq_of_balance`. -/
theorem energy_lift_eq_Eform (α : Edge → ℝ) (H : Free → Fin 9 → ℝ) (U : Fin 9 → Point) :
    energy α U (fun i => lift H U (.inl i)) (fun f => lift H U (.inr f))
      = Eform (response α (coeff H)) U U := by
  rw [gram_energy]
  unfold energy
  apply Finset.sum_congr rfl
  intro e _
  rw [edgeLength_eq_norm, edge_lift]

/-! ## §5 interface audit: the two `anchorIncidence` conventions -/

/-- `FlashResponseHessianFlux.anchorIncidence` (C1540's own convention) equals
`ResumeAnchorFlux.anchorIncidence` (the live consumer chain's convention).  They are NOT
definitionally equal, so any transfer of C1540's `hflux` into the consumers' `flux` needs this
bridge. -/
theorem anchorIncidence_bridge (e : Edge) (i : Fin 9) :
    FlashResponseHessianFlux.anchorIncidence e i = ResumeAnchorFlux.anchorIncidence e i := by
  rcases e with ⟨k, s⟩ | ⟨f, v⟩
  · simp only [FlashResponseHessianFlux.anchorIncidence, ResumeAnchorFlux.anchorIncidence]
    by_cases h : anchorIndex k s = i
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hh : i = anchorIndex k s => h hh.symm), if_neg h]
      norm_num
  · rfl

end N11Formalization.HarmonicLiftExistence

#print axioms N11Formalization.HarmonicLiftExistence.exists_ls_stationary_minimizer
#print axioms N11Formalization.HarmonicLiftExistence.harmonic_columns_exist
#print axioms N11Formalization.HarmonicLiftExistence.harmonic_lift_exists
#print axioms N11Formalization.HarmonicLiftExistence.coeff_eq_of_hbal
#print axioms N11Formalization.HarmonicLiftExistence.response_eq_of_hbal
#print axioms N11Formalization.HarmonicLiftExistence.energy_lift_eq_Eform
#print axioms N11Formalization.HarmonicLiftExistence.anchorIncidence_bridge

set_option pp.explicit true
set_option pp.universes false

#check @N11Formalization.HarmonicLiftExistence.exists_ls_stationary_minimizer
#check @N11Formalization.HarmonicLiftExistence.harmonic_lift_exists
#check @N11Formalization.HarmonicLiftExistence.response_eq_of_hbal
#check @N11Formalization.HarmonicLiftExistence.energy_lift_eq_Eform
