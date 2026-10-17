import N11Formalization.Conditional.CertBox
import N11Formalization.Audit.CrossCheck

/-!
# STATEMENT-AUDIT — what exactly is still missing before `Rstar` is the C891 root coordinate

Owner: teammate `stmt-audit`. Zero `sorry`, zero custom axiom. Read-only import of the Lead's
modules.

The Lead's `Conditional/CertBox.lean` pins the *box* (real hex data) and the *index*
(`radiusIndex = 6`), and proves `certBoxHi 6 < 19/50` in the kernel. This file quantifies what is
*left*: the box data alone cannot determine `Rstar`, because `C891RootSpec.sys` is an arbitrary
function field. Two legal instances with **the same** `boxLo`, `boxHi`, `radiusIndex` give
**different** `Rstar` (one rooted at the box's lower corner, one at its upper corner).

So the only object that can pin `Rstar` numerically is `sys` — the explicit 12-variable TC/KKT
residual system — which is not formalized. This is a *scope* statement (GUIDE §6 / TRUST.md §2.1),
not a claim that anything in the project is mathematically wrong.
-/

namespace N11Formalization.Audit

open N11Formalization

/-- Legal schema instance: box `[lo, hi]`, and `sys := z ↦ z - p`, so the unique boxed zero is `p`
(for any `p` inside the box). -/
def specInBox (lo hi p : Fin 12 → ℚ) (h : ∀ i, lo i ≤ p i ∧ p i ≤ hi i) (ridx : Fin 12) :
    C891RootSpec where
  sys := fun z i => z i - (p i : ℝ)
  boxLo := lo
  boxHi := hi
  radiusIndex := ridx
  exists_unique := by
    refine ⟨fun i => (p i : ℝ), ⟨fun i => ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · show (((lo i : ℚ) : ℝ)) ≤ (p i : ℝ)
      exact_mod_cast (h i).1
    · show (p i : ℝ) ≤ ((hi i : ℚ) : ℝ)
      exact_mod_cast (h i).2
    · funext i; simp
    · intro y hy
      funext i
      have h2 : y i - (p i : ℝ) = 0 := congrFun hy.2 i
      linarith

theorem specInBox_root (lo hi p : Fin 12 → ℚ)
    (h : ∀ i, lo i ≤ p i ∧ p i ≤ hi i) (ridx : Fin 12) :
    (specInBox lo hi p h ridx).root = fun i => (p i : ℝ) := by
  refine ((specInBox lo hi p h ridx).root_unique ?_).symm
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · show (((lo i : ℚ) : ℝ)) ≤ (p i : ℝ)
    exact_mod_cast (h i).1
  · show (p i : ℝ) ≤ ((hi i : ℚ) : ℝ)
    exact_mod_cast (h i).2
  · funext i; simp [specInBox]

/-! ### the certificate box is non-degenerate -/

theorem certRadius_pos : 0 < decRadiusHex.toQ := by
  rw [decRadiusHex_toQ]; norm_num

theorem certBox_ordered : ∀ i, certBoxLo i ≤ certBoxHi i := by
  intro i
  simp only [certBoxLo, certBoxHi]
  linarith [certRadius_pos.le]

theorem certBox_six_strict : certBoxLo 6 < certBoxHi 6 := by
  simp only [certBoxLo, certBoxHi]
  linarith [certRadius_pos]

/-! ### the box + index do not identify `Rstar` -/

theorem certBox_does_not_identify_Rstar :
    ∃ S₁ S₂ : C891RootSpec,
      S₁.boxLo = certBoxLo ∧ S₁.boxHi = certBoxHi ∧ S₁.radiusIndex = 6 ∧
        S₂.boxLo = certBoxLo ∧ S₂.boxHi = certBoxHi ∧ S₂.radiusIndex = 6 ∧
          Rstar S₁ ≠ Rstar S₂ := by
  let h₁ : ∀ i, certBoxLo i ≤ certBoxLo i ∧ certBoxLo i ≤ certBoxHi i :=
    fun i => ⟨le_refl _, certBox_ordered i⟩
  let h₂ : ∀ i, certBoxLo i ≤ certBoxHi i ∧ certBoxHi i ≤ certBoxHi i :=
    fun i => ⟨certBox_ordered i, le_refl _⟩
  refine ⟨specInBox certBoxLo certBoxHi certBoxLo h₁ 6,
    specInBox certBoxLo certBoxHi certBoxHi h₂ 6, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hroot₁ : Rstar (specInBox certBoxLo certBoxHi certBoxLo h₁ 6) = (certBoxLo 6 : ℝ) := by
    show (specInBox certBoxLo certBoxHi certBoxLo h₁ 6).root 6 = (certBoxLo 6 : ℝ)
    rw [specInBox_root]
  have hroot₂ : Rstar (specInBox certBoxLo certBoxHi certBoxHi h₂ 6) = (certBoxHi 6 : ℝ) := by
    show (specInBox certBoxLo certBoxHi certBoxHi h₂ 6).root 6 = (certBoxHi 6 : ℝ)
    rw [specInBox_root]
  rw [hroot₁, hroot₂]
  exact ne_of_lt (by exact_mod_cast certBox_six_strict)

/-- Consequently: a proof that `Rstar S < 19/50` (or that `Rstar S` lies in the certificate box)
constrains `Rstar S` only up to the box, i.e. up to `2 · radius ≈ 2e-9`; it does not identify the
root. The remaining obligation is `sys` (the explicit TC/KKT residuals) together with `∃!` inside
the box. -/
theorem Rstar_only_bounded_by_box :
    ∃ S₁ S₂ : C891RootSpec,
      S₁.boxLo = certBoxLo ∧ S₁.boxHi = certBoxHi ∧ S₁.radiusIndex = 6 ∧
        S₂.boxLo = certBoxLo ∧ S₂.boxHi = certBoxHi ∧ S₂.radiusIndex = 6 ∧
          Rstar S₁ < Rstar S₂ ∧ Rstar S₂ < 19 / 50 := by
  let h₁ : ∀ i, certBoxLo i ≤ certBoxLo i ∧ certBoxLo i ≤ certBoxHi i :=
    fun i => ⟨le_refl _, certBox_ordered i⟩
  let h₂ : ∀ i, certBoxLo i ≤ certBoxHi i ∧ certBoxHi i ≤ certBoxHi i :=
    fun i => ⟨certBox_ordered i, le_refl _⟩
  refine ⟨specInBox certBoxLo certBoxHi certBoxLo h₁ 6,
    specInBox certBoxLo certBoxHi certBoxHi h₂ 6, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hroot₁ : Rstar (specInBox certBoxLo certBoxHi certBoxLo h₁ 6) = (certBoxLo 6 : ℝ) := by
      show (specInBox certBoxLo certBoxHi certBoxLo h₁ 6).root 6 = (certBoxLo 6 : ℝ)
      rw [specInBox_root]
    have hroot₂ : Rstar (specInBox certBoxLo certBoxHi certBoxHi h₂ 6) = (certBoxHi 6 : ℝ) := by
      show (specInBox certBoxLo certBoxHi certBoxHi h₂ 6).root 6 = (certBoxHi 6 : ℝ)
      rw [specInBox_root]
    rw [hroot₁, hroot₂]
    exact_mod_cast certBox_six_strict
  · exact Rstar_lt_R0_of_cert_box (specInBox certBoxLo certBoxHi certBoxHi h₂ 6) rfl rfl

end N11Formalization.Audit
