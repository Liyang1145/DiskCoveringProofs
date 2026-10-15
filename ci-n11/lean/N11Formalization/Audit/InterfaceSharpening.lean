import N11Formalization.Attainment
import N11Formalization.Audit.CertBoxPinning

/-!
# STATEMENT-AUDIT — sharpened interface after `Attainment.lean` (and the new drift hazard)

Owner: teammate `stmt-audit`. Zero `sorry`, zero custom axiom. Read-only import of the Lead's
modules.

`Attainment.lean` proves unconditionally that `sInf feasibleRadii` is attained
(`exists_covers_sInf`, `sInf_mem_feasibleRadii`) and that `feasibleRadii = [sInf, ∞)` is closed.
Consequences audited here:

1. **Everything collapses to one scalar equation.** `StrongInterface R ↔ R = sInf feasibleRadii`
   and `N11MainStatement R ↔ R = sInf feasibleRadii`. So the *only* remaining mathematical inputs
   are the two inequalities `sInf ≤ Rstar` (a cover at `Rstar`, i.e. C892's construction) and
   `Rstar ≤ sInf` (the lower bound C923/C921/C922). In particular C892's *construction* is **not**
   circumvented: only the general "some optimal configuration exists" question is discharged.
2. **New drift hazard (must be flagged).** `N11MainStatement (sInf feasibleRadii)` is *free*
   (`mainStatement_at_sInf_is_free`) — it is true unconditionally and says nothing about the C891
   root. Any final statement phrased as "r_D(11) = sInf" is therefore vacuous with respect to the
   source theorem; the defensible final form must name the same constant on both sides
   (`Rstar S = sInf feasibleRadii`, plus the two inequalities above).
-/

namespace N11Formalization.Audit

open N11Formalization

/-- After unconditional attainment, the strong interface at `R` says exactly `R = sInf`. -/
theorem strongInterface_iff_eq_sInf (R : ℝ) :
    N11Formalization.StrongInterface R ↔ R = sInf N11Formalization.feasibleRadii := by
  constructor
  · intro h
    exact (sInf_feasibleRadii_eq ((isLeast_iff_strongInterface R).mpr h)).symm
  · intro h
    rw [h]
    exact strongInterface_sInf

/-- Same for the `Statement.lean` form. -/
theorem n11MainStatement_iff_eq_sInf (R : ℝ) :
    N11Formalization.N11MainStatement R ↔ R = sInf N11Formalization.feasibleRadii := by
  constructor
  · intro h
    exact (strongInterface_iff_eq_sInf R).mp (strongInterface_of_n11_main h)
  · intro h
    exact n11_main_of_strongInterface ((strongInterface_iff_eq_sInf R).mpr h)

/-- **The free form.** `N11MainStatement (sInf feasibleRadii)` holds with no hypotheses at all.
It mentions no root and no constant from the source certificate; citing it as "the n=11 theorem"
would be a pure statement drift (it is the abstract covering-number identity, true for any finite
`n`-disk problem of this shape). -/
theorem mainStatement_at_sInf_is_free :
    N11Formalization.N11MainStatement (sInf N11Formalization.feasibleRadii) :=
  n11_main_of_strongInterface strongInterface_sInf

/-- The *non-free* half: the identification `Rstar S = sInf feasibleRadii` is a genuine obligation.
The schema admits instances whose `Rstar` differs from `sInf` (take the two instances of
`CertBoxPinning.certBox_does_not_identify_Rstar` with `Rstar = 1/3` and `Rstar = certBoxLo 6`;
`sInf feasibleRadii` cannot equal both). -/
theorem exists_instance_with_Rstar_ne_sInf :
    ∃ S : C891RootSpec, Rstar S ≠ sInf N11Formalization.feasibleRadii := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  let h₁ : ∀ i, certBoxLo i ≤ certBoxLo i ∧ certBoxLo i ≤ certBoxHi i :=
    fun i => ⟨le_refl _, certBox_ordered i⟩
  have hdeg : (1 : ℝ) / 3 = sInf feasibleRadii := by
    rw [← degenerateSpec_Rstar]
    exact hcon degenerateSpec
  have hbox : (certBoxLo 6 : ℝ) = sInf feasibleRadii := by
    have hroot : Rstar (specInBox certBoxLo certBoxHi certBoxLo h₁ 6) = (certBoxLo 6 : ℝ) := by
      show (specInBox certBoxLo certBoxHi certBoxLo h₁ 6).root 6 = (certBoxLo 6 : ℝ)
      rw [specInBox_root]
    rw [← hroot]
    exact hcon (specInBox certBoxLo certBoxHi certBoxLo h₁ 6)
  have hne : ((1 : ℝ) / 3) ≠ (certBoxLo 6 : ℝ) := by
    have hlt : (1 : ℚ) / 3 < certBoxLo 6 := by
      simp only [certBoxLo, decCenterHex_six, decCenter6, decRadiusHex, HexFloat.toQ, hexNatVal,
        List.length_cons, List.length_nil, pow_succ, pow_zero, mul_one]
      norm_num
    have hltR : (1 : ℝ) / 3 < (certBoxLo 6 : ℝ) := by
      have h' : (((1 : ℚ) / 3 : ℚ) : ℝ) < ((certBoxLo 6 : ℚ) : ℝ) := by exact_mod_cast hlt
      simpa using h'
    exact ne_of_lt hltR
  exact hne (hdeg.trans hbox.symm)

end N11Formalization.Audit
