import N11Formalization.Statement
import N11Formalization.Conditional.RootSpec
import N11Formalization.Audit.Drift

/-!
# STATEMENT-AUDIT — cross-checks and specification-strength evidence

Owner: teammate `stmt-audit`. Write scope: `N11Formalization/Audit/**`. Zero `sorry`, zero custom
axiom. This file imports the Lead's modules **read-only** and proves statements *about* them.

Contents
* (1) the Lead's definitional layer and my independent transcription denote the **same objects**
      (`Covers`, `feasibleRadii`, `StrongInterface`) — removes "auditor/formalizer statement drift"
      in the direction "only one of the two objects is the one GUIDE §2 describes";
* (2) `StrongInterface` and `N11MainStatement` are *equivalent*, so the conditional main theorem
      transfers no mathematical content and cannot be mistaken for progress;
* (3) the parametric schema `C891RootSpec` alone does **not** pin the value of `Rstar`: a legal
      instance gives `Rstar = 1/3` with `radiusIndex = 6`. Hence `Rstar`'s numerical identity with
      the C891 root coordinate is *not yet* established by any theorem in the project.
-/

namespace N11Formalization.Audit

open N11Formalization

/-! ## (1) same objects, two independent transcriptions -/

/-- The Lead's `Covers` and the auditor's transcription agree literally. -/
theorem lead_covers_iff_audit_covers (c : Fin 11 → Point) (r : ℝ) :
    N11Formalization.Covers c r ↔ N11Formalization.Audit.Covers c r := Iff.rfl

/-- Hence the same feasible-radius set. -/
theorem lead_feasibleRadii_eq_audit_FeasibleSet :
    N11Formalization.feasibleRadii = N11Formalization.Audit.FeasibleSet := by
  ext r
  exact and_congr_right fun _ =>
    exists_congr fun c => lead_covers_iff_audit_covers c r

/-- And the same strong interface, i.e. both transcriptions fix the same final proposition. -/
theorem lead_StrongInterface_iff_audit_N11Optimum (R : ℝ) :
    N11Formalization.StrongInterface R ↔ N11Formalization.Audit.N11Optimum R := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2⟩

/-! ## (2) the conditional main theorem is an equivalence, not progress -/

/-- `StrongInterface R ↔ N11MainStatement R`: the two covering interfaces are *jointly
interchangeable* with the conclusion. So `n11_main_conditional` (whose hypotheses are exactly
those two interfaces) cannot by itself advance the mathematics; only an instantiation of the
schema with a *proved* C891/C892/C921 content can. -/
theorem strongInterface_iff_mainStatement (R : ℝ) :
    N11Formalization.StrongInterface R ↔ N11Formalization.N11MainStatement R :=
  ⟨N11Formalization.n11_main_of_strongInterface, N11Formalization.strongInterface_of_n11_main⟩

/-! ## (3) `C891RootSpec` does not pin `Rstar` -/

/-- Legal degenerate instance of the parametric schema: singleton box at the constant point
`1/3`, with `sys z = z - 1/3` (so the unique boxed zero is the constant point). -/
def degenerateSpec : C891RootSpec where
  sys := fun z i => z i - (((1 : ℚ) / 3 : ℚ) : ℝ)
  boxLo := fun _ => 1 / 3
  boxHi := fun _ => 1 / 3
  radiusIndex := 6
  exists_unique := by
    refine ⟨fun _ => (((1 : ℚ) / 3 : ℚ) : ℝ), ⟨?_, ?_⟩, ?_⟩
    · intro i; exact ⟨le_refl _, le_refl _⟩
    · funext i; simp
    · intro y hy
      funext i
      have h2 : y i - (((1 : ℚ) / 3 : ℚ) : ℝ) = 0 := congrFun hy.2 i
      linarith

theorem degenerateSpec_root :
    degenerateSpec.root = fun _ : Fin 12 => (((1 : ℚ) / 3 : ℚ) : ℝ) := by
  refine (degenerateSpec.root_unique ?_).symm
  refine ⟨fun _ => ⟨le_refl _, le_refl _⟩, ?_⟩
  funext i
  simp [degenerateSpec]

/-- The `Rstar` of the degenerate instance. -/
theorem degenerateSpec_Rstar : Rstar degenerateSpec = 1 / 3 := by
  show degenerateSpec.root 6 = 1 / 3
  rw [degenerateSpec_root]
  norm_num

/-- **Specification-strength finding (kernel-proved).** The schema admits an instance with
`radiusIndex = 6` whose `Rstar` is `1/3`. Therefore no theorem in the project currently identifies
`Rstar S` with the C891 root coordinate `0.3799838531198386897222616061358…`; that identification
is still an obligation (formalize `sys` = the 12 TC/KKT residuals, `boxLo/boxHi` = the dyadic box
from the decoded hex certificate, and prove `∃!` inside it). -/
theorem schema_does_not_pin_Rstar :
    ∃ S : C891RootSpec, S.radiusIndex = 6 ∧ Rstar S = 1 / 3 :=
  ⟨degenerateSpec, rfl, degenerateSpec_Rstar⟩

/-- Consequently the conditional theorems are about `Rstar S` **for an arbitrary instance `S`**;
they are not about `0.3799838531198386897222616061358 < Rstar < …`. -/
theorem Rstar_not_determined_by_schema :
    ∃ S : C891RootSpec, Rstar S < (3799838531198386897222616061358 : ℝ) / 10 ^ 31 := by
  refine ⟨degenerateSpec, ?_⟩
  rw [degenerateSpec_Rstar]
  norm_num

end N11Formalization.Audit
