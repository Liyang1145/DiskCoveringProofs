import N11Formalization.SharedMomentFactorGridCertificate

/-! Complete signed face bounds are independent of the local ordering of
the three genuine labels. Only their whole-domain angle variables are
reindexed; the original geometry and radius are retained. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFactorPermutation
open SharedMomentFactorGridCertificate

theorem sine_product_perm (a : Fin 3 → ℝ) (e : Equiv.Perm (Fin 3)) :
    Real.sin (a (e 0))*Real.sin (a (e 1))*Real.sin (a (e 2)) =
      Real.sin (a 0)*Real.sin (a 1)*Real.sin (a 2) := by
  simpa only [Fin.prod_univ_three] using Equiv.prod_comp e (fun s => Real.sin (a s))

theorem faceQuadratic_perm (q a : Fin 3 → ℝ) (e : Equiv.Perm (Fin 3)) :
    faceQuadratic (fun s => q (e s)) (fun s => a (e s)) = faceQuadratic q a := by
  have hsum := Equiv.sum_comp e (fun s => q s*Real.sin (a s)^2)
  have hprod := sine_product_perm a e
  unfold faceQuadratic
  calc
    _ = 2*(19/50 : ℝ)^2*(Real.sin (a (e 0))*Real.sin (a (e 1))*Real.sin (a (e 2)))+
        ∑ s : Fin 3, q (e s)*Real.sin (a (e s))^2 := by ring
    _ = 2*(19/50 : ℝ)^2*(Real.sin (a 0)*Real.sin (a 1)*Real.sin (a 2))+
        ∑ s : Fin 3, q s*Real.sin (a s)^2 := by rw [hprod,hsum]
    _ = _ := by ring

theorem faceLinear_perm (b a : Fin 3 → ℝ) (e : Equiv.Perm (Fin 3)) :
    faceLinear (fun s => b (e s)) (fun s => a (e s)) = faceLinear b a := by
  exact Equiv.sum_comp e (fun s => b s*Real.sin (a s))

theorem faceObjective_perm (p q b a : Fin 3 → ℝ) (y : ℝ)
    (e : Equiv.Perm (Fin 3)) :
    faceObjective (fun s => p (e s)) (fun s => q (e s)) (fun s => b (e s))
      (fun s => a (e s)) y = faceObjective p q b a y := by
  unfold faceObjective
  rw [faceQuadratic_perm,faceLinear_perm,Equiv.sum_comp e (fun s => p s*a s)]

theorem faceEnvelope_perm (p q b a : Fin 3 → ℝ) (e : Equiv.Perm (Fin 3)) :
    faceEnvelope (fun s => p (e s)) (fun s => q (e s)) (fun s => b (e s))
      (fun s => a (e s)) = faceEnvelope p q b a := by
  unfold faceEnvelope
  rw [faceQuadratic_perm,faceLinear_perm,Equiv.sum_comp e (fun s => p s*a s)]

/-- A table bound in canonical local order supplies every actual order.
The permutation is arbitrary and may differ from face to face. -/
theorem face_upper_of_permuted_coefficients (p q b : Fin 3 → ℝ) (M : ℝ)
    (e : Equiv.Perm (Fin 3))
    (H : ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective p q b a y ≤ M) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => p (e s)) (fun s => q (e s)) (fun s => b (e s)) a y ≤ M := by
  intro a ha hsum y hy
  let a' : Fin 3 → ℝ := fun s => a (e.symm s)
  have hsum' : (∑ s : Fin 3, a' s)=Real.pi :=
    (Equiv.sum_comp e.symm a).trans hsum
  have hb := H a' (fun s => ha (e.symm s)) hsum' y hy
  have he := faceObjective_perm p q b a' y e
  simpa only [a',Equiv.symm_apply_apply] using he.trans_le hb

end N11Formalization.SharedMomentFactorPermutation
#check @N11Formalization.SharedMomentFactorPermutation.face_upper_of_permuted_coefficients
#print axioms N11Formalization.SharedMomentFactorPermutation.sine_product_perm
#print axioms N11Formalization.SharedMomentFactorPermutation.faceQuadratic_perm
#print axioms N11Formalization.SharedMomentFactorPermutation.faceObjective_perm
#print axioms N11Formalization.SharedMomentFactorPermutation.faceEnvelope_perm
#print axioms N11Formalization.SharedMomentFactorPermutation.face_upper_of_permuted_coefficients
