import N11Formalization.ResumeResponseColumns

noncomputable section
namespace N11Formalization.ResumeHarmonicExtension
open ResumeNetwork ResumeDirichlet ResumeAnchorFlux ResumeResponseGram ResumeResponseColumns FlashLocal

def extend (L : Free → Fin 9 → ℝ) (W : Fin 9 → Point) (v : Free) : Point :=
  ∑ i, L v i • W i

def site (L : Free → Fin 9 → ℝ) (W : Fin 9 → Point) (i : Fin 11) : Point := extend L W (.inl i)
def faceNode (L : Free → Fin 9 → ℝ) (W : Fin 9 → Point) (f : Fin 11) : Point := extend L W (.inr f)
def edgeCoeff (L : Free → Fin 9 → ℝ) (e : Edge) (i : Fin 9) : ℝ :=
  anchorIncidence e i + ∑ v, incidence e v * L v i

theorem edge_split (W : Fin 9 → Point) (C Z : Fin 11 → Point) (e : Edge) :
    edgeVector W C Z e = edgeVector W 0 0 e + edgeVector 0 C Z e := by
  rcases e with ⟨i,s⟩ | ⟨f,k⟩ <;> simp only [edgeVector, Pi.zero_apply] <;> abel

/-- The edge representation follows from the actual 51-edge incidence, rather
than being supplied as a theorem-shaped hypothesis. -/
theorem edge_representation (L : Free → Fin 9 → ℝ) (W : Fin 9 → Point) (e : Edge) :
    edgeVector W (site L W) (faceNode L W) e = ∑ i, edgeCoeff L e i • W i := by
  rw [edge_split, ← anchorIncidence_apply]
  have hf : edgeVector 0 (site L W) (faceNode L W) e = ∑ v, incidence e v • extend L W v := by
    have hh : Sum.elim (site L W) (faceNode L W) = extend L W := by
      funext v
      cases v <;> rfl
    have hz : (fun _ : Fin 9 => (0 : Point)) = (0 : Fin 9 → Point) := by
      funext i
      rfl
    simpa only [hh, hz] using (incidence_apply (site L W) (faceNode L W) e).symm
  rw [hf]
  simp only [extend, Finset.smul_sum, smul_smul, edgeCoeff, add_smul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]

/-- Solve only 22x9 scalar equilibrium equations for L. No inverse is needed,
so disconnected zero-stress face nodes may be assigned arbitrary extensions. -/
theorem response_identity (α : Edge → ℝ) (L : Free → Fin 9 → ℝ)
    (hα : ∀ e, 0 ≤ α e)
    (hc : ∀ v i, ∑ e, α e * incidence e v * edgeCoeff L e i = 0)
    (W : Fin 9 → Point) :
    Eform (response α (edgeCoeff L)) W W = dirichletEnergy α W :=
  response_eq_of_columns α (edgeCoeff L) (site L) (faceNode L) hα (edge_representation L) hc W

#print axioms response_identity
end N11Formalization.ResumeHarmonicExtension
