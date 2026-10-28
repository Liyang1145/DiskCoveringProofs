import N11Formalization.ResumeLocalIncidence
import N11Formalization.ResumeDirichlet

noncomputable section
namespace N11Formalization.ResumeLocalIncidence
open ResumeNetwork ResumeGlobal ResumeDirichlet

/-- Signed source edge vectors: free site minus anchor/face witness.
Unlike a distance identity, this fixes the signs used by adaptive cross terms. -/
def sourceVector (U : Fin 9 → Point) (C : Fin 11 → Point)
    (Z : Fin 9 → Point) : SourceEdge → Point
  | .inl (k,s) => C ⟨(if s = 0 then k else k+1).val, by omega⟩ - U k
  | .inr (f,v) => C (sourceFaces f v) - Z f

theorem sourceVector_eq (U Uc : Fin 9 → Point) (C Cc Zc : Fin 11 → Point)
    (Z : Fin 9 → Point)
    (hU : ∀ k, Uc (siteMap k) = U k)
    (hC : ∀ j, Cc (rawToCanon j) = C j)
    (hZ : ∀ f, Zc (faceMap f) = Z f) (e : SourceEdge) :
    sourceVector U C Z e = edgeVector Uc Cc Zc (edgeMap e) := by
  rcases e with ⟨k,s⟩ | ⟨f,v⟩
  · have hsite (j : Fin 9) :
        rawToCanon ⟨j.val, by omega⟩ = ⟨(siteMap j).val, by omega⟩ := by
      fin_cases j <;> decide
    fin_cases s
    · change C ⟨k.val, by omega⟩ - U k =
        Cc ⟨(siteMap k).val, by omega⟩ - Uc (siteMap k)
      rw [← hsite, hC, hU]
    · change C ⟨(k+1).val, by omega⟩ - U k =
        Cc ⟨(siteMap (k+1)).val, by omega⟩ - Uc (siteMap (k+1) - 1)
      have he : siteMap (k+1) - 1 = siteMap k := by fin_cases k <;> decide
      rw [he, hU, ← hsite, hC]
  · simp only [sourceVector, edgeMap, edgeVector]
    rw [← faceMap_exact f v, hC, hZ]

/-- Zero extension preserves signed weighted cross terms, not only squared lengths.
Both vector families must be explicitly matched on carrying edges. -/
theorem cross_reindex (α : Edge → ℝ) (a b : Edge → Point)
    (aS bS : SourceEdge → Point)
    (hz : ∀ f v, f = (5 : Fin 11) ∨ f = 7 → α (.inr (f,v)) = 0)
    (ha : ∀ e, a (edgeMap e) = aS e) (hb : ∀ e, b (edgeMap e) = bS e) :
    (∑ e : Edge, α e * inner ℝ (a e) (b e)) =
      ∑ e : SourceEdge, α (edgeMap e) * inner ℝ (aS e) (bS e) := by
  rw [sum_reindex _ (fun f v hf => by simp [hz f v hf])]
  apply Finset.sum_congr rfl
  intro e _
  rw [ha, hb]

#print axioms sourceVector_eq
#print axioms cross_reindex
end N11Formalization.ResumeLocalIncidence
