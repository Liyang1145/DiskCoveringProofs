import N11Formalization.ResumeGlobalIncidence

namespace N11Formalization.ResumeLocalIncidence
open ResumeNetwork ResumeGlobal

/-- Source interval_network_envelope.py L21: central2,central6,fan1,2,3,4,5,6,8. -/
def sourceFaces : Fin 9 → Fin 3 → Fin 11 :=
  ![![2,9,10], ![6,9,10], ![1,2,10], ![2,3,9], ![3,4,9],
    ![4,5,9], ![5,6,9], ![6,7,10], ![8,0,10]]
def faceMap : Fin 9 → Fin 11 := ![9,10,8,0,1,2,3,4,6]

/-- All 27 carrying face incidences agree, not merely unordered face sets. -/
theorem faceMap_exact : ∀ f v, rawToCanon (sourceFaces f v) = face (faceMap f) v := by decide

def siteMap (k : Fin 9) : Fin 9 := k - 2

abbrev SourceEdge := (Fin 9 × Fin 2) ⊕ (Fin 9 × Fin 3)

/-- Source boundary order: at raw switch k, site k then site k+1.
Canonical order is site-based, with side 0 previous switch, side 1 next switch. -/
def edgeMap : SourceEdge → Edge
  | .inl (k,s) => if s = 0 then .inl (siteMap k,1) else .inl (siteMap (k+1),0)
  | .inr (f,v) => .inr (faceMap f,v)

theorem edgeMap_injective : Function.Injective edgeMap := by decide

theorem edgeMap_image : ∀ e : Edge,
    (∃ s : SourceEdge, edgeMap s = e) ↔
      match e with
      | .inl _ => True
      | .inr (f,_) => f ≠ 5 ∧ f ≠ 7 := by
  intro e
  rcases e with ⟨i,s⟩ | ⟨f,v⟩
  · fin_cases i <;> fin_cases s <;> decide
  · fin_cases f <;> fin_cases v <;> decide

theorem source_edge_card : Fintype.card SourceEdge = 45 := by decide

/-- Every source boundary endpoint hits its intended anchor. -/
theorem boundary_anchor_exact : ∀ k s,
    anchorIndex (if s = (0 : Fin 2) then siteMap k else siteMap (k+1))
      (if s = 0 then 1 else 0) = siteMap k := by decide

/-- Raw 45-edge length: same source endpoint order, arbitrary raw geometry. -/
noncomputable def sourceLength (U : Fin 9 → Point) (C : Fin 11 → Point)
    (Z : Fin 9 → Point) : SourceEdge → ℝ
  | .inl (k,s) => dist (C ⟨(if s = 0 then k else k+1).val, by omega⟩) (U k)
  | .inr (f,v) => dist (C (sourceFaces f v)) (Z f)

/-- Reindexing commutes with each distance. Geometry is supplied by explicit
input equalities, so this cannot silently identify distinct root objects. -/
theorem sourceLength_eq (U Uc : Fin 9 → Point) (C Cc Zc : Fin 11 → Point)
    (Z : Fin 9 → Point)
    (hU : ∀ k, Uc (siteMap k) = U k)
    (hC : ∀ j, Cc (rawToCanon j) = C j)
    (hZ : ∀ f, Zc (faceMap f) = Z f) (e : SourceEdge) :
    sourceLength U C Z e = edgeLength Uc Cc Zc (edgeMap e) := by
  rcases e with ⟨k,s⟩ | ⟨f,v⟩
  · have hsite (j : Fin 9) :
        rawToCanon ⟨j.val, by omega⟩ = ⟨(siteMap j).val, by omega⟩ := by
      fin_cases j <;> decide
    fin_cases s
    · change dist (C ⟨k.val, by omega⟩) (U k) =
        dist (Cc ⟨(siteMap k).val, by omega⟩) (Uc (siteMap k))
      rw [← hsite, hC, hU]
    · change dist (C ⟨(k+1).val, by omega⟩) (U k) =
        dist (Cc ⟨(siteMap (k+1)).val, by omega⟩) (Uc (siteMap (k+1) - 1))
      have he : siteMap (k+1) - 1 = siteMap k := by fin_cases k <;> decide
      rw [he, hU, ← hsite, hC]
  · simp only [sourceLength, edgeMap, edgeLength]
    rw [← faceMap_exact f v, hC, hZ]

theorem sum_reindex (g : Edge → ℝ)
    (hz : ∀ f v, f = (5 : Fin 11) ∨ f = 7 → g (.inr (f,v)) = 0) :
    ∑ e : Edge, g e = ∑ e : SourceEdge, g (edgeMap e) := by
  classical
  have hsum : ∑ e ∈ Finset.univ.image edgeMap, g e = ∑ e : Edge, g e := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hn : ¬ ∃ s, edgeMap s = e := by simpa using he
    rcases e with ⟨i,s⟩ | ⟨f,v⟩
    · exact False.elim (hn ((edgeMap_image _).2 trivial))
    · have hh : ¬ (f ≠ 5 ∧ f ≠ 7) := fun h => hn ((edgeMap_image _).2 h)
      exact hz f v (by tauto)
  rw [← hsum, Finset.sum_image]
  intro a _ b _ h
  exact edgeMap_injective h

/-- Zero extension of source carrying stress preserves the actual energy. -/
theorem energy_reindex (α : Edge → ℝ) (U Uc : Fin 9 → Point)
    (C Cc Zc : Fin 11 → Point) (Z : Fin 9 → Point)
    (hz : ∀ f v, f = (5 : Fin 11) ∨ f = 7 → α (.inr (f,v)) = 0)
    (hU : ∀ k, Uc (siteMap k) = U k)
    (hC : ∀ j, Cc (rawToCanon j) = C j)
    (hZ : ∀ f, Zc (faceMap f) = Z f) :
    energy α Uc Cc Zc = ∑ e : SourceEdge, α (edgeMap e) * sourceLength U C Z e ^ 2 := by
  unfold energy
  rw [sum_reindex _ (fun f v hf => by simp [hz f v hf])]
  apply Finset.sum_congr rfl
  intro e _
  rw [sourceLength_eq U Uc C Cc Zc Z hU hC hZ]

#print axioms energy_reindex
#print axioms sourceLength_eq
#print axioms faceMap_exact
#print axioms edgeMap_injective
#print axioms edgeMap_image
end N11Formalization.ResumeLocalIncidence
