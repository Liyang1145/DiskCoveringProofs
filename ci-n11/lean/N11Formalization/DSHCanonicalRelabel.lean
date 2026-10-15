import N11Formalization.DSHTopologyInteriorHubLeg
import N11Formalization.DSHTenBoundaryData
import N11Formalization.SourceExactRoot

set_option autoImplicit false

namespace N11Formalization.DSHTopologyInterior

open N11Formalization

/-! A pure finite relabeling bridge: exactly nine circle-meeting sites can be moved to
the frozen ring slots 0..8, with the two complementary sites moved to 9,10. -/

theorem exists_ring_relabel
    {c : Fin 11 → Point} {r : ℝ}
    (hcard : Fintype.card (BoundaryIdx c r) = 9) :
    ∃ p : Equiv.Perm (Fin 11),
      ∀ i : Fin 11, MeetsCircle (fun j => c (p j)) r i ↔ (i : ℕ) < 9 := by
  classical
  let P : Fin 11 → Prop := fun i => MeetsCircle c r i
  let B : Type := {i : Fin 11 // P i}
  let N : Type := {i : Fin 11 // ¬ P i}
  have hB : Fintype.card B = 9 := by
    simpa [B, P] using hcard
  have hN : Fintype.card N = 2 := by
    have h := Fintype.card_subtype_compl P
    simpa [N, B, P, hB] using h
  let eB : Fin 9 ≃ B := Fintype.equivOfCardEq (by simpa [hB])
  let eN : Fin 2 ≃ N := Fintype.equivOfCardEq (by simpa [hN])
  let eSum : (Fin 9 ⊕ Fin 2) ≃ (B ⊕ N) := Equiv.sumCongr eB eN
  let eAll : (B ⊕ N) ≃ Fin 11 := Equiv.Set.sumCompl {i : Fin 11 | P i}
  let fse : (Fin 9 ⊕ Fin 2) ≃ Fin 11 := finSumFinEquiv
  let p : Equiv.Perm (Fin 11) :=
    fse.symm.trans (eSum.trans eAll)
  refine ⟨p, ?_⟩
  have hAllB : ∀ b : B, P (eAll (Sum.inl b)) := by
    intro b
    change P b.1
    exact b.2
  have hAllN : ∀ n : N, ¬ P (eAll (Sum.inr n)) := by
    intro n
    change ¬ P n.1
    exact n.2
  intro i
  let s : Fin 9 ⊕ Fin 2 := fse.symm i
  cases hs : s with
  | inl a =>
      have hi : i = fse (Sum.inl a) := by
        calc
          i = fse (fse.symm i) := by simp
          _ = fse s := by rfl
          _ = fse (Sum.inl a) := by rw [hs]
      have hmeet : P (p (fse (Sum.inl a))) := by
        have hp : p (fse (Sum.inl a)) = eAll (Sum.inl (eB a)) := by
          simp [p, eSum]
        rw [hp]
        exact hAllB (eB a)
      have hslot : (fse (Sum.inl a) : Fin 11).val < 9 := by
        simp [fse, finSumFinEquiv]
      change P (p i) ↔ (i : ℕ) < 9
      rw [hi]
      exact iff_of_true hmeet hslot
  | inr b =>
      have hi : i = fse (Sum.inr b) := by
        calc
          i = fse (fse.symm i) := by simp
          _ = fse s := by rfl
          _ = fse (Sum.inr b) := by rw [hs]
      have hnot : ¬ P (p (fse (Sum.inr b))) := by
        have hp : p (fse (Sum.inr b)) = eAll (Sum.inr (eN b)) := by
          simp [p, eSum]
        rw [hp]
        exact hAllN (eN b)
      have hslot : ¬ ((fse (Sum.inr b) : Fin 11).val < 9) := by
        simp [fse, finSumFinEquiv]
      change P (p i) ↔ (i : ℕ) < 9
      rw [hi]
      exact iff_of_false hnot hslot

theorem covers_relabel (p : Equiv.Perm (Fin 11))
    {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r) :
    Covers (fun j => c (p j)) r := by
  intro x hx
  obtain ⟨i, hi⟩ := hc x hx
  refine ⟨p.symm i, ?_⟩
  simpa using hi

theorem exists_covers_ringLabels
    {c : Fin 11 → Point} {r : ℝ}
    (hcard : Fintype.card (BoundaryIdx c r) = 9) (hc : Covers c r) :
    ∃ p : Equiv.Perm (Fin 11),
      Covers (fun j => c (p j)) r ∧
        DSHTopologyInterior.RingLabels (fun j => c (p j)) r := by
  obtain ⟨p, hp⟩ := exists_ring_relabel hcard
  exact ⟨p, covers_relabel p hc, hp⟩

theorem exists_covers_ringLabels_of_c450
    {c : Fin 11 → Point} {r : ℝ}
    (h450 : C450PerDiskObligation)
    (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    ∃ p : Equiv.Perm (Fin 11),
      Covers (fun j => c (p j)) r ∧
        DSHTopologyInterior.RingLabels (fun j => c (p j)) r := by
  exact exists_covers_ringLabels
    (card_boundaryIdx_eq_nine_of_obligation_lt_sourceRadius h450 hr hc) hc

#check @N11Formalization.DSHTopologyInterior.exists_ring_relabel
#check @N11Formalization.DSHTopologyInterior.covers_relabel
#check @N11Formalization.DSHTopologyInterior.exists_covers_ringLabels
#check @N11Formalization.DSHTopologyInterior.exists_covers_ringLabels_of_c450
#print axioms N11Formalization.DSHTopologyInterior.exists_ring_relabel
#print axioms N11Formalization.DSHTopologyInterior.covers_relabel
#print axioms N11Formalization.DSHTopologyInterior.exists_covers_ringLabels
#print axioms N11Formalization.DSHTopologyInterior.exists_covers_ringLabels_of_c450

end N11Formalization.DSHTopologyInterior
