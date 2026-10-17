import N11Formalization.ActualCanonicalFaceCoordinates

/-! Class33 DRAFT (uncompiled): label lemmas for `canonicalLabel` on 3-element faces, verbatim technique of the
green A25 probe ProbeA25AuditC1804Structure (`decide` does not reduce `orderIsoOfFin`). -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33Labels
open ActualCanonicalFaceCoordinates

theorem lab_zero (f : Finset (Fin 11)) (h : f.card = 3) {i : Fin 11} (hi : i ∈ f)
    (hmin : ∀ j ∈ f, i ≤ j) : canonicalLabel f h 0 = i := by
  unfold canonicalLabel
  have hmem : ((f.orderIsoOfFin h) 0).val ∈ f := ((f.orderIsoOfFin h) 0).property
  have hle : i ≤ ((f.orderIsoOfFin h) 0).val := hmin _ hmem
  by_contra hne
  have hlt : i < ((f.orderIsoOfFin h) 0).val := lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨s, hs⟩ := (f.orderIsoOfFin h).surjective ⟨i, hi⟩
  have hs0 : (0 : Fin 3) ≤ s := Fin.zero_le s
  have hge : ((f.orderIsoOfFin h) 0).val ≤ i := by
    have hm := (f.orderIsoOfFin h).monotone hs0
    rw [hs] at hm
    exact hm
  exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)

theorem lab_two (f : Finset (Fin 11)) (h : f.card = 3) {i : Fin 11} (hi : i ∈ f)
    (hmax : ∀ j ∈ f, j ≤ i) : canonicalLabel f h 2 = i := by
  unfold canonicalLabel
  have hmem : ((f.orderIsoOfFin h) 2).val ∈ f := ((f.orderIsoOfFin h) 2).property
  have hle : ((f.orderIsoOfFin h) 2).val ≤ i := hmax _ hmem
  by_contra hne
  have hlt : ((f.orderIsoOfFin h) 2).val < i := lt_of_le_of_ne hle hne
  obtain ⟨s, hs⟩ := (f.orderIsoOfFin h).surjective ⟨i, hi⟩
  have hs2 : s ≤ (2 : Fin 3) := Fin.le_last s
  have hge : i ≤ ((f.orderIsoOfFin h) 2).val := by
    have hm := (f.orderIsoOfFin h).monotone hs2
    rw [hs] at hm
    exact hm
  exact absurd (lt_of_lt_of_le hlt hge) (lt_irrefl _)

theorem lab_one (f : Finset (Fin 11)) (h : f.card = 3) {a b c : Fin 11}
    (ha : canonicalLabel f h 0 = a) (hc : canonicalLabel f h 2 = c) (hb : b ∈ f)
    (hne_a : b ≠ a) (hne_c : b ≠ c) : canonicalLabel f h 1 = b := by
  unfold canonicalLabel at ha hc ⊢
  by_contra hne
  obtain ⟨s, hs⟩ := (f.orderIsoOfFin h).surjective ⟨b, hb⟩
  have hs' : ((f.orderIsoOfFin h) s).val = b := congrArg Subtype.val hs
  fin_cases s
  · simp only [Fin.mk_zero] at hs'
    rw [ha] at hs'
    exact hne_a hs'.symm
  · simp only [Fin.mk_one] at hs'
    exact hne hs'
  · simp only [Fin.reduceFinMk] at hs'
    rw [hc] at hs'
    exact hne_c hs'.symm

end N11Formalization.Class33Labels
