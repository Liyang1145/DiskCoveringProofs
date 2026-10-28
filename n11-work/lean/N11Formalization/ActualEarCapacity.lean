import N11Formalization.ActualFiveRingStar
import N11Formalization.ActualTwoTripleCapacity

/-! Actual metric payment of the nonadjacent-ear exclusion.
An ear means ONLY its3 real ring disks have a common point. Distinct
nonadjacent ear indices cannot both occur. Adjacent skipped indices still
require the separate planar noncrossing producer, explicitly not paid here. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualEarCapacity
open DSHTopologyInterior ActualRingDirectionOrder ActualFiveRingStar ActualTwoTripleCapacity

def earSet (i : Fin 9) : Finset (Fin 9) := {i-1,i,i+1}
def Ear (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) : Prop :=
  ∃ p : Point, ∀ j ∈ earSet i, dist p (c (ringSite j)) ≤ r

theorem earSet_card : ∀ i : Fin 9, (earSet i).card = 3 := by decide +kernel

theorem nonadjacent_ear_sets : ∀ i j : Fin 9, i ≠ j → j ≠ i-1 → j ≠ i+1 →
    Disjoint (earSet i) (earSet j) ∨
      ∃ k : Fin 9, k ∈ earSet i ∧ k ∈ earSet j ∧
        (((earSet i)∪(earSet j)).erase k).card = 4 := by
  decide +kernel

theorem ear_pair_adjacent {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j : Fin 9} (hij : i ≠ j) (hi : Ear c r i) (hj : Ear c r j) :
    j = i-1 ∨ j = i+1 := by
  by_contra hnot
  have hleft : j ≠ i-1 := fun he => hnot (Or.inl he)
  have hright : j ≠ i+1 := fun he => hnot (Or.inr he)
  obtain ⟨p,hp⟩ := hi
  obtain ⟨q,hq⟩ := hj
  rcases nonadjacent_ear_sets i j hij hleft hright with hdis | hcorner
  · exact no_disjoint_common_triples hc hr hR p q (earSet i) (earSet j)
      (earSet_card i) (earSet_card j) hdis hp hq
  · obtain ⟨k,hki,hkj,hcard⟩ := hcorner
    let s := (((earSet i)∪(earSet j)).erase k)
    apply no_four_ring_neighbors hc hr hR k s hcard (Finset.notMem_erase _ _)
    intro l hl
    have hmem : l ∈ earSet i ∨ l ∈ earSet j := Finset.mem_union.mp (Finset.mem_erase.mp hl).2
    rcases hmem with hli | hlj
    · exact ⟨p,hp k hki,hp l hli⟩
    · exact ⟨q,hq k hkj,hq l hlj⟩

/-- For an embedded noncrossing refinement the ONLY additional finite
input is that adjacent skipped indices do not both form ears. No such
input is claimed for an arbitrary cover without the geometric producer. -/
theorem selected_ears_card_le_one {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (s : Finset (Fin 9)) (hactual : ∀ i ∈ s, Ear c r i)
    (hnoAdjacent : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → j ≠ i-1 ∧ j ≠ i+1) :
    s.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hne
  have hp := ear_pair_adjacent hc hr hR hne (hactual i hi) (hactual j hj)
  have hn := hnoAdjacent i hi j hj hne
  exact hp.elim hn.1 hn.2

end N11Formalization.ActualEarCapacity
#check @N11Formalization.ActualEarCapacity.ear_pair_adjacent
#check @N11Formalization.ActualEarCapacity.selected_ears_card_le_one
#print axioms N11Formalization.ActualEarCapacity.ear_pair_adjacent
