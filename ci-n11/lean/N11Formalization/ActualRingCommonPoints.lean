import N11Formalization.ActualCapClusterCapacity

/-! Whole-plane common-point exclusions for actual ring disks.
At most THREE rings contain any point. No graph, ear or Voronoi premises.
The proof keeps original r, all actual caps and all degenerate points. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRingCommonPoints
open DSHTopologyInterior ActualRingDirectionOrder ActualCapClusterCapacity

def ringsAt (c : Fin 11 → Point) (r : ℝ) (p : Point) : Finset (Fin 9) :=
  Finset.univ.filter (fun i => dist p (c (ringSite i)) ≤ r)

theorem no_four_common_rings {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (p : Point) (s : Finset (Fin 9)) (hs : s.card = 4)
    (hcommon : ∀ i ∈ s, dist p (c (ringSite i)) ≤ r) : False := by
  apply no_four_cap_cluster hc hr hR p s hs
  intro i hi x hx hxi
  have ht := dist_triangle x (c (ringSite i)) p
  rw [dist_comm (c (ringSite i)) p] at ht
  linarith [hcommon i hi]

theorem ringsAt_card_le_three {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) (p : Point) :
    (ringsAt c r p).card ≤ 3 := by
  classical
  by_contra hnot
  have hfour : 4 ≤ (ringsAt c r p).card := by omega
  obtain ⟨s,hsub,hs⟩ := Finset.exists_subset_card_eq hfour
  apply no_four_common_rings hc hr hR p s hs
  intro i hi
  exact (Finset.mem_filter.mp (hsub hi)).2

end N11Formalization.ActualRingCommonPoints
#check @N11Formalization.ActualRingCommonPoints.ringsAt_card_le_three
#print axioms N11Formalization.ActualRingCommonPoints.ringsAt_card_le_three
