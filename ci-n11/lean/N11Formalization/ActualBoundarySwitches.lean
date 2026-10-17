import N11Formalization.ActualBoundaryTransversality
import N11Formalization.ActualBoundaryNineTies

/-! No false identification of a tangent nearest tie with a switch:
private circle points pay transversality, then Fermat's theorem excludes
local owner constancy. The whole circle has exactly9 switch POINTS. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundarySwitches
open DSHTopologyOwnership DSHTopologyOwnershipSwitches DSHTopologyOwnershipSwitchCount
open ActualVoronoiCells ActualBoundaryNearestPairs ActualBoundaryNineTies
open ActualBoundaryNeighborTies ActualBoundaryTransversality ActualCoverStructuralReduction
open ActualRingDirectionOrder ActualBoundaryCyclicOrder

theorem common_owner_of_locallyConst {c : Fin 11 → Point} {t : ℝ}
    (h : LocallyConstAt c t) :
    ∃ eps > 0, ∃ i : Fin 11, ∀ s : ℝ, |s-t| < eps → s ≠ t → ownerAngle c s = i := by
  obtain ⟨eps,heps,hcross⟩ := h
  let u := t-eps/2
  let v := t+eps/2
  let i := ownerAngle c u
  have huv : ownerAngle c u = ownerAngle c v := hcross u v
    (by dsimp [u]; linarith) (by dsimp [u]; linarith)
    (by dsimp [v]; linarith) (by dsimp [v]; linarith)
  refine ⟨eps,heps,i,?_⟩
  intro s hs hst
  have hb := abs_lt.mp hs
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · have h := hcross s v (by linarith [hb.1]) hlt
      (by dsimp [v]; linarith) (by dsimp [v]; linarith)
    exact h.trans huv.symm
  · exact (hcross u s (by dsimp [u]; linarith) (by dsimp [u]; linarith)
      hgt (by linarith [hb.2])).symm

theorem nearest_at_limit_of_common_owner {c : Fin 11 → Point} {t eps : ℝ}
    (heps : 0 < eps) {i : Fin 11}
    (howner : ∀ s : ℝ, |s-t| < eps → s ≠ t → ownerAngle c s = i) :
    circleMap t ∈ Cell c i := by
  have hsq (k : Fin 11) : sqDist (c i) t ≤ sqDist (c k) t := by
    by_contra hnot
    let g := fun s : ℝ => sqDist (c i) s-sqDist (c k) s
    have hg : 0 < g t := by dsimp [g]; linarith [lt_of_not_ge hnot]
    have hcont : ContinuousAt g t := ((continuous_sqDist _).sub (continuous_sqDist _)).continuousAt
    obtain ⟨delta,hdelta,hh⟩ := (Metric.continuousAt_iff.mp hcont) (g t/2) (by linarith)
    let d := min eps delta
    have hd : 0 < d := lt_min heps hdelta
    have hde : d ≤ eps := min_le_left _ _
    have hdd : d ≤ delta := min_le_right _ _
    let s := t-d/2
    have habs : |s-t| = d/2 := by
      dsimp [s]
      rw [abs_of_nonpos (by linarith : t-d/2-t ≤ 0)]
      ring
    have hse : |s-t| < eps := by rw [habs]; linarith
    have hsd : dist s t < delta := by rw [Real.dist_eq,habs]; linarith
    have hst : s ≠ t := by dsimp [s]; linarith
    have ho := owns_ownerAngle c s
    rw [howner s hse hst] at ho
    have hle : g s ≤ 0 := by dsimp [g]; linarith [ho.1 k]
    have hnear := hh hsd
    rw [Real.dist_eq] at hnear
    have hlow := (abs_lt.mp hnear).1
    linarith
  intro k
  apply (dist_le_dist_iff_sq _ _ _).mpr
  rw [← sqDist_eq_dist_sq,← sqDist_eq_dist_sq]
  exact hsq k

/-- A genuine two-site nearest tie is a switch, because both ring sites
have actual private circle points; no tangential/genericity premise. -/
theorem Representative.tie_switch {c : Fin 11 → Point} {r t : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i j : Fin 9} (hij : i ≠ j)
    (hi : circleMap t ∈ Cell c (ringSite i)) (hj : circleMap t ∈ Cell c (ringSite j)) :
    SwitchAt c t := by
  have hsites : ringSite i ≠ ringSite j := fun he => hij (ringSite_inj he)
  have heq : dist (circleMap t) (c (ringSite i)) = dist (circleMap t) (c (ringSite j)) :=
    le_antisymm (hi (ringSite j)) (hj (ringSite i))
  obtain ⟨y,hy,hya,hyother⟩ := h.private_circle i
  obtain ⟨z,hz,hzb,hzother⟩ := h.private_circle j
  have hnonzero := gapDerivative_ne_zero hy hz
    (hya.trans_lt (hyother _ hsites.symm)) (hzb.trans_lt (hzother _ hsites)) heq
  let g := fun s : ℝ => sqDist (c (ringSite j)) s-sqDist (c (ringSite i)) s
  have hderiv := hasDerivAt_gap (c (ringSite i)) (c (ringSite j)) t
  have hg0 : g t = 0 := by
    dsimp [g]
    rw [sqDist_eq_dist_sq,sqDist_eq_dist_sq,heq,sub_self]
  intro hlocal
  obtain ⟨eps,heps,k,howner⟩ := common_owner_of_locallyConst hlocal
  have hk := nearest_at_limit_of_common_owner heps howner
  have hcases := nearest_one_of_pair h.cover hr h.labels (circleMap_norm t) hsites hi hj hk
  have hball : ∀ᶠ s : ℝ in nhds t, |s-t| < eps := by
    apply Metric.eventually_nhds_iff.mpr
    exact ⟨eps,heps,fun s hs => by rwa [Real.dist_eq] at hs⟩
  rcases hcases with hkI | hkJ
  · have hmin : IsLocalMin g t := by
      apply hball.mono
      intro s hs
      by_cases hst : s = t
      · rw [hst]
      have ho := owns_ownerAngle c s
      rw [howner s hs hst,hkI] at ho
      rw [hg0]
      dsimp [g]
      linarith [ho.1 (ringSite j)]
    exact hnonzero (hmin.hasDerivAt_eq_zero hderiv)
  · have hmax : IsLocalMax g t := by
      apply hball.mono
      intro s hs
      by_cases hst : s = t
      · rw [hst]
      have ho := owns_ownerAngle c s
      rw [howner s hs hst,hkJ] at ho
      rw [hg0]
      dsimp [g]
      linarith [ho.1 (ringSite i)]
    exact hnonzero (hmax.hasDerivAt_eq_zero hderiv)

theorem tieMin_iff_boundaryTie (c : Fin 11 → Point) (t : ℝ) :
    TieMin c t ↔ BoundaryTie c (circleMap t) := by
  constructor
  · rintro ⟨i,j,hij,heq,hle⟩
    have hi : circleMap t ∈ Cell c i := by
      intro k
      apply (dist_le_dist_iff_sq _ _ _).mpr
      rw [← sqDist_eq_dist_sq,← sqDist_eq_dist_sq]
      exact hle k
    have hj : circleMap t ∈ Cell c j := by
      intro k
      apply (dist_le_dist_iff_sq _ _ _).mpr
      rw [← sqDist_eq_dist_sq,← sqDist_eq_dist_sq,← heq]
      exact hle k
    exact ⟨circleMap_norm t,i,j,hij,hi,hj⟩
  · rintro ⟨_,i,j,hij,hi,hj⟩
    have heq := le_antisymm (hi j) (hj i)
    refine ⟨i,j,hij,?_,?_⟩
    · rw [sqDist_eq_dist_sq,sqDist_eq_dist_sq,heq]
    · intro k
      rw [sqDist_eq_dist_sq,sqDist_eq_dist_sq]
      exact (dist_le_dist_iff_sq _ _ _).mp (hi k)

theorem Representative.switch_iff_tieMin {c : Fin 11 → Point} {r t : ℝ}
    (h : Representative c r) (hr : r < 19/50) :
    SwitchAt c t ↔ TieMin c t := by
  refine ⟨switchAt_imp_tieMin,?_⟩
  intro ht
  obtain ⟨hx,i,j,hij,hi,hj⟩ := (tieMin_iff_boundaryTie c t).mp ht
  let I : Fin 9 := ⟨i.val,nearest_ring h.cover h.labels hx hi⟩
  let J : Fin 9 := ⟨j.val,nearest_ring h.cover h.labels hx hj⟩
  have hIJ : I ≠ J := fun he => hij (Fin.ext (congrArg (fun q : Fin 9 => q.val) he))
  exact Representative.tie_switch h hr hIJ hi hj

def BoundarySwitch (c : Fin 11 → Point) (x : Point) : Prop :=
  ∃ t : ℝ, circleMap t = x ∧ SwitchAt c t

theorem Representative.switch_set_eq_tie_set {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) :
    {x : Point | BoundarySwitch c x} = {x : Point | BoundaryTie c x} := by
  ext x
  constructor
  · rintro ⟨t,ht,hs⟩
    rw [← ht]
    exact (tieMin_iff_boundaryTie c t).mp (switchAt_imp_tieMin hs)
  · intro ht
    let t := circleAngle x
    have hp : circleMap t = x := circleMap_circleAngle _ ht.1
    refine ⟨t,hp,?_⟩
    apply (Representative.switch_iff_tieMin h hr).mpr
    apply (tieMin_iff_boundaryTie c t).mpr
    rwa [hp]

theorem Representative.switch_set_card {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) :
    {x : Point | BoundarySwitch c x}.ncard = 9 := by
  rw [Representative.switch_set_eq_tie_set h hr]
  exact NineTies.tie_set_card h hr v

end N11Formalization.ActualBoundarySwitches
#check @N11Formalization.ActualBoundarySwitches.Representative.switch_iff_tieMin
#check @N11Formalization.ActualBoundarySwitches.Representative.switch_set_card
#print axioms N11Formalization.ActualBoundarySwitches.Representative.switch_iff_tieMin
#print axioms N11Formalization.ActualBoundarySwitches.Representative.switch_set_card
