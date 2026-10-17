import N11Formalization.ActualRingEssentiality
import N11Formalization.ActualInwardNormalization

/-! ACTUAL ring midpoint directions are distinct and can be placed in
strict angular order by a coverage-preserving permutation fixing both hubs.
This is midpoint order, not yet connected ownership or a two-fan classification. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRingDirectionOrder
open DSHTopologyInterior ActualRingEssentiality

def ringSite (i : Fin 9) : Fin 11 := ⟨i.val, by omega⟩
def direction (c : Fin 11 → Point) (i : Fin 9) : Point := centerDir (c (ringSite i))
def midpointAngle (c : Fin 11 → Point) (i : Fin 9) : ℝ := circleAngle (direction c i)

theorem direction_injective {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) :
    Function.Injective (direction c) := by
  intro i j heq
  by_contra hij
  have hsites : ringSite i ≠ ringSite j := by
    intro h
    exact hij (Fin.ext (congrArg (fun q : Fin 11 => q.val) h))
  have hiMeet : MeetsCircle c r (ringSite i) := hR.ring_meets i.isLt
  have hjMeet : MeetsCircle c r (ringSite j) := hR.ring_meets j.isLt
  have hr1 : r < 1 := by linarith
  have hr0 := Covers.nonneg hc
  have hine : c (ringSite i) ≠ 0 := ActualInwardNormalization.touching_ne_zero hr1 hiMeet
  have hjne : c (ringSite j) ≠ 0 := ActualInwardNormalization.touching_ne_zero hr1 hjMeet
  obtain ⟨x,hx,hxi,hxother⟩ := private_circle_point hc hr hR i
  obtain ⟨y,hy,hyj,hyother⟩ := private_circle_point hc hr hR j
  have hix := ((cap_eq_of_meets hine hr0 hr1 hiMeet hx).1).mp hxi
  have hjy := ((cap_eq_of_meets hjne hr0 hr1 hjMeet hy).1).mp hyj
  have hjx : inner ℝ x (direction c j) < Real.cos (capHalfWidth (c (ringSite j)) r) := by
    by_contra h
    have hd := ((cap_eq_of_meets hjne hr0 hr1 hjMeet hx).1).mpr (le_of_not_gt h)
    exact not_le_of_gt (hxother (ringSite j) hsites.symm) hd
  have hiy : inner ℝ y (direction c i) < Real.cos (capHalfWidth (c (ringSite i)) r) := by
    by_contra h
    have hd := ((cap_eq_of_meets hine hr0 hr1 hiMeet hy).1).mpr (le_of_not_gt h)
    exact not_le_of_gt (hyother (ringSite i) hsites) hd
  change Real.cos (capHalfWidth (c (ringSite i)) r) ≤ inner ℝ x (direction c i) at hix
  change Real.cos (capHalfWidth (c (ringSite j)) r) ≤ inner ℝ y (direction c j) at hjy
  rw [heq] at hix hiy
  linarith

theorem midpointAngle_injective {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) :
    Function.Injective (midpointAngle c) := by
  intro i j heq
  apply direction_injective hc hr hR
  have hr1 : r < 1 := by linarith
  have hi : ‖direction c i‖ = 1 :=
    centerDir_norm (ActualInwardNormalization.touching_ne_zero hr1 (hR.ring_meets i.isLt))
  have hj : ‖direction c j‖ = 1 :=
    centerDir_norm (ActualInwardNormalization.touching_ne_zero hr1 (hR.ring_meets j.isLt))
  calc
    direction c i = circleMap (midpointAngle c i) := (circleMap_circleAngle _ hi).symm
    _ = circleMap (midpointAngle c j) := congrArg circleMap heq
    _ = direction c j := circleMap_circleAngle _ hj

theorem exists_sorted_perm (f : Fin 9 → ℝ) (hf : Function.Injective f) :
    ∃ p : Equiv.Perm (Fin 9), StrictMono (fun i : Fin 9 => f (p i)) := by
  classical
  let S : Finset ℝ := Finset.univ.image f
  have hcard : S.card = 9 := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  let g : Fin 9 → S := fun i => ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j h
      exact hf (congrArg Subtype.val h)
    · intro y
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp y.2
      exact ⟨i,Subtype.ext hi⟩
  let q : Fin 9 ≃ S := Equiv.ofBijective g hg
  let e : Fin 9 ≃o S := S.orderIsoOfFin hcard
  let p : Equiv.Perm (Fin 9) := e.toEquiv.trans q.symm
  have hp (i : Fin 9) : f (p i) = (e i).val := by
    change (q (q.symm (e i))).val = (e i).val
    rw [q.apply_symm_apply]
  refine ⟨p, ?_⟩
  intro i j hij
  change f (p i) < f (p j)
  rw [hp,hp]
  exact e.strictMono hij

def extendRingPerm (p : Equiv.Perm (Fin 9)) : Equiv.Perm (Fin 11) :=
  (finSumFinEquiv.symm.trans (p.sumCongr (Equiv.refl (Fin 2)))).trans finSumFinEquiv

theorem extendRingPerm_ring (p : Equiv.Perm (Fin 9)) (i : Fin 9) :
    extendRingPerm p (ringSite i) = ringSite (p i) := by
  have hleft (k : Fin 9) :
      (finSumFinEquiv : (Fin 9 ⊕ Fin 2) ≃ Fin 11) (Sum.inl k) = ringSite k := rfl
  change finSumFinEquiv ((p.sumCongr (Equiv.refl (Fin 2)))
    (finSumFinEquiv.symm (ringSite i))) = ringSite (p i)
  rw [← hleft i,Equiv.symm_apply_apply]
  rfl

theorem extendRingPerm_hub9 (p : Equiv.Perm (Fin 9)) : extendRingPerm p 9 = 9 := by
  have h : (finSumFinEquiv : (Fin 9 ⊕ Fin 2) ≃ Fin 11) (Sum.inr (0 : Fin 2)) = 9 := rfl
  change finSumFinEquiv ((p.sumCongr (Equiv.refl (Fin 2)))
    (finSumFinEquiv.symm (9 : Fin 11))) = 9
  rw [← h,Equiv.symm_apply_apply]
  rfl

theorem extendRingPerm_hub10 (p : Equiv.Perm (Fin 9)) : extendRingPerm p 10 = 10 := by
  have h : (finSumFinEquiv : (Fin 9 ⊕ Fin 2) ≃ Fin 11) (Sum.inr (1 : Fin 2)) = 10 := rfl
  change finSumFinEquiv ((p.sumCongr (Equiv.refl (Fin 2)))
    (finSumFinEquiv.symm (10 : Fin 11))) = 10
  rw [← h,Equiv.symm_apply_apply]
  rfl

theorem extendRingPerm_ring_iff (p : Equiv.Perm (Fin 9)) (i : Fin 11) :
    (extendRingPerm p i).val < 9 ↔ i.val < 9 := by
  by_cases hi : i.val < 9
  · let k : Fin 9 := ⟨i.val,hi⟩
    have hk : ringSite k = i := rfl
    rw [← hk,extendRingPerm_ring]
    exact iff_of_true (p k).isLt k.isLt
  · have hc : i = (9 : Fin 11) ∨ i = 10 := by
      have hv := i.isLt
      have : i.val = 9 ∨ i.val = 10 := by omega
      exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    rcases hc with rfl | rfl
    · rw [extendRingPerm_hub9]
    · rw [extendRingPerm_hub10]

theorem relabeled_ringLabels (p : Equiv.Perm (Fin 9)) {c : Fin 11 → Point} {r : ℝ}
    (hR : RingLabels c r) : RingLabels (fun i => c (extendRingPerm p i)) r := by
  intro i
  exact (hR (extendRingPerm p i)).trans (extendRingPerm_ring_iff p i)

theorem exists_ordered_cover {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) :
    ∃ p : Equiv.Perm (Fin 9),
      Covers (fun i => c (extendRingPerm p i)) r ∧
      RingLabels (fun i => c (extendRingPerm p i)) r ∧
      StrictMono (midpointAngle (fun i => c (extendRingPerm p i))) := by
  obtain ⟨p,hp⟩ := exists_sorted_perm (midpointAngle c) (midpointAngle_injective hc hr hR)
  refine ⟨p,covers_relabel (extendRingPerm p) hc,relabeled_ringLabels p hR,?_⟩
  have he (i : Fin 9) :
      midpointAngle (fun j => c (extendRingPerm p j)) i = midpointAngle c (p i) := by
    unfold midpointAngle direction
    change circleAngle (centerDir (c (extendRingPerm p (ringSite i)))) =
      circleAngle (centerDir (c (ringSite (p i))))
    rw [extendRingPerm_ring]
  intro i j hij
  change midpointAngle (fun k => c (extendRingPerm p k)) i <
    midpointAngle (fun k => c (extendRingPerm p k)) j
  rw [he,he]
  exact hp hij

end N11Formalization.ActualRingDirectionOrder
#check @N11Formalization.ActualRingDirectionOrder.direction_injective
#check @N11Formalization.ActualRingDirectionOrder.exists_ordered_cover
#print axioms N11Formalization.ActualRingDirectionOrder.direction_injective
#print axioms N11Formalization.ActualRingDirectionOrder.exists_ordered_cover
