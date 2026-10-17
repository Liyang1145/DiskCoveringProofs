import N11Formalization.ActualQ0BoundaryFans
import N11Formalization.ResumeNetwork

/-! Legitimate arbitrary cyclic ring cut and hub exchange.
The frozen canonical face table is read, never redefined. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCanonicalSitePermutation
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualQ0BoundaryFans ResumeNetwork

def hubPerm (b : Bool) : Equiv.Perm (Fin 11) :=
  if b then Equiv.refl _ else Equiv.swap 9 10

theorem hubPerm_ring : ∀ b : Bool, ∀ i : Fin 9,
    hubPerm b (ringSite i)=ringSite i := by decide +kernel

theorem hubPerm_hub9 : ∀ b : Bool, hubPerm b 9=hubSite b := by decide +kernel
theorem hubPerm_hub10 : ∀ b : Bool, hubPerm b 10=hubSite (!b) := by decide +kernel

def canonicalPerm (k : Fin 9) (b : Bool) : Equiv.Perm (Fin 11) :=
  (hubPerm b).trans (extendRingPerm (Equiv.addRight k))

theorem canonicalPerm_ring (k : Fin 9) (b : Bool) (i : Fin 9) :
    canonicalPerm k b (ringSite i)=ringSite (i+k) := by
  rw [canonicalPerm,Equiv.trans_apply,hubPerm_ring,extendRingPerm_ring]
  rfl

theorem canonicalPerm_hub9 (k : Fin 9) (b : Bool) :
    canonicalPerm k b 9=hubSite b := by
  rw [canonicalPerm,Equiv.trans_apply,hubPerm_hub9]
  cases b <;> simp only [hubSite,Bool.false_eq_true,if_false,if_true,
    extendRingPerm_hub9,extendRingPerm_hub10]

theorem canonicalPerm_hub10 (k : Fin 9) (b : Bool) :
    canonicalPerm k b 10=hubSite (!b) := by
  rw [canonicalPerm,Equiv.trans_apply,hubPerm_hub10]
  cases b <;> simp only [hubSite,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,
    extendRingPerm_hub9,extendRingPerm_hub10]

theorem canonical_fan_table : ∀ i : Fin 9,
    ({face ⟨i.val,by omega⟩ 0,face ⟨i.val,by omega⟩ 1,face ⟨i.val,by omega⟩ 2} :
      Finset (Fin 11)) =
      {ringSite i,ringSite (nextRing i),if i.val<4 then 9 else 10} := by
  decide +kernel

theorem canonical_central_table :
    ({face 9 0,face 9 1,face 9 2} : Finset (Fin 11)) = {0,9,10} ∧
      ({face 10 0,face 10 1,face 10 2} : Finset (Fin 11)) = {4,9,10} := by
  decide +kernel

theorem next_shift (i k : Fin 9) : ringSite (nextRing i+k)=nextSite (i+k) := by
  unfold nextSite nextRing
  congr 1
  abel

end N11Formalization.ActualCanonicalSitePermutation
#check @N11Formalization.ActualCanonicalSitePermutation.canonicalPerm_ring
#check @N11Formalization.ActualCanonicalSitePermutation.canonical_fan_table
#print axioms N11Formalization.ActualCanonicalSitePermutation.canonicalPerm_ring
#print axioms N11Formalization.ActualCanonicalSitePermutation.canonical_fan_table
