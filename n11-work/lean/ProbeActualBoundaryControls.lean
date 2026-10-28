import N11Formalization.ActualBoundarySwitches
import N11Formalization.ActualCapClusterLift

/-! Negative controls: nearest tie!=switch for coincident sites; an abstract
arccos interval may be nonempty for an EMPTY actual cap. These demonstrate
why private-point transversality and actual cap-meeting cannot be erased. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeActualBoundaryControls
open DSHTopologyOwnership DSHTopologyOwnershipSwitches DSHTopologyOwnershipSwitchCount
open ActualBoundaryArcFrame ActualCapClusterLift

def coincident : Fin 11 → Point := fun _ => 0

theorem coincident_owner (t : ℝ) : ownerAngle coincident t = 0 := by
  apply ownerAngle_eq_of_owns
  refine ⟨fun j => le_rfl,?_⟩
  intro j hj
  exact False.elim (Fin.not_lt_zero j hj)

theorem tie_without_switch (t : ℝ) : TieMin coincident t ∧ ¬ SwitchAt coincident t := by
  constructor
  · exact ⟨0,1,by decide,rfl,fun _ => le_rfl⟩
  · intro hs
    apply hs
    refine ⟨1,by norm_num,?_⟩
    intro u v hu1 hu2 hv1 hv2
    rw [coincident_owner,coincident_owner]

theorem spurious_big_arc : ∃ p : Point, p ≠ 0 ∧
    (BigArc p 0 0).Nonempty ∧ ¬ ∃ x : Point, ‖x‖ = 1 ∧ dist x p ≤ 0 := by
  let p : Point := (2:ℝ) • circleMap 0
  have hn : ‖p‖ = 2 := by
    rw [norm_smul,Real.norm_eq_abs,circleMap_norm]
    norm_num
  have hp : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
  refine ⟨p,hp,⟨bigMidpoint p,?_,?_⟩,?_⟩
  · change bigMidpoint p+(0:ℤ)*period-capHalfWidth p (2*0) ≤ bigMidpoint p
    norm_num
    linarith [capHalfWidth_nonneg p 0]
  · change bigMidpoint p ≤ bigMidpoint p+(0:ℤ)*period+capHalfWidth p (2*0)
    norm_num
    linarith [capHalfWidth_nonneg p 0]
  · rintro ⟨x,hx,hd⟩
    have ht := norm_le_norm_add_norm_sub x p
    rw [← dist_eq_norm,hx,hn] at ht
    linarith

end N11Formalization.ProbeActualBoundaryControls
#check @N11Formalization.ProbeActualBoundaryControls.tie_without_switch
#check @N11Formalization.ProbeActualBoundaryControls.spurious_big_arc
#print axioms N11Formalization.ProbeActualBoundaryControls.tie_without_switch
#print axioms N11Formalization.ProbeActualBoundaryControls.spurious_big_arc
