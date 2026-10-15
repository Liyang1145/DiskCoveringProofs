import N11Formalization.ActualCircularSectorClosure

/-! Aggregate the nine genuine nearest-neighbor switch area atoms.

The switch data are chosen from `NineTies`; this is an actual nearest-tie
consumer, not an anchor-endpoint surrogate.  The result is only the exact
positive finite sum of switch atoms, leaving the clipped-cell area bridge
explicit.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSwitchAtomAggregate
open ActualCoverStructuralReduction ActualBoundaryNineTies
open ActualBoundarySwitchMetric ActualBoundarySwitchAngles
open ActualBoundaryNeighborTies ActualRingDirectionOrder ActualBoundaryCyclicOrder
open ActualRingLinkBoundaryData

noncomputable def switchData
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) (i : Fin 9) :
    SwitchData (c (ringSite i)) (c (nextSite i)) (circleMap (v.tie i).angle) r :=
  Classical.choice (actual_boundary_switch_metric h hr i (v.tie i))

theorem switchData_spec
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) (i : Fin 9) :
    (switchData h hr v i).radius^2 *
        Real.sin (2*SwitchData.angle (switchData h hr v i))/2 =
      (switchData h hr v i).chord * (switchData h hr v i).offset :=
  SwitchData.exact_area_atom (switchData h hr v i)

theorem switch_atom_pos
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) (i : Fin 9) :
    0 < (switchData h hr v i).chord * (switchData h hr v i).offset :=
  mul_pos (switchData h hr v i).chord_pos
    (switchData h hr v i).offset_pos

theorem switch_atom_sum_pos
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) :
    0 < ∑ i : Fin 9,
      (switchData h hr v i).chord * (switchData h hr v i).offset := by
  apply Finset.sum_pos
  · intro i hi
    exact switch_atom_pos h hr v i
  · exact Finset.univ_nonempty

theorem switch_area_sum_eq_atom_sum
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) :
    (∑ i : Fin 9,
      (switchData h hr v i).radius^2 *
        Real.sin (2*SwitchData.angle (switchData h hr v i))/2) =
      ∑ i : Fin 9,
        (switchData h hr v i).chord * (switchData h hr v i).offset := by
  apply Finset.sum_congr rfl
  intro i hi
  exact switchData_spec h hr v i

end N11Formalization.ActualSwitchAtomAggregate
#check @N11Formalization.ActualSwitchAtomAggregate.switch_atom_sum_pos
#check @N11Formalization.ActualSwitchAtomAggregate.switch_area_sum_eq_atom_sum
#print axioms N11Formalization.ActualSwitchAtomAggregate.switch_atom_sum_pos
