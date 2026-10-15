import N11Formalization.ActualSelectedRingEdges
import N11Formalization.ActualQ0BoundaryFans

/-! Pure cyclic coordinate data for the ACTUAL ear-deleted eight-cycle.
Deleting an arbitrary real ear middle label, not a symmetry restriction.
Seven original boundary sides and one short ear chord survive. -/
set_option autoImplicit false
namespace N11Formalization.ActualQ1CoreCycle
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualSelectedRingEdges

def coreSite (e : Fin 9) (i : Fin 8) : Fin 9 := e+⟨i.val+1,by omega⟩
def coreNext (i : Fin 8) : Fin 8 := i+1

def coreEdge (e : Fin 9) (i : Fin 8) : Finset (Fin 11) :=
  {ringSite (coreSite e i),ringSite (coreSite e (coreNext i))}

theorem coreSite_injective : ∀ e : Fin 9, Function.Injective (coreSite e) := by
  intro e i j he
  have hh := add_left_cancel he
  have hv := congrArg Fin.val hh
  apply Fin.ext
  change i.val+1=j.val+1 at hv
  omega

theorem core_sites_without_middle : ∀ e : Fin 9, ∀ j : Fin 9,
    (∃ i : Fin 8, coreSite e i=j) ↔ j ≠ e := by decide +kernel

theorem core_site_not_middle : ∀ e : Fin 9, ∀ i : Fin 8, coreSite e i ≠ e := by
  decide +kernel

theorem core_next_ne : ∀ i : Fin 8, coreNext i ≠ i := by decide +kernel

theorem core_edge_injective : ∀ e : Fin 9, Function.Injective (coreEdge e) := by
  decide +kernel

theorem core_seven_original_sides : ∀ e : Fin 9, ∀ i : Fin 8, i.val<7 →
    coreSite e (coreNext i)=nextRing (coreSite e i) := by decide +kernel

theorem core_chord_endpoints : ∀ e : Fin 9,
    coreSite e 7=e-1 ∧ coreSite e (coreNext 7)=nextRing e := by decide +kernel

theorem core_original_side_not_ear : ∀ e : Fin 9, ∀ i : Fin 8, i.val<7 →
    ¬ (ringSite (coreSite e i) ∈ ({prevSite e,ringSite e,nextSite e} : Finset (Fin 11)) ∧
      ringSite (coreSite e (coreNext i)) ∈
        ({prevSite e,ringSite e,nextSite e} : Finset (Fin 11))) := by decide +kernel

theorem core_ring_pair_hub_unique : ∀ e : Fin 9, ∀ i j : Fin 8, ∀ b d : Bool,
    ({ringSite (coreSite e i),ringSite (coreSite e (coreNext i)),
      ActualQ0BoundaryFans.hubSite b} : Finset (Fin 11)) =
    {ringSite (coreSite e j),ringSite (coreSite e (coreNext j)),
      ActualQ0BoundaryFans.hubSite d} → i=j ∧ b=d := by decide +kernel

end N11Formalization.ActualQ1CoreCycle
#check @N11Formalization.ActualQ1CoreCycle.core_seven_original_sides
#check @N11Formalization.ActualQ1CoreCycle.core_chord_endpoints
#check @N11Formalization.ActualQ1CoreCycle.core_ring_pair_hub_unique
#print axioms N11Formalization.ActualQ1CoreCycle.core_sites_without_middle
#print axioms N11Formalization.ActualQ1CoreCycle.core_ring_pair_hub_unique
