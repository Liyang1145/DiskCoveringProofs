import N11Formalization.ActualCanonicalMomentTransport
import N11Formalization.MetricSectorBoxCertificate

/-! Pure finite graph symmetries for the balanced Q1 family. The two
representatives correspond to the two HOST balanced starts after the
proved label shift. These statements relabel finite graphs and factors;
they impose no reflection symmetry on an actual metric configuration. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.CanonicalBalancedGraphOrbits
open ActualOrderedMetricGraphs ActualCanonicalSitePermutation ActualRingDirectionOrder
open ActualRingLinkBoundaryData ActualEarOwnedWidth
open MetricSectorCompactRegularity MetricSectorBoxCertificate

def ringReflection : Equiv.Perm (Fin 9) where
  toFun := fun i => -i
  invFun := fun i => -i
  left_inv := neg_neg
  right_inv := neg_neg

def reflectionPerm : Equiv.Perm (Fin 11) := extendRingPerm ringReflection

theorem reflection_ring (i : Fin 9) : reflectionPerm (ringSite i)=ringSite (-i) :=
  extendRingPerm_ring ringReflection i

theorem reflection_cycle : ∀ i : Fin 9,
    labelMap reflectionPerm (ActualEdgeFlagSums.cycleEdge i)=
      ActualEdgeFlagSums.cycleEdge (-i-1) := by
  decide +kernel

theorem reflection_sector_owner : ∀ i : Fin 9,
    reflectionPerm (nextSite i)=nextSite (-i-2) := by
  decide +kernel

theorem reflection_outside : ∀ i : Fin 9,
    i ∈ outsideGaps 0 ↔ -i-2 ∈ outsideGaps 0 := by
  decide +kernel

theorem reflection_ear : labelMap reflectionPerm q1Ear=q1Ear := by decide +kernel

theorem balanced_hub_exchange : ∀ k : Fin 8,
    (q1Faces k 4).image (labelMap (hubPerm false))=q1Faces (k+4) 4 := by
  decide +kernel

theorem balanced_reflection : ∀ k : Fin 8,
    (q1Faces k 4).image (labelMap reflectionPerm)=q1Faces (3-k) 4 := by
  decide +kernel

def representative (k : Fin 8) : Fin 8 := if k ∈ ({0,3,4,7} : Finset (Fin 8)) then 7 else 1

def usesReflection (k : Fin 8) : Bool := decide (k ∈ ({0,2,4,6} : Finset (Fin 8)))
def usesHubExchange (k : Fin 8) : Bool := decide (k ∈ ({0,3,5,6} : Finset (Fin 8)))

def orbitPerm (k : Fin 8) : Equiv.Perm (Fin 11) :=
  (if usesReflection k then reflectionPerm else Equiv.refl _).trans
    (if usesHubExchange k then hubPerm false else Equiv.refl _)

theorem representative_two : ∀ k : Fin 8, representative k=7 ∨ representative k=1 := by
  decide +kernel

theorem balanced_orbit : ∀ k : Fin 8,
    (q1Faces (representative k) 4).image (labelMap (orbitPerm k))=q1Faces k 4 := by
  decide +kernel

theorem balanced_orbit_edges (k : Fin 8) :
    (q1Edges (representative k) 4).image (labelMap (orbitPerm k))=q1Edges k 4 := by
  rw [q1Edges,← faceEdges_labelMap,balanced_orbit]
  rfl

theorem balanced_orbit_ear : ∀ k : Fin 8, labelMap (orbitPerm k) q1Ear=q1Ear := by
  decide +kernel

theorem chord_swap (a u v : ℝ) : chordLength a u v=chordLength a v u := by
  unfold chordLength
  congr 1
  ring

theorem width_swap (a u v : ℝ) : sectorWidth a u v=sectorWidth a v u := by
  unfold sectorWidth
  rw [chord_swap]

theorem sector_objective_swap (C mu dL dR bL bR a u v : ℝ) :
    sectorObjective C mu dL dR bL bR a u v=
      sectorObjective C mu dR dL bR bL a v u := by
  unfold sectorObjective sectorFactor
  rw [width_swap]
  ring

end N11Formalization.CanonicalBalancedGraphOrbits
#print axioms N11Formalization.CanonicalBalancedGraphOrbits.reflection_cycle
#print axioms N11Formalization.CanonicalBalancedGraphOrbits.reflection_sector_owner
#print axioms N11Formalization.CanonicalBalancedGraphOrbits.reflection_outside
#print axioms N11Formalization.CanonicalBalancedGraphOrbits.balanced_hub_exchange
#print axioms N11Formalization.CanonicalBalancedGraphOrbits.balanced_reflection
#print axioms N11Formalization.CanonicalBalancedGraphOrbits.balanced_orbit
#print axioms N11Formalization.CanonicalBalancedGraphOrbits.balanced_orbit_edges
#print axioms N11Formalization.CanonicalBalancedGraphOrbits.balanced_orbit_ear
#print axioms N11Formalization.CanonicalBalancedGraphOrbits.sector_objective_swap
