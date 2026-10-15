import N11Formalization.ActualRefinementLinkDegrees
import N11Formalization.ActualNearestPairRigidity
import N11Formalization.ActualRefinementGraphConnected

/-! Each selected local3/4/5-gon fan link is connected on its actual
neighbors, proved by finite kernel enumeration then transported by a genuine
graph homomorphism into the global actual refinement link. Global hub-link
connectedness is NOT an input or claimed by this local theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementLocalLinks
open ActualFiniteNearestRefinement ActualIncidentFanRefinement
open ActualRefinementTriangleUniqueness ActualRefinementSideMultiplicity

def linkGraph {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i : Fin 11) :
    SimpleGraph (Fin 11) where
  Adj j k := j ≠ k ∧ j ≠ i ∧ k ≠ i ∧
    ∃ a : R.Index, i ∈ labelSet R a ∧ j ∈ labelSet R a ∧ k ∈ labelSet R a
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2.1,h.2.1,by
    obtain ⟨a,hi,hj,hk⟩ := h.2.2.2
    exact ⟨a,hi,hk,hj⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def localNeighbor {n : ℕ} (hn : 0 < n) (I J : Fin n) : Prop :=
  J ≠ I ∧ ∃ k : Fin n, FanIndex k ∧ I ∈ indexTriangle hn k ∧ J ∈ indexTriangle hn k

instance {n : ℕ} (hn : 0 < n) (I J : Fin n) : Decidable (localNeighbor hn I J) := by
  unfold localNeighbor
  infer_instance

def localLink {n : ℕ} (hn : 0 < n) (I : Fin n) : SimpleGraph (Fin n) where
  Adj J K := J ≠ K ∧ J ≠ I ∧ K ≠ I ∧
    ∃ a : Fin n, FanIndex a ∧ I ∈ indexTriangle hn a ∧
      J ∈ indexTriangle hn a ∧ K ∈ indexTriangle hn a
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2.1,h.2.1,by
    obtain ⟨a,ha,hI,hJ,hK⟩ := h.2.2.2
    exact ⟨a,ha,hI,hK,hJ⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {n : ℕ} (hn : 0 < n) (I : Fin n) : DecidableRel (localLink hn I).Adj := by
  intro J K
  unfold localLink
  infer_instance

theorem local_fan_link_connected {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    ∀ I J K : Fin n, localNeighbor (by omega : 0 < n) I J →
      localNeighbor (by omega : 0 < n) I K →
      (localLink (by omega : 0 < n) I).Reachable J K := by
  interval_cases n <;> decide +revert

def localLinkHom {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (v : R.vertices)
    (I : Fin (ActualVoronoiIncidence.incident c (R.face v).point).card) :
    localLink (lt_of_lt_of_le (by decide : 0 < 3) (R.face v).at_least_three) I →g
      linkGraph R ((R.order v).order I).val where
  toFun J := ((R.order v).order J).val
  map_rel' := by
    intro J K hJK
    have hinj := ActualIncidentFacetAdjacency.OrderedCircle.label_injective (R.order v)
    obtain ⟨hJK,hJI,hKI,a,ha,hI,hJ,hK⟩ := hJK
    let A : {k : Fin (ActualVoronoiIncidence.incident c (R.face v).point).card // FanIndex k} := ⟨a,ha⟩
    exact ⟨hinj.ne hJK,hinj.ne hJI,hinj.ne hKI,⟨v,A⟩,
      (local_label_mem R v A I).mpr hI,
      (local_label_mem R v A J).mpr hJ,
      (local_label_mem R v A K).mpr hK⟩

theorem actual_local_link_reachable {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (v : R.vertices)
    (I J K : Fin (ActualVoronoiIncidence.incident c (R.face v).point).card)
    (hJ : localNeighbor (lt_of_lt_of_le (by decide : 0 < 3) (R.face v).at_least_three) I J)
    (hK : localNeighbor (lt_of_lt_of_le (by decide : 0 < 3) (R.face v).at_least_three) I K) :
    (linkGraph R ((R.order v).order I).val).Reachable
      ((R.order v).order J).val ((R.order v).order K).val :=
  (local_fan_link_connected (R.face v).at_least_three (R.face v).at_most_five I J K hJ hK).map
    (localLinkHom R v I)

end N11Formalization.ActualRefinementLocalLinks
#check @N11Formalization.ActualRefinementLocalLinks.actual_local_link_reachable
#print axioms N11Formalization.ActualRefinementLocalLinks.local_fan_link_connected
#print axioms N11Formalization.ActualRefinementLocalLinks.actual_local_link_reachable
