import N11Formalization.ActualBoundaryChartRelabeling
import N11Formalization.ActualHubEdgeEndpoints
import N11Formalization.C450Source11Segment
import N11Formalization.EnergyTerminalBatchB11

/-! The actual unrestricted main-route consumer, with ALL unpaid inputs named.
Not an unconditional solution. It does not assume a lower-bound conclusion,
source-candidate faces, symmetry, genericity, or canonical0/4 before proof.
The only remaining mathematics is the actual canonical33 producer; the two
certificate obligations retain their precise historical remaining families. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualMainRoute
open ActualCoverStructuralReduction ActualBoundaryChart ActualBoundaryChartRelabeling
open ActualBoundaryCyclicOrder ActualRingDirectionOrder SourceChartIsometry ResumeNetwork

/-- Produce the ACTUAL33 canonical graph inequalities after choosing a cyclic
ring cut and a permissible hub permutation. It is an UNPAID geometric task,
not a field of Representative, not an axiom, and not a lower-bound premise.
The original radius is unchanged. The witnesses need not be assumed source
or symmetric; proving they are actual common-nearest vertices is one valid
way to pay the inequalities. -/
def Canonical33Obligation : Prop :=
  ∀ (c : Fin 11 → Point) (r : ℝ), Representative c r →
    r < SourceExactRoot.sourceRadius →
    ∃ (k : Fin 9) (e : Equiv.Perm (Fin 11)) (Z : Fin 11 → Point),
      (∀ i : Fin 9, e (ringSite i) = ringSite (i+k)) ∧
      ∀ f : Fin 11, ∀ v : Fin 3, dist (c (e (face f v))) (Z f) ≤ r

/-- Strong actual-primal-vertex target for the geometry team. A clipped
refinement keeps original nearest vertices even for artificial diagonals.
This obligation is UNPAID; its type does not assert a candidate table for
an arbitrary cover. The source-free consumer below turns it into the33
metric rows using ACTUAL Covers, rather than assuming their radii. -/
def CanonicalNearest33Obligation : Prop :=
  ∀ (c : Fin 11 → Point) (r : ℝ), Representative c r →
    r < SourceExactRoot.sourceRadius →
    ∃ (k : Fin 9) (e : Equiv.Perm (Fin 11)) (Z : Fin 11 → Point),
      (∀ i : Fin 9, e (ringSite i) = ringSite (i+k)) ∧
      (∀ f : Fin 11, ‖Z f‖ ≤ 1) ∧
      ∀ f : Fin 11, ∀ v : Fin 3, Z f ∈ ActualVoronoiCells.Cell c (e (face f v))

theorem canonical33_of_actual_nearest (hnearest : CanonicalNearest33Obligation) :
    Canonical33Obligation := by
  intro c r h hr
  obtain ⟨k,e,Z,he,hinside,hcells⟩ := hnearest c r h hr
  refine ⟨k,e,Z,he,?_⟩
  intro f v
  rw [dist_comm]
  exact ActualVoronoiCells.nearest_le_radius h.cover (mem_unitDisk.mpr (hinside f)) (hcells f v)

/-- All three unpaid obligations are explicit. Every other cover/chart
interface needed by the actual oracle is produced, rather than requested. -/
theorem lower_bound_of_remaining
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (h33 : Canonical33Obligation) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r := by
  intro r c hr0 hc
  by_contra hnot
  have hlt : r < SourceExactRoot.sourceRadius := lt_of_not_ge hnot
  have hs := C450Source11Segment.source_of_remaining h450
  obtain ⟨p,d,hd,_,_⟩ := representative_of_source hs hlt hc
  have hrR0 : r < 19/50 := hlt.trans
    (SourceExactRoot.sourceRadius_mem_box.2.trans_lt boxHiCert_six_lt_R0_real)
  obtain ⟨b⟩ := boundaryChart_of_cover hd.cover hrR0 hd.labels hd.midpoint_order
  obtain ⟨k,e,Z,he,hfaces⟩ := h33 d r hd hlt
  have hf := BoundaryChart.shifted_feasible_of_faces b hr0 k e he Z hfaces
  have hbound := EnergyTerminalBatchB11.chart_radius_of_remaining henergy
    (shiftY b.y k) (shiftY_nonneg b.nonneg k) (shiftY_sum b.sum_one k)
    (fun i => gaugeMap b k (d (e i))) (fun f => gaugeMap b k (Z f)) r hf
  exact not_le_of_gt hlt hbound

/-- SAME C891 root/coordinate6 plus the already proved attainment. Conditional
on exactly the three listed unpaid obligations; never counted as completion. -/
theorem main_of_remaining
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (h33 : Canonical33Obligation) : N11MainStatement SourceExactRoot.sourceRadius :=
  SourceExactRoot.main_of_lower_bound (lower_bound_of_remaining h450 henergy h33)

theorem main_of_actual_nearest_remaining
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (hnearest : CanonicalNearest33Obligation) : N11MainStatement SourceExactRoot.sourceRadius :=
  main_of_remaining h450 henergy (canonical33_of_actual_nearest hnearest)

end N11Formalization.ActualMainRoute
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#check @N11Formalization.ActualMainRoute.canonical33_of_actual_nearest
#check @N11Formalization.ActualMainRoute.lower_bound_of_remaining
#check @N11Formalization.ActualMainRoute.main_of_remaining
#print axioms N11Formalization.ActualMainRoute.lower_bound_of_remaining
#print axioms N11Formalization.ActualMainRoute.main_of_remaining
#print axioms N11Formalization.ActualMainRoute.canonical33_of_actual_nearest
#print axioms N11Formalization.ActualMainRoute.main_of_actual_nearest_remaining
