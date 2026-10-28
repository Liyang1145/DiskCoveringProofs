import N11Formalization.ActualQ0FourRunNormalization
import N11Formalization.ActualCanonicalSitePermutation
import N11Formalization.ActualMainRoute

/-! Productive full canonical33 nearest rows from ACTUAL q0(6,7).
The input q0/degree class remains explicit; its metric exclusions are
UNPAID. Legitimate cycliccut/hubswap, all11 original primal witnesses,
including canonical slack faces5/7; no symmetric/source-center premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ0CanonicalNearestRows
open ActualCoverStructuralReduction ActualFiniteNearestRefinement ActualRefinementEarCount
open ActualRefinementTriangleUniqueness ActualHubTriangleCensus ActualQ0BoundaryFans
open ActualQ0OrderedTwoFans ActualQ0FourRunNormalization
open ActualCanonicalSitePermutation ActualRingDirectionOrder ActualRingLinkBoundaryData
open ResumeNetwork ActualRefinementSideMultiplicity

def rawLabels (f : Fin 11) : Finset (Fin 11) := {face f 0,face f 1,face f 2}

theorem canonical_image_fan (k : Fin 9) (b : Bool) (i : Fin 9) :
    (rawLabels ⟨i.val,by omega⟩).image (canonicalPerm k b) =
      {ringSite (i+k),nextSite (i+k),if i.val<4 then hubSite b else hubSite (!b)} := by
  unfold rawLabels
  rw [canonical_fan_table,Finset.image_insert,Finset.image_insert,Finset.image_singleton,
    canonicalPerm_ring,canonicalPerm_ring,next_shift]
  by_cases hi : i.val < 4
  · rw [if_pos hi,if_pos hi,canonicalPerm_hub9]
  · rw [if_neg hi,if_neg hi,canonicalPerm_hub10]

theorem canonical_image_central (k : Fin 9) (b : Bool) :
    (rawLabels 9).image (canonicalPerm k b) = {9,10,ringSite k} ∧
      (rawLabels 10).image (canonicalPerm k b) = {9,10,ringSite ((4 : Fin 9)+k)} := by
  have h9 : rawLabels 9 = {ringSite 0,9,10} := canonical_central_table.1
  have h10 : rawLabels 10 = {ringSite 4,9,10} := canonical_central_table.2
  rw [h9,h10,Finset.image_insert,Finset.image_insert,Finset.image_singleton,
    Finset.image_insert,Finset.image_insert,Finset.image_singleton,
    canonicalPerm_ring,canonicalPerm_ring,zero_add,
    canonicalPerm_hub9,canonicalPerm_hub10]
  cases b <;> constructor <;> ext x <;>
    simp only [hubSite,Bool.false_eq_true,Bool.not_false,Bool.not_true,if_false,if_true,
      Finset.mem_insert,Finset.mem_singleton] <;> tauto

theorem actual_q0_canonical_label_faces {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (O : OrderedData R) (h4 : O.run_length.val=4) :
    ∀ f : Fin 11, ∃ A : R.Index,
      (rawLabels f).image (canonicalPerm O.cut (O.fans.colors O.cut)) = labelSet R A := by
  intro f
  by_cases hf : f.val < 9
  · let i : Fin 9 := ⟨f.val,hf⟩
    have he : (⟨i.val,by omega⟩ : Fin 11)=f := Fin.ext rfl
    refine ⟨O.fans.faces (i+O.cut),?_⟩
    rw [← he,canonical_image_fan,ActualQ0OrderedTwoFans.OrderedData.true_shifted_fan,h4]
  · have hc : f=9 ∨ f=10 := by
      have hb := f.isLt
      have hh : f.val=9 ∨ f.val=10 := by omega
      exact hh.imp (fun he => Fin.ext he) (fun he => Fin.ext he)
    rcases hc with rfl | rfl
    · obtain ⟨A,hA⟩ := O.central_first
      exact ⟨A,(canonical_image_central O.cut (O.fans.colors O.cut)).1.trans hA.symm⟩
    · obtain ⟨A,hA⟩ := O.central_second
      rw [four_run_second O h4] at hA
      exact ⟨A,(canonical_image_central O.cut (O.fans.colors O.cut)).2.trans hA.symm⟩

theorem actual_q0_six_seven_canonical_nearest {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=0)
    (hd : min (neighbors R 9).card (neighbors R 10).card=6 ∧
      max (neighbors R 9).card (neighbors R 10).card=7) :
    ∃ (k : Fin 9) (e : Equiv.Perm (Fin 11)) (Z : Fin 11 → Point),
      (∀ i : Fin 9, e (ringSite i)=ringSite (i+k)) ∧
      (∀ f : Fin 11, ‖Z f‖ < 1) ∧
      ∀ f : Fin 11, ∀ v : Fin 3, Z f ∈ ActualVoronoiCells.Cell c (e (face f v)) ∧
        dist (Z f) (c (e (face f v))) ≤ r := by
  classical
  obtain ⟨O,h4⟩ := actual_q0_four_run_data h hr R hq hd
  let e := canonicalPerm O.cut (O.fans.colors O.cut)
  have hfaces (f : Fin 11) : ∃ A : R.Index, (rawLabels f).image e = labelSet R A :=
    actual_q0_canonical_label_faces O h4 f
  let A := fun f => Classical.choose (hfaces f)
  let Z := fun f => R.witness (A f)
  refine ⟨O.cut,e,Z,canonicalPerm_ring _ _,fun f => (Refinement.real_triangle R (A f)).1,?_⟩
  intro f v
  have hm : e (face f v) ∈ (rawLabels f).image e := by
    apply Finset.mem_image.mpr
    refine ⟨face f v,?_,rfl⟩
    fin_cases v <;> simp [rawLabels]
  rw [Classical.choose_spec (hfaces f)] at hm
  obtain ⟨s,hs⟩ := mem_labelSet.mp hm
  change R.witness (A f) ∈ ActualVoronoiCells.Cell c (e (face f v)) ∧
    dist (R.witness (A f)) (c (e (face f v))) ≤ r
  rw [← hs]
  exact (Refinement.real_triangle R (A f)).2.1 s

/-- Exact remaining metric-classification producer, UNPAID. It keeps
arbitrary representatives and every actual coherent refinement. -/
def RemainingMetricClassification : Prop :=
  ∀ (c : Fin 11 → Point) (r : ℝ), Representative c r →
    r < SourceExactRoot.sourceRadius → ∀ R : Refinement c r,
      (ringOnlyTriangles R).card=0 ∧
        min (neighbors R 9).card (neighbors R 10).card=6 ∧
        max (neighbors R 9).card (neighbors R 10).card=7

theorem canonical_nearest_of_metric (hm : RemainingMetricClassification) :
    ActualMainRoute.CanonicalNearest33Obligation := by
  intro c r h hr
  have hr0 : r < 19/50 := hr.trans
    (SourceExactRoot.sourceRadius_mem_box.2.trans_lt boxHiCert_six_lt_R0_real)
  obtain ⟨R⟩ := actual_refinement h hr0
  obtain ⟨hq,h6,h7⟩ := hm c r h hr R
  obtain ⟨k,e,Z,he,hZ,hrows⟩ := actual_q0_six_seven_canonical_nearest h hr0 R hq ⟨h6,h7⟩
  exact ⟨k,e,Z,he,fun f => (hZ f).le,fun f v => (hrows f v).1⟩

theorem main_of_metric_remaining
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (hmetric : RemainingMetricClassification) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMainRoute.main_of_actual_nearest_remaining h450 henergy
    (canonical_nearest_of_metric hmetric)

end N11Formalization.ActualQ0CanonicalNearestRows
#check @N11Formalization.ActualQ0CanonicalNearestRows.actual_q0_six_seven_canonical_nearest
#print N11Formalization.ActualQ0CanonicalNearestRows.RemainingMetricClassification
#check @N11Formalization.ActualQ0CanonicalNearestRows.canonical_nearest_of_metric
#check @N11Formalization.ActualQ0CanonicalNearestRows.main_of_metric_remaining
#print axioms N11Formalization.ActualQ0CanonicalNearestRows.actual_q0_six_seven_canonical_nearest
#print axioms N11Formalization.ActualQ0CanonicalNearestRows.canonical_nearest_of_metric
#print axioms N11Formalization.ActualQ0CanonicalNearestRows.main_of_metric_remaining
