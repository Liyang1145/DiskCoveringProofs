import N11Formalization.ActualCanonicalFaceCoordinates
import N11Formalization.ActualSharedMomentRationalCertificate

/-! Canonical finite rational moment coefficients pulled back to true faces,
local slots, selected edges and cyclic switches. The proved coordinate chart
transports mask balance, factor coefficients and the complete dual constant.
No metric matching, moment equality or real factor bound is an input. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCanonicalMomentTransport

open ActualCanonicalFaceCoordinates ActualOrderedMetricGraphs ActualCanonicalSitePermutation
open ActualCoverStructuralReduction ActualFiniteNearestRefinement ActualEdgeFlagSums
open ActualRefinementDoubleCounting ActualSharedMomentRationalCertificate
open ActualRingDirectionOrder ActualRingLinkBoundaryData MetricAreaRationalCertificate
open ActualEarOwnedWidth

def edgeEquiv {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {p : Equiv.Perm (Fin 11)}
    (C : Coordinates R F p) : (edges R) ≃ (faceEdges F) where
  toFun e := ⟨labelMap p.symm e.val,(C.edge_mem_iff e.val).mp e.property⟩
  invFun e := ⟨labelMap p e.val,by
    apply (C.edge_mem_iff _).mpr
    rw [labelMap_symm_apply]
    exact e.property⟩
  left_inv e := Subtype.ext (labelMap_apply_symm p e.val)
  right_inv e := Subtype.ext (labelMap_symm_apply p e.val)

structure CanonicalCoeffQ (F : Finset (Finset (Fin 11))) where
  faceCard : ∀ f : F, f.val.card=3
  mu : Fin 11 → ℚ
  faceMask : F → Fin 3 → ℚ
  switchMask : Fin 9 → ℚ
  sideFirst : Finset (Fin 11) → ℚ
  sideSecond : Finset (Fin 11) → ℚ
  leftFirst : Fin 9 → ℚ
  leftSecond : Fin 9 → ℚ
  rightFirst : Fin 9 → ℚ
  rightSecond : Fin 9 → ℚ
  width : ℚ

theorem q0FaceCard : ∀ (m : Fin 9) (f : q0Faces m), f.val.card=3 := by
  decide +kernel

theorem q1FaceCard : ∀ (k m : Fin 8) (f : q1Faces k m), f.val.card=3 := by
  decide +kernel

def CanonicalCoeffQ.label {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (f : F) (s : Fin 3) : Fin 11 := canonicalLabel f.val (D.faceCard f) s

def CanonicalCoeffQ.flagEdge {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (f : F) (s : Fin 3) : Finset (Fin 11) := f.val.erase (D.label f s)

theorem canonicalFlagEdge_card {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (f : F) (s : Fin 3) : (D.flagEdge f s).card=2 := by
  have hm : D.label f s ∈ f.val := canonicalLabel_mem _ _ _
  have hh := Finset.card_erase_add_one hm
  rw [D.faceCard f] at hh
  unfold CanonicalCoeffQ.flagEdge
  omega

theorem canonicalFlagEdge_mem {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (f : F) (s : Fin 3) : D.flagEdge f s ∈ faceEdges F := by
  apply Finset.mem_biUnion.mpr
  exact ⟨f.val,f.property,Finset.mem_powersetCard.mpr
    ⟨Finset.erase_subset _ _,canonicalFlagEdge_card D f s⟩⟩

def canonicalFaceP {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (f : F) (s : Fin 3) : ℚ :=
  -D.mu (D.label f s)-kap (D.flagEdge f s)

def canonicalFaceQ {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (f : F) (s : Fin 3) : ℚ := D.faceMask f s*D.sideSecond (D.flagEdge f s)

def canonicalFaceB {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (f : F) (s : Fin 3) : ℚ := D.faceMask f s*D.sideFirst (D.flagEdge f s)

def canonicalSwitchP {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (i : Fin 9) : ℚ :=
  (∑ j ∈ cycleEdge i, D.mu j)-kap (cycleEdge i)

def canonicalSwitchQ {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F) (i : Fin 9) : ℚ :=
  D.switchMask i*D.sideSecond (cycleEdge i)

def canonicalSwitchB {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F) (i : Fin 9) : ℚ :=
  D.switchMask i*D.sideFirst (cycleEdge i)

def canonicalSwitchD2 {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F) (i : Fin 9) : ℚ :=
  D.leftSecond i+D.rightSecond (i-1)

def canonicalSwitchD1 {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F) (i : Fin 9) : ℚ :=
  D.leftFirst i+D.rightFirst (i-1)

def pullbackKap (cut : Fin 9) (b : Bool) (kap : Finset (Fin 11) → ℚ)
    (e : Finset (Fin 11)) : ℚ := kap (labelMap (canonicalPerm cut b).symm e)

def pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) : CoeffQ R where
  mu := fun i => D.mu ((canonicalPerm cut b).symm i)
  faceMask := fun A s => D.faceMask (C.faceEquiv A) (C.slotPerm A s)
  switchMask := fun i => D.switchMask (i-cut)
  sideFirst := fun e => D.sideFirst (labelMap (canonicalPerm cut b).symm e)
  sideSecond := fun e => D.sideSecond (labelMap (canonicalPerm cut b).symm e)
  leftFirst := fun i => D.leftFirst (i-cut)
  leftSecond := fun i => D.leftSecond (i-cut)
  rightFirst := fun i => D.rightFirst (i-cut)
  rightSecond := fun i => D.rightSecond (i-cut)
  width := D.width

theorem canonicalPerm_nextSite (cut : Fin 9) (b : Bool) (i : Fin 9) :
    canonicalPerm cut b (nextSite i)=nextSite (i+cut) := by
  unfold nextSite
  rw [canonicalPerm_ring]
  exact next_shift i cut

theorem cycleEdge_transport (cut : Fin 9) (b : Bool) (i : Fin 9) :
    labelMap (canonicalPerm cut b) (cycleEdge i)=cycleEdge (i+cut) := by
  simp only [labelMap,cycleEdge,Finset.image_insert,Finset.image_singleton,
    canonicalPerm_ring,canonicalPerm_nextSite]

theorem inverse_cycleEdge (cut : Fin 9) (b : Bool) (i : Fin 9) :
    labelMap (canonicalPerm cut b).symm (cycleEdge i)=cycleEdge (i-cut) := by
  have hh := cycleEdge_transport cut b (i-cut)
  rw [sub_add_cancel] at hh
  rw [← hh,labelMap_symm_apply]

theorem label_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) (A : R.Index) (s : Fin 3) :
    (canonicalPerm cut b).symm (R.labels A s)=D.label (C.faceEquiv A) (C.slotPerm A s) := by
  rw [C.slot_label,Equiv.symm_apply_apply]
  rfl

theorem flag_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) (A : R.Index) (s : Fin 3) :
    labelMap (canonicalPerm cut b).symm (ActualEdgeFlagSums.flagEdge R A s)=
      D.flagEdge (C.faceEquiv A) (C.slotPerm A s) := by
  rw [C.inverse_flag_eq]
  rfl

theorem faceP_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (A : R.Index) (s : Fin 3) :
    faceP (pullback C D) (pullbackKap cut b kap) A s=
      canonicalFaceP D kap (C.faceEquiv A) (C.slotPerm A s) := by
  unfold faceP pullback pullbackKap canonicalFaceP
  dsimp only
  rw [label_pullback C D,flag_pullback C D]

theorem faceQ_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) (A : R.Index) (s : Fin 3) :
    faceQ (pullback C D) A s=canonicalFaceQ D (C.faceEquiv A) (C.slotPerm A s) := by
  unfold faceQ pullback canonicalFaceQ
  dsimp only
  rw [flag_pullback C D]

theorem faceB_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) (A : R.Index) (s : Fin 3) :
    faceB (pullback C D) A s=canonicalFaceB D (C.faceEquiv A) (C.slotPerm A s) := by
  unfold faceB pullback canonicalFaceB
  dsimp only
  rw [flag_pullback C D]

theorem sum_labelMap_pullback (p : Equiv.Perm (Fin 11)) (f : Fin 11 → ℚ)
    (e : Finset (Fin 11)) :
    (∑ i ∈ labelMap p e, f (p.symm i))=∑ i ∈ e, f i := by
  unfold labelMap
  rw [Finset.sum_image (fun i _ j _ hij => p.injective hij)]
  simp only [Equiv.symm_apply_apply]

theorem switchP_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (i : Fin 9) :
    switchP (pullback C D) (pullbackKap cut b kap) i=canonicalSwitchP D kap (i-cut) := by
  unfold switchP pullback pullbackKap canonicalSwitchP
  dsimp only
  rw [inverse_cycleEdge]
  have hh := cycleEdge_transport cut b (i-cut)
  rw [sub_add_cancel] at hh
  rw [← hh,sum_labelMap_pullback]

theorem switchQ_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) (i : Fin 9) :
    switchQ (pullback C D) i=canonicalSwitchQ D (i-cut) := by
  unfold switchQ pullback canonicalSwitchQ
  dsimp only
  rw [inverse_cycleEdge]

theorem switchB_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) (i : Fin 9) :
    switchB (pullback C D) i=canonicalSwitchB D (i-cut) := by
  unfold switchB pullback canonicalSwitchB
  dsimp only
  rw [inverse_cycleEdge]

theorem switchD2_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) (i : Fin 9) :
    switchD2 (pullback C D) i=canonicalSwitchD2 D (i-cut) := by
  unfold switchD2 pullback canonicalSwitchD2
  dsimp only
  rw [show (i-1)-cut=(i-cut)-1 by abel]

theorem switchD1_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) (i : Fin 9) :
    switchD1 (pullback C D) i=canonicalSwitchD1 D (i-cut) := by
  unfold switchD1 pullback canonicalSwitchD1
  dsimp only
  rw [show (i-1)-cut=(i-cut)-1 by abel]

theorem outsideGaps_transport (cut ear i : Fin 9) :
    i ∈ outsideGaps ear ↔ i-cut ∈ outsideGaps (ear-cut) := by
  have hh (n : Fin 9) : i-cut=(ear-cut)-n ↔ i=ear-n := by
    rw [show (ear-cut)-n=(ear-n)-cut by abel]
    exact sub_left_inj
  simp only [outsideGaps,earGaps,Finset.mem_sdiff,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton,hh,sub_left_inj]

def canonicalSectorC {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (ear : Fin 9) (eta : ℚ) (i : Fin 9) : ℚ :=
  D.width+if i ∈ outsideGaps ear then eta else 0

theorem sectorC_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (ear : Fin 9) (eta : ℚ) (i : Fin 9) :
    sectorC (pullback C D) ear eta i=canonicalSectorC D (ear-cut) eta (i-cut) := by
  unfold sectorC pullback canonicalSectorC
  simp only [outsideGaps_transport cut ear i]

theorem sectorOwner_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) (i : Fin 9) :
    (pullback C D).mu (nextSite i)=D.mu (nextSite (i-cut)) := by
  have hh := canonicalPerm_nextSite cut b (i-cut)
  rw [sub_add_cancel] at hh
  change D.mu ((canonicalPerm cut b).symm (nextSite i))=D.mu (nextSite (i-cut))
  rw [← hh,Equiv.symm_apply_apply]

theorem faceSum_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {p : Equiv.Perm (Fin 11)}
    (C : Coordinates R F p) (m : F → ℚ) :
    (∑ A : R.Index, m (C.faceEquiv A))=∑ f : F, m f := Equiv.sum_comp C.faceEquiv m

theorem cyclicSum_pullback (cut : Fin 9) (m : Fin 9 → ℚ) :
    (∑ i : Fin 9, m (i-cut))=∑ i : Fin 9, m i := by
  have hh := Equiv.sum_comp (Equiv.addRight cut) (fun i => m (i-cut))
  simpa only [Equiv.coe_addRight,add_sub_cancel_right] using hh.symm

def canonicalEdgeSumQ {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (e : Finset (Fin 11)) : ℚ :=
  ∑ f : F, ∑ s : Fin 3, if D.flagEdge f s=e then D.faceMask f s else 0

def CanonicalMaskBalancedQ {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F) : Prop :=
  ∀ e ∈ faceEdges F, canonicalEdgeSumQ D e+switchSumQ D.switchMask e=0

theorem edgeSumQ_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) (e : Finset (Fin 11)) :
    edgeSumQ R (pullback C D).faceMask e=
      canonicalEdgeSumQ D (labelMap (canonicalPerm cut b).symm e) := by
  classical
  have hh := Equiv.sum_comp C.flagEquiv (fun z : F × Fin 3 =>
    if D.flagEdge z.1 z.2=labelMap (canonicalPerm cut b).symm e then D.faceMask z.1 z.2 else 0)
  change (∑ z : R.Index × Fin 3,
    if D.flagEdge (C.faceEquiv z.1) (C.slotPerm z.1 z.2)=labelMap (canonicalPerm cut b).symm e
    then D.faceMask (C.faceEquiv z.1) (C.slotPerm z.1 z.2) else 0)=_ at hh
  simp only [Fintype.sum_prod_type] at hh
  unfold edgeSumQ ActualEdgeFlagSums.edgeFlags canonicalEdgeSumQ pullback
  rw [Finset.sum_filter,Fintype.sum_prod_type]
  dsimp only
  convert hh using 1
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro s _
  have hp : ActualEdgeFlagSums.flagEdge R A s=e ↔
      D.flagEdge (C.faceEquiv A) (C.slotPerm A s)=labelMap (canonicalPerm cut b).symm e := by
    rw [← flag_pullback C D]
    exact ((labelMap_injective (canonicalPerm cut b).symm).eq_iff).symm
  simp only [hp]

theorem switchSumQ_pullback (cut : Fin 9) (b : Bool) (g : Fin 9 → ℚ) (e : Finset (Fin 11)) :
    switchSumQ (fun i => g (i-cut)) e=switchSumQ g (labelMap (canonicalPerm cut b).symm e) := by
  have hh := Equiv.sum_comp (Equiv.addRight cut)
    (fun i => if cycleEdge i=e then g (i-cut) else 0)
  simp only [Equiv.coe_addRight,add_sub_cancel_right,← cycleEdge_transport cut b,
    labelMap_eq_iff] at hh
  exact hh.symm

theorem maskBalanced_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (hm : CanonicalMaskBalancedQ D) :
    MaskBalancedQ R (pullback C D).faceMask (pullback C D).switchMask := by
  intro e he
  rw [edgeSumQ_pullback]
  change canonicalEdgeSumQ D (labelMap (canonicalPerm cut b).symm e)+
    switchSumQ (fun i => D.switchMask (i-cut)) e=0
  rw [switchSumQ_pullback cut b]
  exact hm _ ((C.edge_mem_iff e).mp he)

def stationWeightQ (i : Fin 11) : ℚ := if i.val < 9 then 1 else 2

def canonicalStationCoeffQ {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F) : ℚ :=
  ∑ i : Fin 11, stationWeightQ i*D.mu i

theorem canonicalPerm_stationWeight : ∀ (cut : Fin 9) (b : Bool) (i : Fin 11),
    stationWeightQ (canonicalPerm cut b i)=stationWeightQ i := by decide +kernel

theorem stationCoeffQ_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F) :
    stationCoeffQ (pullback C D)=canonicalStationCoeffQ D := by
  have hh := Equiv.sum_comp (canonicalPerm cut b)
    (fun i => stationWeightQ i*D.mu ((canonicalPerm cut b).symm i))
  simp only [canonicalPerm_stationWeight,Equiv.symm_apply_apply] at hh
  exact hh.symm

theorem edgeMultiplierSum_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (kap : Finset (Fin 11) → ℚ) :
    (∑ e ∈ edges R, pullbackKap cut b kap e)=∑ e ∈ faceEdges F, kap e := by
  rw [C.edges_image,Finset.sum_image (fun e _ f _ hef => labelMap_injective _ hef)]
  simp only [pullbackKap,labelMap_symm_apply]

def canonicalConstantCoeffQ {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (eta : ℚ) : ℚ :=
  canonicalStationCoeffQ D+(∑ e ∈ faceEdges F, kap e)-2*D.width-2*eta

def canonicalConstantUpperQ {F : Finset (Finset (Fin 11))} (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (eta : ℚ) : ℚ :=
  piProductUpper (canonicalConstantCoeffQ D kap eta)+2*(108/125)*eta

theorem constantCoeffQ_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (eta : ℚ) :
    constantCoeffQ (pullback C D) (pullbackKap cut b kap) eta=canonicalConstantCoeffQ D kap eta := by
  unfold constantCoeffQ canonicalConstantCoeffQ
  rw [stationCoeffQ_pullback,edgeMultiplierSum_pullback C]
  rfl

theorem constantUpperQ_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (eta : ℚ) :
    constantUpperQ (pullback C D) (pullbackKap cut b kap) eta=canonicalConstantUpperQ D kap eta := by
  unfold constantUpperQ canonicalConstantUpperQ
  rw [constantCoeffQ_pullback]

theorem nonnegative_edge_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (kap : Finset (Fin 11) → ℚ)
    (hkap : ∀ e ∈ faceEdges F, 0 ≤ kap e) : ∀ e ∈ edges R, 0 ≤ pullbackKap cut b kap e :=
  fun e he => hkap _ ((C.edge_mem_iff e).mp he)

end N11Formalization.ActualCanonicalMomentTransport
#check @N11Formalization.ActualCanonicalMomentTransport.pullback
#check @N11Formalization.ActualCanonicalMomentTransport.maskBalanced_pullback
#check @N11Formalization.ActualCanonicalMomentTransport.constantUpperQ_pullback
#check @N11Formalization.ActualCanonicalMomentTransport.constantCoeffQ_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.faceP_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.edgeEquiv
#print axioms N11Formalization.ActualCanonicalMomentTransport.faceQ_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.faceB_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.switchP_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.switchQ_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.switchB_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.switchD2_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.switchD1_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.sectorC_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.sectorOwner_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.edgeSumQ_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.switchSumQ_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.maskBalanced_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.stationCoeffQ_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.edgeMultiplierSum_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.constantUpperQ_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.constantCoeffQ_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.nonnegative_edge_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.q0FaceCard
#print axioms N11Formalization.ActualCanonicalMomentTransport.q1FaceCard
