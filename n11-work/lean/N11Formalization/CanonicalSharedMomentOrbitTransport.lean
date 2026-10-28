import N11Formalization.ActualCanonicalSharedMomentConsumer
import N11Formalization.CanonicalBalancedGraphOrbits

/-! Balanced canonical certificates are transported by finite face and
slot permutations. Reflection reindexes switches and sectors and exchanges
the two endpoint copies. No symmetry of a real configuration is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.CanonicalSharedMomentOrbitTransport

open ActualCanonicalFaceCoordinates ActualCanonicalMomentTransport
open ActualCanonicalSharedMomentConsumer CanonicalBalancedGraphOrbits
open ActualOrderedMetricGraphs ActualCanonicalSitePermutation ActualEdgeFlagSums
open ActualRingLinkBoundaryData ActualEarOwnedWidth SharedMomentFactorPermutation
open SharedMomentFactorGridCertificate ActualSharedMomentRationalCertificate
open MetricAreaRationalCertificate

def targetFaces (k : Fin 8) : Finset (Finset (Fin 11)) := q1Faces k 4
def representativeFaces (k : Fin 8) : Finset (Finset (Fin 11)) := q1Faces (representative k) 4

theorem targetFaces_eq (k : Fin 8) : targetFaces k=q1Faces k 4 := rfl
theorem representativeFaces_eq (k : Fin 8) : representativeFaces k=q1Faces (representative k) 4 := rfl

theorem targetFaceCard (k : Fin 8) (f : targetFaces k) : f.val.card=3 := q1FaceCard k 4 f
theorem representativeFaceCard (k : Fin 8) (f : representativeFaces k) : f.val.card=3 := q1FaceCard (representative k) 4 f

theorem orbit_faces (k : Fin 8) : (representativeFaces k).image (labelMap (orbitPerm k))=targetFaces k :=
  balanced_orbit k

theorem orbit_edges (k : Fin 8) : (faceEdges (representativeFaces k)).image (labelMap (orbitPerm k))=
    faceEdges (targetFaces k) := balanced_orbit_edges k

attribute [irreducible] targetFaces representativeFaces

def switchIndex (k : Fin 8) (i : Fin 9) : Fin 9 := if usesReflection k then -i-1 else i
def sectorIndex (k : Fin 8) (i : Fin 9) : Fin 9 := if usesReflection k then -i-2 else i

theorem switchIndex_involutive : ∀ k : Fin 8, ∀ i : Fin 9,
    switchIndex k (switchIndex k i)=i := by decide +kernel

theorem sectorIndex_involutive : ∀ k : Fin 8, ∀ i : Fin 9,
    sectorIndex k (sectorIndex k i)=i := by decide +kernel

def switchEquiv (k : Fin 8) : Equiv.Perm (Fin 9) where
  toFun := switchIndex k
  invFun := switchIndex k
  left_inv := switchIndex_involutive k
  right_inv := switchIndex_involutive k

def sectorEquiv (k : Fin 8) : Equiv.Perm (Fin 9) where
  toFun := sectorIndex k
  invFun := sectorIndex k
  left_inv := sectorIndex_involutive k
  right_inv := sectorIndex_involutive k

theorem orbit_cycle : ∀ k : Fin 8, ∀ i : Fin 9,
    labelMap (orbitPerm k) (cycleEdge i)=cycleEdge (switchIndex k i) := by decide +kernel

theorem inverse_orbit_cycle : ∀ k : Fin 8, ∀ i : Fin 9,
    labelMap (orbitPerm k).symm (cycleEdge i)=cycleEdge (switchIndex k i) := by decide +kernel

theorem inverse_orbit_owner : ∀ k : Fin 8, ∀ i : Fin 9,
    (orbitPerm k).symm (nextSite i)=nextSite (sectorIndex k i) := by decide +kernel

theorem orbit_outside : ∀ k : Fin 8, ∀ i : Fin 9,
    i ∈ outsideGaps 0 ↔ sectorIndex k i ∈ outsideGaps 0 := by decide +kernel

def faceEquiv (k : Fin 8) : (targetFaces k) ≃ (representativeFaces k) where
  toFun f := ⟨labelMap (orbitPerm k).symm f.val,by
    have hm : f.val ∈ (representativeFaces k).image (labelMap (orbitPerm k)) := by
      simpa only [orbit_faces k] using f.property
    obtain ⟨g,hg,he⟩ := Finset.mem_image.mp hm
    rw [← he,labelMap_symm_apply]
    exact hg⟩
  invFun f := ⟨labelMap (orbitPerm k) f.val,by
    rw [← orbit_faces k]
    exact Finset.mem_image.mpr ⟨f.val,f.property,rfl⟩⟩
  left_inv f := Subtype.ext (labelMap_apply_symm _ _)
  right_inv f := Subtype.ext (labelMap_symm_apply _ _)

theorem faceEquiv_val (k : Fin 8) (f : targetFaces k) :
    (faceEquiv k f).val=labelMap (orbitPerm k).symm f.val := rfl

theorem face_eq (k : Fin 8) (f : targetFaces k) :
    f.val=labelMap (orbitPerm k) (faceEquiv k f).val := (labelMap_apply_symm _ _).symm

private def faceLabelEquiv (k : Fin 8) (f : targetFaces k) : f.val ≃ (faceEquiv k f).val where
  toFun i := ⟨(orbitPerm k).symm i.val,by
    apply (mem_labelMap (orbitPerm k)).mp
    rw [← face_eq k f]
    exact i.property⟩
  invFun i := ⟨orbitPerm k i.val,by
    rw [face_eq k f]
    exact Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
  left_inv i := Subtype.ext ((orbitPerm k).apply_symm_apply _)
  right_inv i := Subtype.ext ((orbitPerm k).symm_apply_apply _)

def slotPerm (k : Fin 8) (f : targetFaces k) : Equiv.Perm (Fin 3) :=
  ((f.val.orderIsoOfFin (targetFaceCard k f)).toEquiv.trans (faceLabelEquiv k f)).trans
    ((faceEquiv k f).val.orderIsoOfFin (representativeFaceCard k (faceEquiv k f))).toEquiv.symm

theorem slot_label (k : Fin 8) (f : targetFaces k) (s : Fin 3) :
    canonicalLabel (faceEquiv k f).val (representativeFaceCard k (faceEquiv k f))
      (slotPerm k f s)=(orbitPerm k).symm (canonicalLabel f.val (targetFaceCard k f) s) := by
  exact congrArg Subtype.val
    (((faceEquiv k f).val.orderIsoOfFin (representativeFaceCard k (faceEquiv k f))).apply_symm_apply _)

def flagEquiv (k : Fin 8) : ((targetFaces k) × Fin 3) ≃ ((representativeFaces k) × Fin 3) where
  toFun z := (faceEquiv k z.1,slotPerm k z.1 z.2)
  invFun z := ((faceEquiv k).symm z.1,(slotPerm k ((faceEquiv k).symm z.1)).symm z.2)
  left_inv z := by rcases z with ⟨f,s⟩; simp
  right_inv z := by rcases z with ⟨f,s⟩; simp

attribute [irreducible] faceEquiv slotPerm

def orbitKap (k : Fin 8) (kap : Finset (Fin 11) → ℚ) (e : Finset (Fin 11)) : ℚ :=
  kap (labelMap (orbitPerm k).symm e)

def orbitCoeffQ (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) :
    CanonicalCoeffQ (targetFaces k) where
  faceCard := targetFaceCard k
  mu := fun i => D.mu ((orbitPerm k).symm i)
  faceMask := fun f s => D.faceMask (faceEquiv k f) (slotPerm k f s)
  switchMask := fun i => D.switchMask (switchIndex k i)
  sideFirst := fun e => D.sideFirst (labelMap (orbitPerm k).symm e)
  sideSecond := fun e => D.sideSecond (labelMap (orbitPerm k).symm e)
  leftFirst := fun i => if usesReflection k then D.rightFirst (sectorIndex k i) else D.leftFirst i
  leftSecond := fun i => if usesReflection k then D.rightSecond (sectorIndex k i) else D.leftSecond i
  rightFirst := fun i => if usesReflection k then D.leftFirst (sectorIndex k i) else D.rightFirst i
  rightSecond := fun i => if usesReflection k then D.leftSecond (sectorIndex k i) else D.rightSecond i
  width := D.width

theorem orbit_mu (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 11) :
    (orbitCoeffQ k D).mu i=D.mu ((orbitPerm k).symm i) := rfl

theorem orbit_mask (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (f : targetFaces k) (s : Fin 3) :
    (orbitCoeffQ k D).faceMask f s=D.faceMask (faceEquiv k f) (slotPerm k f s) := rfl

theorem orbit_switchMask (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 9) :
    (orbitCoeffQ k D).switchMask i=D.switchMask (switchIndex k i) := rfl

theorem orbit_sideFirst (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (e : Finset (Fin 11)) :
    (orbitCoeffQ k D).sideFirst e=D.sideFirst (labelMap (orbitPerm k).symm e) := rfl

theorem orbit_sideSecond (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (e : Finset (Fin 11)) :
    (orbitCoeffQ k D).sideSecond e=D.sideSecond (labelMap (orbitPerm k).symm e) := rfl

theorem orbit_leftFirst (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 9) :
    (orbitCoeffQ k D).leftFirst i=(if usesReflection k then D.rightFirst (sectorIndex k i) else D.leftFirst i) := rfl

theorem orbit_leftSecond (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 9) :
    (orbitCoeffQ k D).leftSecond i=(if usesReflection k then D.rightSecond (sectorIndex k i) else D.leftSecond i) := rfl

theorem orbit_rightFirst (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 9) :
    (orbitCoeffQ k D).rightFirst i=(if usesReflection k then D.leftFirst (sectorIndex k i) else D.rightFirst i) := rfl

theorem orbit_rightSecond (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 9) :
    (orbitCoeffQ k D).rightSecond i=(if usesReflection k then D.leftSecond (sectorIndex k i) else D.rightSecond i) := rfl

theorem orbit_width (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) :
    @CanonicalCoeffQ.width (targetFaces k) (orbitCoeffQ k D)=
      @CanonicalCoeffQ.width (representativeFaces k) D := rfl

theorem label_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (f : targetFaces k) (s : Fin 3) :
    (orbitPerm k).symm ((orbitCoeffQ k D).label f s)=D.label (faceEquiv k f) (slotPerm k f s) :=
  (slot_label k f s).symm

theorem flag_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (f : targetFaces k) (s : Fin 3) :
    labelMap (orbitPerm k).symm ((orbitCoeffQ k D).flagEdge f s)=
      D.flagEdge (faceEquiv k f) (slotPerm k f s) := by
  unfold CanonicalCoeffQ.flagEdge
  rw [face_eq k f]
  have hl : (orbitCoeffQ k D).label f s=
      orbitPerm k (D.label (faceEquiv k f) (slotPerm k f s)) := by
    rw [← label_transport k D,Equiv.apply_symm_apply]
  rw [hl]
  have he : (labelMap (orbitPerm k) (faceEquiv k f).val).erase
      (orbitPerm k (D.label (faceEquiv k f) (slotPerm k f s)))=
      labelMap (orbitPerm k) ((faceEquiv k f).val.erase (D.label (faceEquiv k f) (slotPerm k f s))) :=
    (Finset.image_erase (orbitPerm k).injective _ _).symm
  rw [he,labelMap_symm_apply]

attribute [irreducible] orbitCoeffQ

theorem faceP_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (kap : Finset (Fin 11) → ℚ) (f : targetFaces k) (s : Fin 3) :
    canonicalFaceP (orbitCoeffQ k D) (orbitKap k kap) f s=
      canonicalFaceP D kap (faceEquiv k f) (slotPerm k f s) := by
  simp only [canonicalFaceP,orbit_mu,orbitKap]
  rw [label_transport,flag_transport]

theorem faceQ_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (f : targetFaces k) (s : Fin 3) :
    canonicalFaceQ (orbitCoeffQ k D) f s=canonicalFaceQ D (faceEquiv k f) (slotPerm k f s) := by
  simp only [canonicalFaceQ,orbit_mask,orbit_sideSecond]
  rw [flag_transport]

theorem faceB_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (f : targetFaces k) (s : Fin 3) :
    canonicalFaceB (orbitCoeffQ k D) f s=canonicalFaceB D (faceEquiv k f) (slotPerm k f s) := by
  simp only [canonicalFaceB,orbit_mask,orbit_sideFirst]
  rw [flag_transport]

theorem switchP_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (kap : Finset (Fin 11) → ℚ) (i : Fin 9) :
    canonicalSwitchP (orbitCoeffQ k D) (orbitKap k kap) i=canonicalSwitchP D kap (switchIndex k i) := by
  simp only [canonicalSwitchP,orbit_mu,orbitKap]
  rw [inverse_orbit_cycle]
  have hh := orbit_cycle k (switchIndex k i)
  rw [switchIndex_involutive] at hh
  rw [← hh,sum_labelMap_pullback]

theorem switchQ_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 9) :
    canonicalSwitchQ (orbitCoeffQ k D) i=canonicalSwitchQ D (switchIndex k i) := by
  simp only [canonicalSwitchQ,orbit_switchMask,orbit_sideSecond]
  rw [inverse_orbit_cycle]

theorem switchB_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 9) :
    canonicalSwitchB (orbitCoeffQ k D) i=canonicalSwitchB D (switchIndex k i) := by
  simp only [canonicalSwitchB,orbit_switchMask,orbit_sideFirst]
  rw [inverse_orbit_cycle]

theorem switchD2_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 9) :
    canonicalSwitchD2 (orbitCoeffQ k D) i=canonicalSwitchD2 D (switchIndex k i) := by
  by_cases hr : usesReflection k=true
  · simp only [canonicalSwitchD2,orbit_leftSecond,orbit_rightSecond,sectorIndex,switchIndex,hr,if_true]
    rw [show -(i-1)-2=-i-1 by abel,show (-i-1)-1=-i-2 by abel]
    ring
  · simp [canonicalSwitchD2,orbit_leftSecond,orbit_rightSecond,switchIndex,hr]

theorem switchD1_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 9) :
    canonicalSwitchD1 (orbitCoeffQ k D) i=canonicalSwitchD1 D (switchIndex k i) := by
  by_cases hr : usesReflection k=true
  · simp only [canonicalSwitchD1,orbit_leftFirst,orbit_rightFirst,sectorIndex,switchIndex,hr,if_true]
    rw [show -(i-1)-2=-i-1 by abel,show (-i-1)-1=-i-2 by abel]
    ring
  · simp [canonicalSwitchD1,orbit_leftFirst,orbit_rightFirst,switchIndex,hr]

theorem sectorC_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (eta : ℚ) (i : Fin 9) :
    canonicalSectorC (orbitCoeffQ k D) 0 eta i=canonicalSectorC D 0 eta (sectorIndex k i) := by
  simp only [canonicalSectorC,orbit_width,orbit_outside k i]

theorem sectorOwner_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) (i : Fin 9) :
    (orbitCoeffQ k D).mu (nextSite i)=D.mu (nextSite (sectorIndex k i)) := by
  simp only [orbit_mu,inverse_orbit_owner]

theorem edge_mem_iff (k : Fin 8) (e : Finset (Fin 11)) :
    e ∈ faceEdges (targetFaces k) ↔ labelMap (orbitPerm k).symm e ∈ faceEdges (representativeFaces k) := by
  rw [← orbit_edges k]
  constructor
  · intro he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp he
    rw [← hfe,labelMap_symm_apply]
    exact hf
  · intro he
    exact Finset.mem_image.mpr ⟨labelMap (orbitPerm k).symm e,he,labelMap_apply_symm (orbitPerm k) e⟩

theorem edgeSum_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (e : Finset (Fin 11)) :
    canonicalEdgeSumQ (orbitCoeffQ k D) e=canonicalEdgeSumQ D (labelMap (orbitPerm k).symm e) := by
  classical
  have hh := Equiv.sum_comp (flagEquiv k) (fun z : (representativeFaces k) × Fin 3 =>
    if D.flagEdge z.1 z.2=labelMap (orbitPerm k).symm e then D.faceMask z.1 z.2 else 0)
  change (∑ z : (targetFaces k) × Fin 3,
    if D.flagEdge (faceEquiv k z.1) (slotPerm k z.1 z.2)=labelMap (orbitPerm k).symm e
    then D.faceMask (faceEquiv k z.1) (slotPerm k z.1 z.2) else 0)=_ at hh
  simp only [Fintype.sum_prod_type] at hh
  unfold canonicalEdgeSumQ
  convert hh using 1
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro s _
  have hp : (orbitCoeffQ k D).flagEdge f s=e ↔
      D.flagEdge (faceEquiv k f) (slotPerm k f s)=labelMap (orbitPerm k).symm e := by
    rw [← flag_transport k D]
    exact ((labelMap_injective (orbitPerm k).symm).eq_iff).symm
  simp only [hp,orbit_mask]

theorem switchSum_transport (k : Fin 8) (g : Fin 9 → ℚ) (e : Finset (Fin 11)) :
    switchSumQ (fun i => g (switchIndex k i)) e=switchSumQ g (labelMap (orbitPerm k).symm e) := by
  have hh := Equiv.sum_comp (switchEquiv k) (fun i => if cycleEdge i=e then g (switchIndex k i) else 0)
  change (∑ i : Fin 9, if cycleEdge (switchIndex k i)=e then g (switchIndex k (switchIndex k i)) else 0)=_ at hh
  simp only [switchIndex_involutive] at hh
  have hp (i : Fin 9) : cycleEdge (switchIndex k i)=e ↔ cycleEdge i=labelMap (orbitPerm k).symm e := by
    rw [← orbit_cycle k i,labelMap_eq_iff]
  simpa only [hp,switchSumQ] using hh.symm

theorem maskBalanced_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (H : CanonicalMaskBalancedQ D) : CanonicalMaskBalancedQ (orbitCoeffQ k D) := by
  intro e he
  rw [edgeSum_transport]
  simp only [switchSumQ,orbit_switchMask]
  change canonicalEdgeSumQ D (labelMap (orbitPerm k).symm e)+switchSumQ (fun i => D.switchMask (switchIndex k i)) e=0
  rw [switchSum_transport]
  exact H _ ((edge_mem_iff k e).mp he)

theorem orbit_stationWeight : ∀ k : Fin 8, ∀ i : Fin 11,
    stationWeightQ (orbitPerm k i)=stationWeightQ i := by decide +kernel

theorem stationCoeff_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k)) :
    canonicalStationCoeffQ (orbitCoeffQ k D)=canonicalStationCoeffQ D := by
  have hh := Equiv.sum_comp (orbitPerm k) (fun i => stationWeightQ i*D.mu ((orbitPerm k).symm i))
  simp only [orbit_stationWeight,Equiv.symm_apply_apply] at hh
  simpa only [canonicalStationCoeffQ,orbit_mu] using hh.symm

theorem edgeMultiplierSum_transport (k : Fin 8) (kap : Finset (Fin 11) → ℚ) :
    (∑ e ∈ faceEdges (targetFaces k), orbitKap k kap e)=∑ e ∈ faceEdges (representativeFaces k), kap e := by
  rw [← orbit_edges k,Finset.sum_image (fun e _ f _ hef => labelMap_injective _ hef)]
  simp only [orbitKap,labelMap_symm_apply]

theorem constantCoeff_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (kap : Finset (Fin 11) → ℚ) (eta : ℚ) :
    canonicalConstantCoeffQ (orbitCoeffQ k D) (orbitKap k kap) eta=canonicalConstantCoeffQ D kap eta := by
  unfold canonicalConstantCoeffQ
  rw [stationCoeff_transport,edgeMultiplierSum_transport]
  rw [orbit_width]

theorem sharpConstant_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ) :
    canonicalSharpConstantUpperQ (orbitCoeffQ k D) (orbitKap k kap) eta alpha=
      canonicalSharpConstantUpperQ D kap eta alpha := by
  unfold canonicalSharpConstantUpperQ
  rw [constantCoeff_transport]

theorem total_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ)
    (faceMax : (representativeFaces k) → ℚ) (switchMax sectorMax : Fin 9 → ℚ) :
    canonicalTotalUpperQ (orbitCoeffQ k D) (orbitKap k kap) eta alpha
      (fun f => faceMax (faceEquiv k f)) (fun i => switchMax (switchIndex k i))
      (fun i => sectorMax (sectorIndex k i))=canonicalTotalUpperQ D kap eta alpha faceMax switchMax sectorMax := by
  unfold canonicalTotalUpperQ
  rw [sharpConstant_transport,Equiv.sum_comp (faceEquiv k) faceMax]
  have hs := Equiv.sum_comp (switchEquiv k) switchMax
  have ht := Equiv.sum_comp (sectorEquiv k) sectorMax
  change (∑ i : Fin 9, switchMax (switchIndex k i))=∑ i : Fin 9, switchMax i at hs
  change (∑ i : Fin 9, sectorMax (sectorIndex k i))=∑ i : Fin 9, sectorMax i at ht
  rw [hs,ht]

theorem factorBounds_transport (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (kap : Finset (Fin 11) → ℚ) (eta : ℚ)
    (faceMax : (representativeFaces k) → ℚ) (switchMax sectorMax : Fin 9 → ℚ)
    (H : CanonicalFactorBounds D kap 0 eta faceMax switchMax sectorMax) :
    CanonicalFactorBounds (orbitCoeffQ k D) (orbitKap k kap) 0 eta
      (fun f => faceMax (faceEquiv k f)) (fun i => switchMax (switchIndex k i))
      (fun i => sectorMax (sectorIndex k i)) := by
  constructor
  · intro f a ha hsum y hy
    simp only [faceP_transport,faceQ_transport,faceB_transport]
    exact face_upper_of_permuted_coefficients _ _ _ _ (slotPerm k f) (H.face (faceEquiv k f)) a ha hsum y hy
  · intro i t ht y hy
    rw [switchP_transport,switchQ_transport,switchB_transport,switchD2_transport,switchD1_transport]
    exact H.switch (switchIndex k i) t ht y hy
  · intro i a ha u hu v hv
    rw [sectorC_transport,sectorOwner_transport]
    by_cases hr : usesReflection k=true
    · simp only [orbit_leftSecond,orbit_rightSecond,orbit_leftFirst,orbit_rightFirst,hr,if_true]
      rw [sector_objective_swap]
      exact H.sector (sectorIndex k i) a ha v hv u hu
    · simp [orbit_leftSecond,orbit_rightSecond,orbit_leftFirst,orbit_rightFirst,sectorIndex,hr]
      exact H.sector i a ha u hu v hv

def orbitCertificate (k : Fin 8) (D : CanonicalCoeffQ (representativeFaces k))
    (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ) (K : CanonicalCertificate D kap 0 eta alpha) :
    CanonicalCertificate (orbitCoeffQ k D) (orbitKap k kap) 0 eta alpha where
  faceMax := fun f => K.faceMax (faceEquiv k f)
  switchMax := fun i => K.switchMax (switchIndex k i)
  sectorMax := fun i => K.sectorMax (sectorIndex k i)
  balance := maskBalanced_transport k D K.balance
  edge_nonnegative := fun e he => K.edge_nonnegative _ ((edge_mem_iff k e).mp he)
  eta_nonnegative := K.eta_nonnegative
  bracket := K.bracket
  bounds := factorBounds_transport k D kap eta K.faceMax K.switchMax K.sectorMax K.bounds
  strict := by rw [total_transport]; exact K.strict

private structure CertificateTable (F : Finset (Finset (Fin 11))) (alpha : ℚ) : Prop where
  witnessed : ∃ D : CanonicalCoeffQ F, ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
    Nonempty (CanonicalCertificate D kap 0 eta alpha)

private theorem transportCertificateTable {F G : Finset (Finset (Fin 11))}
    (h : F=G) (alpha : ℚ) : CertificateTable F alpha → CertificateTable G alpha := by
  cases h
  exact fun K => K

theorem balanced_certificates_of_two (alpha : ℚ)
    (H7 : ∃ D : CanonicalCoeffQ (q1Faces 7 4), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
      Nonempty (CanonicalCertificate D kap 0 eta alpha))
    (H1 : ∃ D : CanonicalCoeffQ (q1Faces 1 4), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
      Nonempty (CanonicalCertificate D kap 0 eta alpha)) :
    ∀ k : Fin 8, ∃ D : CanonicalCoeffQ (q1Faces k 4), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
      Nonempty (CanonicalCertificate D kap 0 eta alpha) := by
  intro k
  have hh : CertificateTable (representativeFaces k) alpha := by
    rcases representative_two k with hk | hk
    · have he : representativeFaces k=q1Faces 7 4 :=
        (representativeFaces_eq k).trans (congrArg (fun j : Fin 8 => q1Faces j 4) hk)
      exact transportCertificateTable he.symm alpha ⟨H7⟩
    · have he : representativeFaces k=q1Faces 1 4 :=
        (representativeFaces_eq k).trans (congrArg (fun j : Fin 8 => q1Faces j 4) hk)
      exact transportCertificateTable he.symm alpha ⟨H1⟩
  obtain ⟨D,kap,eta,⟨K⟩⟩ := hh.witnessed
  have ht : CertificateTable (targetFaces k) alpha :=
    ⟨⟨orbitCoeffQ k D,orbitKap k kap,eta,⟨orbitCertificate k D kap eta alpha K⟩⟩⟩
  exact (transportCertificateTable (targetFaces_eq k) alpha ht).witnessed

end N11Formalization.CanonicalSharedMomentOrbitTransport
#check @N11Formalization.CanonicalSharedMomentOrbitTransport.orbitCertificate
#check @N11Formalization.CanonicalSharedMomentOrbitTransport.balanced_certificates_of_two
#print axioms N11Formalization.CanonicalSharedMomentOrbitTransport.faceEquiv
#print axioms N11Formalization.CanonicalSharedMomentOrbitTransport.slotPerm
#print axioms N11Formalization.CanonicalSharedMomentOrbitTransport.flag_transport
#print axioms N11Formalization.CanonicalSharedMomentOrbitTransport.switchD2_transport
#print axioms N11Formalization.CanonicalSharedMomentOrbitTransport.maskBalanced_transport
#print axioms N11Formalization.CanonicalSharedMomentOrbitTransport.total_transport
#print axioms N11Formalization.CanonicalSharedMomentOrbitTransport.factorBounds_transport
#print axioms N11Formalization.CanonicalSharedMomentOrbitTransport.orbitCertificate
#print axioms N11Formalization.CanonicalSharedMomentOrbitTransport.balanced_certificates_of_two
