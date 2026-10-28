import N11Formalization.ActualOrderedMetricGraphs
import N11Formalization.ActualEdgeFlagSums
import Mathlib.Data.Finset.Sort

/-! Actual face and local-slot coordinates on the proved canonical graphs.
Triangle uniqueness turns the existing whole-label face image into a genuine
bijection. Ascending canonical labels determine each local slot permutation;
face/edge incidence is preserved without an additional matching premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCanonicalFaceCoordinates

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualOrderedMetricGraphs ActualEdgeFlagSums
open ActualCanonicalSitePermutation ActualQ0OrderedTwoFans ActualQ1OrderedCoreFans
open ActualRefinementEarCount
open ActualRefinementDoubleCounting

theorem labelMap_symm_apply (p : Equiv.Perm (Fin 11)) (f : Finset (Fin 11)) :
    labelMap p.symm (labelMap p f)=f := by
  simp [labelMap,Finset.image_image]

theorem labelMap_apply_symm (p : Equiv.Perm (Fin 11)) (f : Finset (Fin 11)) :
    labelMap p (labelMap p.symm f)=f := by
  simp [labelMap,Finset.image_image]

theorem labelMap_injective (p : Equiv.Perm (Fin 11)) : Function.Injective (labelMap p) :=
  Finset.image_injective p.injective

theorem labelMap_eq_iff (p : Equiv.Perm (Fin 11)) (f e : Finset (Fin 11)) :
    labelMap p f=e ↔ f=labelMap p.symm e := by
  constructor
  · intro he
    rw [← he,labelMap_symm_apply]
  · intro he
    rw [he,labelMap_apply_symm]

theorem mem_labelMap (p : Equiv.Perm (Fin 11)) {i : Fin 11} {f : Finset (Fin 11)} :
    i ∈ labelMap p f ↔ p.symm i ∈ f := by
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
    rw [← he,p.symm_apply_apply]
    exact hj
  · intro hi
    exact Finset.mem_image.mpr ⟨p.symm i,hi,p.apply_symm_apply i⟩

def canonicalLabel (f : Finset (Fin 11)) (hcard : f.card=3) (s : Fin 3) : Fin 11 :=
  (f.orderIsoOfFin hcard s).val

theorem canonicalLabel_mem (f : Finset (Fin 11)) (hcard : f.card=3) (s : Fin 3) :
    canonicalLabel f hcard s ∈ f := (f.orderIsoOfFin hcard s).property

theorem canonicalLabel_injective (f : Finset (Fin 11)) (hcard : f.card=3) :
    Function.Injective (canonicalLabel f hcard) := by
  intro s t hst
  exact (f.orderIsoOfFin hcard).injective (Subtype.ext hst)

theorem canonicalLabel_surjective (f : Finset (Fin 11)) (hcard : f.card=3) {i : Fin 11}
    (hi : i ∈ f) : ∃ s : Fin 3, canonicalLabel f hcard s=i := by
  refine ⟨(f.orderIsoOfFin hcard).symm ⟨i,hi⟩,?_⟩
  exact congrArg Subtype.val ((f.orderIsoOfFin hcard).apply_symm_apply ⟨i,hi⟩)

structure Coordinates {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (F : Finset (Finset (Fin 11))) (p : Equiv.Perm (Fin 11)) where
  faces_image : actualFaces R=F.image (labelMap p)
  faceEquiv : R.Index ≃ F
  face_eq : ∀ A, labelSet R A=labelMap p (faceEquiv A).val
  faceCard : ∀ f : F, f.val.card=3
  slotPerm : ∀ A : R.Index, Equiv.Perm (Fin 3)
  slot_label : ∀ A s, R.labels A s=p
    (canonicalLabel (faceEquiv A).val (faceCard (faceEquiv A)) (slotPerm A s))

private def faceMap {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (F : Finset (Finset (Fin 11))) (p : Equiv.Perm (Fin 11))
    (hF : actualFaces R=F.image (labelMap p)) (A : R.Index) : F := by
  refine ⟨labelMap p.symm (labelSet R A),?_⟩
  have hm : labelSet R A ∈ actualFaces R := Finset.mem_image.mpr ⟨A,Finset.mem_univ _,rfl⟩
  rw [hF] at hm
  obtain ⟨f,hf,he⟩ := Finset.mem_image.mp hm
  have hh : labelMap p.symm (labelSet R A)=f := by rw [← he,labelMap_symm_apply]
  exact hh ▸ hf

private theorem faceMap_val {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (F : Finset (Finset (Fin 11))) (p : Equiv.Perm (Fin 11))
    (hF : actualFaces R=F.image (labelMap p)) (A : R.Index) :
    (faceMap R F p hF A).val=labelMap p.symm (labelSet R A) := rfl

private theorem faceMap_bijective {c : Fin 11 → Point} (hc : Function.Injective c) {r : ℝ}
    (R : Refinement c r) (F : Finset (Finset (Fin 11))) (p : Equiv.Perm (Fin 11))
    (hF : actualFaces R=F.image (labelMap p)) : Function.Bijective (faceMap R F p hF) := by
  constructor
  · intro A B he
    apply labelSet_injective hc R
    have hh := congrArg (fun f : F => labelMap p f.val) he
    simpa only [faceMap_val,labelMap_apply_symm] using hh
  · intro f
    have hm : labelMap p f.val ∈ actualFaces R := by
      rw [hF]
      exact Finset.mem_image.mpr ⟨f.val,f.property,rfl⟩
    obtain ⟨A,_,hA⟩ := Finset.mem_image.mp hm
    refine ⟨A,Subtype.ext ?_⟩
    rw [faceMap_val,hA,labelMap_symm_apply]

/-- This constructor consumes the already-proved face image theorem.
The public q0/q1 constructors below produce that theorem from true geometry. -/
def ofFaceImage {c : Fin 11 → Point} (hc : Function.Injective c) {r : ℝ}
    (R : Refinement c r) (F : Finset (Finset (Fin 11))) (p : Equiv.Perm (Fin 11))
    (hF : actualFaces R=F.image (labelMap p)) : Coordinates R F p := by
  classical
  let E : R.Index ≃ F := Equiv.ofBijective (faceMap R F p hF) (faceMap_bijective hc R F p hF)
  have he (A : R.Index) : labelSet R A=labelMap p (E A).val := by
    change labelSet R A=labelMap p (faceMap R F p hF A).val
    rw [faceMap_val,labelMap_apply_symm]
  have hcard (f : F) : f.val.card=3 := by
    have hh := labelSet_card R (E.symm f)
    rw [he,E.apply_symm_apply] at hh
    simpa only [labelMap,Finset.card_image_of_injective f.val p.injective] using hh
  let rank (A : R.Index) (s : Fin 3) : Fin 3 :=
    (((E A).val).orderIsoOfFin (hcard (E A))).symm
      ⟨p.symm (R.labels A s),by
        apply (mem_labelMap p).mp
        rw [← he A]
        exact mem_labelSet.mpr ⟨s,rfl⟩⟩
  have hl (A : R.Index) (s : Fin 3) :
      canonicalLabel (E A).val (hcard (E A)) (rank A s)=p.symm (R.labels A s) := by
    exact congrArg Subtype.val ((((E A).val).orderIsoOfFin (hcard (E A))).apply_symm_apply _)
  have hrank (A : R.Index) : Function.Injective (rank A) := by
    intro s t hst
    apply Refinement.labels_injective R A
    apply p.symm.injective
    rw [← hl A s,← hl A t,hst]
  let S (A : R.Index) : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective (rank A) ⟨hrank A,Finite.surjective_of_injective (hrank A)⟩
  refine ⟨hF,E,he,hcard,S,?_⟩
  intro A s
  change R.labels A s=p (canonicalLabel (E A).val (hcard (E A)) (rank A s))
  rw [hl,p.apply_symm_apply]

namespace Coordinates
variable {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
variable {F : Finset (Finset (Fin 11))} {p : Equiv.Perm (Fin 11)}

def flagEdge (C : Coordinates R F p) (f : F) (s : Fin 3) : Finset (Fin 11) :=
  f.val.erase (canonicalLabel f.val (C.faceCard f) s)

theorem flag_eq (C : Coordinates R F p) (A : R.Index) (s : Fin 3) :
    ActualEdgeFlagSums.flagEdge R A s=labelMap p (C.flagEdge (C.faceEquiv A) (C.slotPerm A s)) := by
  unfold ActualEdgeFlagSums.flagEdge flagEdge
  rw [C.face_eq,C.slot_label]
  exact (Finset.image_erase p.injective _ _).symm

theorem inverse_flag_eq (C : Coordinates R F p) (A : R.Index) (s : Fin 3) :
    labelMap p.symm (ActualEdgeFlagSums.flagEdge R A s)=C.flagEdge (C.faceEquiv A) (C.slotPerm A s) := by
  rw [C.flag_eq,labelMap_symm_apply]

def flagEquiv (C : Coordinates R F p) : (R.Index × Fin 3) ≃ (F × Fin 3) where
  toFun z := (C.faceEquiv z.1,C.slotPerm z.1 z.2)
  invFun z := (C.faceEquiv.symm z.1,(C.slotPerm (C.faceEquiv.symm z.1)).symm z.2)
  left_inv z := by rcases z with ⟨A,s⟩; simp
  right_inv z := by rcases z with ⟨f,s⟩; simp

theorem edges_image (C : Coordinates R F p) : edges R=(faceEdges F).image (labelMap p) := by
  rw [actual_edges_from_faces,C.faces_image,faceEdges_labelMap]

theorem edge_mem_iff (C : Coordinates R F p) (e : Finset (Fin 11)) :
    e ∈ edges R ↔ labelMap p.symm e ∈ faceEdges F := by
  rw [C.edges_image]
  constructor
  · intro he
    obtain ⟨f,hf,he⟩ := Finset.mem_image.mp he
    rw [← he,labelMap_symm_apply]
    exact hf
  · intro he
    exact Finset.mem_image.mpr ⟨labelMap p.symm e,he,labelMap_apply_symm p e⟩

theorem face_edge_incidence (C : Coordinates R F p) (A : R.Index) (e : Finset (Fin 11)) :
    e ⊆ labelSet R A ↔ labelMap p.symm e ⊆ (C.faceEquiv A).val := by
  rw [C.face_eq]
  constructor
  · intro he i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact (mem_labelMap p).mp (he hj)
  · intro he i hi
    apply (mem_labelMap p).mpr
    exact he (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

end Coordinates

def q0Coordinates {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r} (O : OrderedData R) :
    Coordinates R (q0Faces O.run_length) (canonicalPerm O.cut (O.fans.colors O.cut)) :=
  ofFaceImage h.injective R _ _ (q0_faces_transport h hr O)

def q1Coordinates {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r} (O : OrderedCoreData R) :
    Coordinates R (q1Faces O.cut O.run_length)
      (canonicalPerm O.fans.ear.center (O.fans.colors O.cut)) :=
  ofFaceImage h.injective R _ _ (q1_faces_transport h hr O)

theorem actual_q0_coordinates {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=0) :
    ∃ len : Fin 9, 0 < len.val ∧ ∃ k : Fin 9, ∃ b : Bool,
      Nonempty (Coordinates R (q0Faces len) (canonicalPerm k b)) := by
  obtain ⟨O⟩ := actual_q0_ordered_two_fans h hr R hq
  exact ⟨O.run_length,O.positive,O.cut,O.fans.colors O.cut,⟨q0Coordinates h hr O⟩⟩

theorem actual_q1_coordinates {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=1) :
    ∃ len : Fin 8, 0 < len.val ∧ ∃ k : Fin 8, ∃ e : Fin 9, ∃ b : Bool,
      Nonempty (Coordinates R (q1Faces k len) (canonicalPerm e b)) := by
  obtain ⟨O⟩ := actual_q1_ordered_core_fans h hr R hq
  exact ⟨O.run_length,O.positive,O.cut,O.fans.ear.center,O.fans.colors O.cut,⟨q1Coordinates h hr O⟩⟩

end N11Formalization.ActualCanonicalFaceCoordinates
#check @N11Formalization.ActualCanonicalFaceCoordinates.ofFaceImage
#check @N11Formalization.ActualCanonicalFaceCoordinates.actual_q0_coordinates
#check @N11Formalization.ActualCanonicalFaceCoordinates.actual_q1_coordinates
#print axioms N11Formalization.ActualCanonicalFaceCoordinates.ofFaceImage
#print axioms N11Formalization.ActualCanonicalFaceCoordinates.Coordinates.flag_eq
#print axioms N11Formalization.ActualCanonicalFaceCoordinates.Coordinates.flagEquiv
#print axioms N11Formalization.ActualCanonicalFaceCoordinates.Coordinates.edge_mem_iff
#print axioms N11Formalization.ActualCanonicalFaceCoordinates.Coordinates.face_edge_incidence
#print axioms N11Formalization.ActualCanonicalFaceCoordinates.actual_q0_coordinates
#print axioms N11Formalization.ActualCanonicalFaceCoordinates.actual_q1_coordinates
