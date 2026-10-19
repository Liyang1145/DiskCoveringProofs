import N11Formalization.SharedMomentFacePlaneGradientCertificate

/-! Exact numerical proposal data and two-coordinate closed splitting tools.
Data alone provides no covering-class or factor-bound assertion. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentConcreteFace1
open RationalBoxSubdivision SharedMomentFacePlaneGradientCertificate

def planeBox (aLo aHi bLo bHi : ℚ) : Cell (Fin 2) := ![⟨aLo,aHi⟩,⟨bLo,bHi⟩]

theorem planeBox_split_zero {leaf : Cell (Fin 2) → Prop}
    (aLo cut aHi bLo bHi : ℚ) (hlo : aLo ≤ cut) (hhi : cut ≤ aHi)
    (left : Certificate leaf (planeBox aLo cut bLo bHi))
    (right : Certificate leaf (planeBox cut aHi bLo bHi)) :
    Certificate leaf (planeBox aLo aHi bLo bHi) := by
  have hl : leftChild (planeBox aLo aHi bLo bHi) 0 cut = planeBox aLo cut bLo bHi := by
    funext i
    fin_cases i <;> simp [leftChild,planeBox]
  have hr : rightChild (planeBox aLo aHi bLo bHi) 0 cut = planeBox cut aHi bLo bHi := by
    funext i
    fin_cases i <;> simp [rightChild,planeBox]
  apply Certificate.split 0 cut hlo hhi
  · rw [hl]
    exact left
  · rw [hr]
    exact right

theorem planeBox_split_one {leaf : Cell (Fin 2) → Prop}
    (aLo aHi bLo cut bHi : ℚ) (hlo : bLo ≤ cut) (hhi : cut ≤ bHi)
    (left : Certificate leaf (planeBox aLo aHi bLo cut))
    (right : Certificate leaf (planeBox aLo aHi cut bHi)) :
    Certificate leaf (planeBox aLo aHi bLo bHi) := by
  have hl : leftChild (planeBox aLo aHi bLo bHi) 1 cut = planeBox aLo aHi bLo cut := by
    funext i
    fin_cases i <;> simp [leftChild,planeBox]
  have hr : rightChild (planeBox aLo aHi bLo bHi) 1 cut = planeBox aLo aHi cut bHi := by
    funext i
    fin_cases i <;> simp [rightChild,planeBox]
  apply Certificate.split 1 cut hlo hhi
  · rw [hl]
    exact left
  · rw [hr]
    exact right

def start0_face1_p : Fin 3 → ℚ := ![(14313377/250000000 : ℚ),(-30939859/1000000000 : ℚ),(-7389693/1000000000 : ℚ)]
def start0_face1_q : Fin 3 → ℚ := ![(98958367/250000000 : ℚ),(74532777/1000000000 : ℚ),(251843483/1000000000 : ℚ)]
def start0_face1_b : Fin 3 → ℚ := ![(-541272263/1000000000 : ℚ),(17146697/200000000 : ℚ),(-102151007/500000000 : ℚ)]
def start0_face1_bound : ℚ := (18011/100000 : ℚ)
def start0_face1_leaf (B : Cell (Fin 2)) : Prop :=
  GradientPlaneLeaf start0_face1_p start0_face1_q start0_face1_b start0_face1_bound B
#print axioms planeBox_split_zero
#print axioms planeBox_split_one
end N11Formalization.SharedMomentConcreteFace1
