import N11Formalization.Interval.Core

/-! Finite adaptive subdivisions of rational closed boxes. Every split
retains both copies of its closed boundary. Leaf semantics are proved once;
a certificate supplies only finite rational leaf and cut checks. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.RationalBoxSubdivision

abbrev Cell (I : Type*) := I → RatInterval

def Mem {I : Type*} (B : Cell I) (x : I → ℝ) : Prop := ∀ i, (B i).Mem (x i)
def Valid {I : Type*} (B : Cell I) : Prop := ∀ i, (B i).Valid
def midpoint {I : Type*} (B : Cell I) (i : I) : ℚ := ((B i).lo+(B i).hi)/2
def halfWidth {I : Type*} (B : Cell I) (i : I) : ℚ := ((B i).hi-(B i).lo)/2

theorem midpoint_mem {I : Type*} {B : Cell I} (hB : Valid B) :
    Mem B (fun i => (midpoint B i : ℝ)) := by
  intro i
  have hh := (hB i).lo_le_hi
  unfold midpoint
  push_cast
  constructor <;> linarith only [hh]

theorem halfWidth_nonneg {I : Type*} {B : Cell I} (hB : Valid B) (i : I) :
    0 ≤ halfWidth B i := by
  unfold halfWidth
  exact div_nonneg (sub_nonneg.mpr (hB i)) (by norm_num)

theorem distance_le_halfWidth {I : Type*} {B : Cell I} {x : I → ℝ}
    (hx : Mem B x) (i : I) : |x i-(midpoint B i : ℝ)| ≤ (halfWidth B i : ℝ) := by
  have hh := hx i
  unfold midpoint halfWidth
  push_cast
  exact abs_le.mpr ⟨by linarith only [hh.1],by linarith only [hh.2]⟩

def leftChild {I : Type*} [DecidableEq I] (B : Cell I) (i : I) (t : ℚ) : Cell I :=
  Function.update B i ⟨(B i).lo,t⟩
def rightChild {I : Type*} [DecidableEq I] (B : Cell I) (i : I) (t : ℚ) : Cell I :=
  Function.update B i ⟨t,(B i).hi⟩

theorem split_cover {I : Type*} [DecidableEq I] (B : Cell I) (i : I) (t : ℚ)
    {x : I → ℝ} (hx : Mem B x) :
    Mem (leftChild B i t) x ∨ Mem (rightChild B i t) x := by
  by_cases ht : x i ≤ (t : ℝ)
  · left
    intro j
    by_cases hj : j=i
    · subst j
      simpa only [leftChild,Function.update_self,RatInterval.mem_iff] using ⟨(hx i).1,ht⟩
    · simpa only [leftChild,Function.update_of_ne hj] using hx j
  · right
    intro j
    by_cases hj : j=i
    · subst j
      simpa only [rightChild,Function.update_self,RatInterval.mem_iff] using ⟨(lt_of_not_ge ht).le,(hx i).2⟩
    · simpa only [rightChild,Function.update_of_ne hj] using hx j

theorem leftChild_valid {I : Type*} [DecidableEq I] {B : Cell I} (hB : Valid B)
    (i : I) (t : ℚ) (ht : (B i).lo ≤ t) : Valid (leftChild B i t) := by
  intro j
  by_cases hj : j=i
  · subst j
    simpa only [leftChild,Function.update_self,RatInterval.Valid] using ht
  · simpa only [leftChild,Function.update_of_ne hj] using hB j

theorem rightChild_valid {I : Type*} [DecidableEq I] {B : Cell I} (hB : Valid B)
    (i : I) (t : ℚ) (ht : t ≤ (B i).hi) : Valid (rightChild B i t) := by
  intro j
  by_cases hj : j=i
  · subst j
    simpa only [rightChild,Function.update_self,RatInterval.Valid] using ht
  · simpa only [rightChild,Function.update_of_ne hj] using hB j

/-- Proof data follows a finite binary tree. A leaf must be justified,
including any leaf pruned by an exact domain-disjointness check. -/
inductive Certificate {I : Type*} [DecidableEq I] (leaf : Cell I → Prop) : Cell I → Prop
  | accept {B : Cell I} : leaf B → Certificate leaf B
  | split {B : Cell I} (i : I) (t : ℚ) : (B i).lo ≤ t → t ≤ (B i).hi →
      Certificate leaf (leftChild B i t) → Certificate leaf (rightChild B i t) →
      Certificate leaf B

theorem certificate_sound {I : Type*} [DecidableEq I] {leaf : Cell I → Prop}
    {B : Cell I} (T : Certificate leaf B) (P : (I → ℝ) → Prop)
    (hleaf : ∀ C, leaf C → ∀ x, Mem C x → P x) : ∀ x, Mem B x → P x := by
  induction T with
  | accept h => exact hleaf _ h
  | @split C i t hlo hhi Tl Tr ihl ihr =>
      intro x hx
      rcases split_cover C i t hx with hl | hr
      · exact ihl x hl
      · exact ihr x hr

end N11Formalization.RationalBoxSubdivision
#check @N11Formalization.RationalBoxSubdivision.certificate_sound
#print axioms N11Formalization.RationalBoxSubdivision.midpoint_mem
#print axioms N11Formalization.RationalBoxSubdivision.distance_le_halfWidth
#print axioms N11Formalization.RationalBoxSubdivision.split_cover
#print axioms N11Formalization.RationalBoxSubdivision.certificate_sound
