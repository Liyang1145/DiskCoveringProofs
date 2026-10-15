import N11Formalization.SourceRawResponsePacket
import N11Formalization.SourceFineRelativeFluxPacket
import N11Formalization.StructuredCongruence
import N11Formalization.ResumeIntervalAugmented

/-! Actual correlation-preserving congruence memberships for ANY exact
rational8x8 proposal. H0 pair identity and G Gram factor are paid here.
Numerical transformedG containments/strict rows remain explicit inputs. -/
set_option autoImplicit false
namespace N11Formalization.SourceStructuredIntervals
open N11Formalization RatInterval Matrix SourceActiveMatrixIntervals
open SourceRawResponseIntervals SourceRawResponsePacket StructuredCongruence
noncomputable section

def rawG (k : Fin 9) (a : Fin 4) : ℝ :=
  SourceRelativeFluxGeometry.G (ResumeLocalIncidence.siteMap k) a
def realC (C : Matrix (Fin 8) (Fin 8) ℚ) : Matrix (Fin 8) (Fin 8) ℝ := C.map Rat.cast
def extendedC (C : Matrix (Fin 8) (Fin 8) ℚ) (k : Fin 9) (i : Fin 8) : ℚ :=
  if h : k.val<8 then C ⟨k.val,h⟩ i else 0

theorem extendedC_cast (C : Matrix (Fin 8) (Fin 8) ℚ) (k : Fin 9) (i : Fin 8) :
    (extendedC C k i : ℝ)=extendColumn (realC C) i k := by
  unfold extendedC extendColumn
  split_ifs <;> simp [realC]

def TInput (C : Matrix (Fin 8) (Fin 8) ℚ) (i : Fin 8) (a : Fin 4) : RatInterval :=
  sumI (fun k : Fin 8 => mul (ofRat (C k i)) (SourceFineRelativeFluxPacket.GB k.castSucc a))
theorem TInput_mem (C : Matrix (Fin 8) (Fin 8) ℚ) (i : Fin 8) (a : Fin 4) :
    (TInput C i a).Mem (transformedG rawG (realC C) i a) :=
  sumI_mem (fun k => mul_mem (ofRat_mem _) (SourceFineRelativeFluxPacket.GB_mem _ _))

def pairBox (C : Matrix (Fin 8) (Fin 8) ℚ) (i j : Fin 8) : RatInterval :=
  sumI (fun k : Fin 9 => sumI (fun l : Fin 9 => if k<l then
    mul (neg (HB k l)) (ofRat ((extendedC C k i-extendedC C l i)*
      (extendedC C k j-extendedC C l j))) else ofRat 0))
theorem pairBox_mem (C : Matrix (Fin 8) (Fin 8) ℚ) (i j : Fin 8) :
    (pairBox C i j).Mem
      (∑ k : Fin 9,∑ l : Fin 9,if k<l then -rawH0 k l*
        (extendColumn (realC C) i k-extendColumn (realC C) i l)*
        (extendColumn (realC C) j k-extendColumn (realC C) j l) else 0) := by
  apply sumI_mem
  intro k
  apply sumI_mem
  intro l
  by_cases h : k<l
  · simp only [if_pos h]
    have he := mul_mem (neg_mem (HB_mem k l (ne_of_lt h))) (ofRat_mem
      ((extendedC C k i-extendedC C l i)*(extendedC C k j-extendedC C l j)))
    simp only [Rat.cast_mul,Rat.cast_sub,extendedC_cast] at he
    convert he using 1 <;> ring
  · simp only [if_neg h]
    simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)

def gramBox (TB : Fin 8 → Fin 4 → RatInterval) (i j : Fin 8) : RatInterval :=
  sumI (fun a : Fin 4 => if i=j then sq (TB i a) else mul (TB i a) (TB j a))
theorem gramBox_mem (C : Matrix (Fin 8) (Fin 8) ℚ)
    (TB : Fin 8 → Fin 4 → RatInterval)
    (hT : ∀ i a,(TB i a).Mem (transformedG rawG (realC C) i a)) (i j : Fin 8) :
    (gramBox TB i j).Mem
      (∑ a : Fin 4,transformedG rawG (realC C) i a*transformedG rawG (realC C) j a) := by
  apply sumI_mem
  intro a
  by_cases h : i=j
  · subst j
    simp only [ite_true]
    simpa only [pow_two] using sq_mem_pow (hT i a)
  · simp only [if_neg h]
    exact mul_mem (hT i a) (hT j a)

def structuredBox (C : Matrix (Fin 8) (Fin 8) ℚ) (TB : Fin 8 → Fin 4 → RatInterval)
    (i j : Fin 8) : RatInterval :=
  sub (add (pairBox C i j) (mul (ofRat 1468) (gramBox TB i j)))
    (ofRat ((9/5000)*(∑ k : Fin 8,C k i*C k j)))

def actualAugmented : Matrix (Fin 8) (Fin 8) ℝ :=
  ResumeCoercivityCertificate.augmented
    (fun k l : Fin 8 => rawH0 k.castSucc l.castSucc)
    (fun k a => rawG k.castSucc a) 734 (9/5000)

theorem structuredBox_mem (C : Matrix (Fin 8) (Fin 8) ℚ)
    (TB : Fin 8 → Fin 4 → RatInterval)
    (hT : ∀ i a,(TB i a).Mem (transformedG rawG (realC C) i a)) (i j : Fin 8) :
    (structuredBox C TB i j).Mem
      (((realC C).transpose*actualAugmented*realC C) i j) := by
  have he := augmented_structured_entry rawH0 rawG (realC C)
    rawH0_symmetric rawH0_rowsum 734 (9/5000) i j
  rw [actualAugmented,he]
  have hdiag := ofRat_mem ((9/5000)*(∑ k : Fin 8,C k i*C k j))
  simp only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sum,realC,Matrix.map_apply] at hdiag
  have hm := sub_mem (add_mem (pairBox_mem C i j)
    (mul_mem (ofRat_mem 1468) (gramBox_mem C TB hT i j))) hdiag
  simpa only [structuredBox,realC,Matrix.map_apply,Rat.cast_ofNat,
    show (2 : ℝ)*734=1468 by norm_num] using hm

/-- Numerical provider interfaces exposed honestly; actual symmetry, row
zero, source H/G, factor2 and pin shape are supplied here, not premises. -/
theorem coercivity_of_certificate (C : Matrix (Fin 8) (Fin 8) ℚ)
    (TB : Fin 8 → Fin 4 → RatInterval) (QB : Fin 8 → Fin 8 → RatInterval)
    (hT : ∀ i a,Contains (TB i a) (TInput C i a))
    (hQ : ∀ i j,Contains (QB i j) (structuredBox C TB i j))
    (hrow : ∀ i,(1/2 : ℚ)+(∑ j : Fin 8,if j=i then 0 else (QB i j).abs.hi)≤(QB i i).lo)
    (x : Fin 8 → ℝ) :
    (9/5000 : ℝ)*(∑ i : Fin 8,x i^2)≤
      (∑ i : Fin 8,∑ j : Fin 8,rawH0 i.castSucc j.castSucc*x i*x j)+
        1468*(∑ a : Fin 4,(∑ i : Fin 8,rawG i.castSucc a*x i)^2) := by
  have hmem := structuredBox_mem C TB
    (fun i a => mem_of_contains (hT i a) (TInput_mem C i a))
  have hs := ResumeIntervalMatrix.congruence_symmetric actualAugmented (realC C)
    (ResumeIntervalAugmented.augmented_symmetric _ _ _ _ (fun i j =>
      rawH0_symmetric i.castSucc j.castSucc))
  have hn := ResumeIntervalCoercivity.nonneg_of_intervals actualAugmented (realC C) QB
    (1/2) (by norm_num) hs (fun i j => mem_of_contains (hQ i j) (hmem i j)) hrow x
  rw [actualAugmented,ResumeCoercivityCertificate.augmented_expansion] at hn
  norm_num at hn
  linarith

end
end N11Formalization.SourceStructuredIntervals
#check @N11Formalization.SourceStructuredIntervals.structuredBox_mem
#check @N11Formalization.SourceStructuredIntervals.coercivity_of_certificate
#print axioms N11Formalization.SourceStructuredIntervals.coercivity_of_certificate
