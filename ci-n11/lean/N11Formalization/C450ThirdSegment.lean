import N11Formalization.C450SignedAngularMajorant
import N11Formalization.C450ThirdRadialNeg1
import N11Formalization.C450ThirdRadialNeg2
import N11Formalization.C450ThirdRadialMid
import N11Formalization.C450ThirdRadialPos
import N11Formalization.C450SecondSegment

/-! Actual THIRD normalized C450 source segment. Other33 remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ThirdSegment
open C450RadialPacketKernel C450AngularMajorant
open C450SignedAngularMajorant C450NormalizedInterface

def third : TenSeg := c450Segs[2]'(by decide +kernel)
theorem third_mem : third ∈ c450Segs := by decide +kernel
theorem nn0 : |third.a1|+|third.a2|+|third.a3| ≤ third.a0 :=
  (c450Segs_nonneg third third_mem).1
theorem nn1 : |third.b1|+|third.b2|+|third.b3| ≤ third.b0 :=
  (c450Segs_nonneg third third_mem).2
def W0 : TrigDensity := third.W0 nn0
def W1 : TrigDensity := third.W1 nn1

theorem neg1_model_eq (r : ℝ) :
    model C450ThirdRadialNeg1.params r =
      angularModel W0.a0 (tailSup W1-W1.a1) (-(71/10000)/2+(1/125)^2) r := by
  norm_num [model,C450ThirdRadialNeg1.params,W0,W1,third,c450Segs,TenSeg.W0,TenSeg.W1,tailSup]
theorem neg2_model_eq (r : ℝ) :
    model C450ThirdRadialNeg2.params r =
      angularModel W0.a0 (tailSup W1-W1.a1/2) ((1/125)^2) r := by
  norm_num [model,C450ThirdRadialNeg2.params,W0,W1,third,c450Segs,TenSeg.W0,TenSeg.W1,tailSup]
theorem mid_model_eq (r : ℝ) :
    model C450ThirdRadialMid.params r =
      angularModel W0.a0 (tailSup W1) (1/125/2+(1/125)^2) r := by
  norm_num [model,C450ThirdRadialMid.params,W0,W1,third,c450Segs,TenSeg.W0,TenSeg.W1,tailSup]
theorem pos_model_eq (r : ℝ) :
    model C450ThirdRadialPos.params r =
      angularModel W0.a0 (tailSup W1+(2/5)*W1.a1) (1/125+(1/125)^2) r := by
  norm_num [model,C450ThirdRadialPos.params,W0,W1,third,c450Segs,TenSeg.W0,TenSeg.W1,tailSup]

theorem neg1_radial_paid :
    AngularRadialBound W0.a0 W1.a0 (tailSup W1-W1.a1) (-(71/10000)/2+(1/125)^2) := by
  intro r hr0 hr1
  have hb := C450ThirdRadialNeg1.bound r ⟨hr0,hr1⟩
  rw [neg1_model_eq] at hb
  have hc := cap_lt_actual C450ThirdRadialNeg1.params C450ThirdRadialNeg1.params_valid
  change (cap C450ThirdRadialNeg1.params:ℝ) < Real.pi*(W0.a0+W1.a0)/10 at hc
  exact hb.trans hc
theorem neg2_radial_paid :
    AngularRadialBound W0.a0 W1.a0 (tailSup W1-W1.a1/2) ((1/125)^2) := by
  intro r hr0 hr1
  have hb := C450ThirdRadialNeg2.bound r ⟨hr0,hr1⟩
  rw [neg2_model_eq] at hb
  have hc := cap_lt_actual C450ThirdRadialNeg2.params C450ThirdRadialNeg2.params_valid
  change (cap C450ThirdRadialNeg2.params:ℝ) < Real.pi*(W0.a0+W1.a0)/10 at hc
  exact hb.trans hc
theorem mid_radial_paid :
    AngularRadialBound W0.a0 W1.a0 (tailSup W1) (1/125/2+(1/125)^2) := by
  intro r hr0 hr1
  have hb := C450ThirdRadialMid.bound r ⟨hr0,hr1⟩
  rw [mid_model_eq] at hb
  have hc := cap_lt_actual C450ThirdRadialMid.params C450ThirdRadialMid.params_valid
  change (cap C450ThirdRadialMid.params:ℝ) < Real.pi*(W0.a0+W1.a0)/10 at hc
  exact hb.trans hc
theorem pos_radial_paid :
    AngularRadialBound W0.a0 W1.a0 (tailSup W1+(2/5)*W1.a1) (1/125+(1/125)^2) := by
  intro r hr0 hr1
  have hb := C450ThirdRadialPos.bound r ⟨hr0,hr1⟩
  rw [pos_model_eq] at hb
  have hc := cap_lt_actual C450ThirdRadialPos.params C450ThirdRadialPos.params_valid
  change (cap C450ThirdRadialPos.params:ℝ) < Real.pi*(W0.a0+W1.a0)/10 at hc
  exact hb.trans hc

theorem third_paid : SegmentNormalized third := by
  intro h0 h1
  have hp := normalized_of_four W0 W1
    (by norm_num [W0,third,c450Segs,TenSeg.W0])
    (by norm_num [W0,third,c450Segs,TenSeg.W0])
    (by norm_num [W0,third,c450Segs,TenSeg.W0])
    (by norm_num [W1,third,c450Segs,TenSeg.W1])
    (71/10000) (1/125) (by norm_num) (by norm_num)
    neg1_radial_paid neg2_radial_paid mid_radial_paid pos_radial_paid
  have he0 : (third.eLo:ℝ) = (71/10000:ℝ) := by norm_num [third,c450Segs]
  have he1 : (third.eHi:ℝ) = (1/125:ℝ) := by norm_num [third,c450Segs]
  rw [he0,he1]
  exact hp

def remainingSegs : List TenSeg := c450Segs.drop 3
theorem remaining_count : remainingSegs.length = 33 := by decide +kernel
theorem second_remaining_split :
    C450SecondSegment.remainingSegs = third :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s
theorem second_remaining_of_remaining (hr : RemainingSourceObligation) :
    C450SecondSegment.RemainingSourceObligation := by
  intro s hs
  rw [second_remaining_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hthird | hrest
  · rw [hthird]
    exact third_paid
  · exact hr s hrest
theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation :=
  C450SecondSegment.source_of_remaining (second_remaining_of_remaining hr)
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450ThirdSegment
#check @N11Formalization.C450ThirdSegment.third_paid
#check @N11Formalization.C450ThirdSegment.atom_of_remaining
#print axioms N11Formalization.C450ThirdSegment.neg1_radial_paid
#print axioms N11Formalization.C450ThirdSegment.neg2_radial_paid
#print axioms N11Formalization.C450ThirdSegment.mid_radial_paid
#print axioms N11Formalization.C450ThirdSegment.pos_radial_paid
#print axioms N11Formalization.C450ThirdSegment.third_paid
#print axioms N11Formalization.C450ThirdSegment.atom_of_remaining
