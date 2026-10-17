import N11Formalization.C450SecondRadialNeg
import N11Formalization.C450SecondRadialMid
import N11Formalization.C450SecondRadialPos
import N11Formalization.C450FirstSegment

/-! Genuine second normalized C450 segment. All other34 remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SecondSegment
open C450SecondRadialKernel C450AngularMajorant C450NormalizedInterface

def second : TenSeg := c450Segs[1]'(by decide +kernel)
theorem second_mem : second ∈ c450Segs := by decide +kernel
theorem nn0 : |second.a1|+|second.a2|+|second.a3| ≤ second.a0 :=
  (c450Segs_nonneg second second_mem).1
theorem nn1 : |second.b1|+|second.b2|+|second.b3| ≤ second.b0 :=
  (c450Segs_nonneg second second_mem).2
def W0 : TrigDensity := second.W0 nn0
def W1 : TrigDensity := second.W1 nn1

theorem neg_model_eq (r : ℝ) :
    model .neg r = angularModel W0.a0 (tailSup W1-W1.a1) ((71/10000)^2) r := by
  norm_num [model,A,M,F,E,tail,B,H,W0,W1,second,c450Segs,TenSeg.W0,TenSeg.W1,tailSup]
theorem mid_model_eq (r : ℝ) :
    model .mid r = angularModel W0.a0 (tailSup W1) (71/10000/2+(71/10000)^2) r := by
  norm_num [model,A,M,F,E,tail,B,H,W0,W1,second,c450Segs,TenSeg.W0,TenSeg.W1,tailSup]
theorem pos_model_eq (r : ℝ) :
    model .pos r = angularModel W0.a0 (tailSup W1+(2/5)*W1.a1) (71/10000+(71/10000)^2) r := by
  norm_num [model,A,M,F,E,tail,B,H,W0,W1,second,c450Segs,TenSeg.W0,TenSeg.W1,tailSup]

theorem neg_radial_paid : AngularRadialBound W0.a0 W1.a0 (tailSup W1-W1.a1) ((71/10000)^2) := by
  intro r hr0 hr1
  have hb := C450SecondRadialNeg.bound r ⟨hr0,hr1⟩
  rw [neg_model_eq] at hb
  have hc := cap_lt_actual
  change (cap:ℝ) < Real.pi*(W0.a0+W1.a0)/10 at hc
  exact hb.trans hc
theorem mid_radial_paid : AngularRadialBound W0.a0 W1.a0 (tailSup W1) (71/10000/2+(71/10000)^2) := by
  intro r hr0 hr1
  have hb := C450SecondRadialMid.bound r ⟨hr0,hr1⟩
  rw [mid_model_eq] at hb
  have hc := cap_lt_actual
  change (cap:ℝ) < Real.pi*(W0.a0+W1.a0)/10 at hc
  exact hb.trans hc
theorem pos_radial_paid : AngularRadialBound W0.a0 W1.a0 (tailSup W1+(2/5)*W1.a1) (71/10000+(71/10000)^2) := by
  intro r hr0 hr1
  have hb := C450SecondRadialPos.bound r ⟨hr0,hr1⟩
  rw [pos_model_eq] at hb
  have hc := cap_lt_actual
  change (cap:ℝ) < Real.pi*(W0.a0+W1.a0)/10 at hc
  exact hb.trans hc

theorem second_paid : SegmentNormalized second := by
  intro h0 h1
  have hp := normalized_of_three W0 W1
    (by norm_num [W0,second,c450Segs,TenSeg.W0])
    (by norm_num [W0,second,c450Segs,TenSeg.W0])
    (by norm_num [W0,second,c450Segs,TenSeg.W0])
    (by norm_num [W1,second,c450Segs,TenSeg.W1])
    (1/250) (71/10000) (by norm_num)
    neg_radial_paid mid_radial_paid pos_radial_paid
  have he0 : (second.eLo:ℝ) = (1/250:ℝ) := by norm_num [second,c450Segs]
  have he1 : (second.eHi:ℝ) = (71/10000:ℝ) := by norm_num [second,c450Segs]
  rw [he0,he1]
  exact hp

def remainingSegs : List TenSeg := c450Segs.drop 2
theorem remaining_count : remainingSegs.length = 34 := by decide +kernel
theorem segs_split : c450Segs = C450FirstSegment.first :: second :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s

theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation := by
  intro s hs
  rw [segs_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hfirst | hsecond | hrem
  · rw [hfirst]
    exact C450FirstSegment.first_paid
  · rw [hsecond]
    exact second_paid
  · exact hr s hrem
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450SecondSegment
#check @N11Formalization.C450SecondSegment.second_paid
#check @N11Formalization.C450SecondSegment.atom_of_remaining
#print axioms N11Formalization.C450SecondSegment.neg_radial_paid
#print axioms N11Formalization.C450SecondSegment.mid_radial_paid
#print axioms N11Formalization.C450SecondSegment.pos_radial_paid
#print axioms N11Formalization.C450SecondSegment.second_paid
#print axioms N11Formalization.C450SecondSegment.atom_of_remaining
