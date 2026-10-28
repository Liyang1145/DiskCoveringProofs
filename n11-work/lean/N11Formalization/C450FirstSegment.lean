import N11Formalization.C450FirstRadialG01
import N11Formalization.C450FirstRadialG02
import N11Formalization.C450FirstRadialG03
import N11Formalization.C450FirstRadialG04
import N11Formalization.C450FirstRadialG05
import N11Formalization.C450FirstRadialG06
import N11Formalization.C450FirstRadialG07
import N11Formalization.C450FirstRadialG08

/-! Actual FIRST normalized source segment. All other35 remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FirstSegment
open C450FirstRadialKernel C450RadialMajorant C450NormalizedInterface

def first : TenSeg := c450Segs[0]'(by decide +kernel)
theorem first_mem : first ∈ c450Segs := by decide +kernel
theorem nn0 : |first.a1|+|first.a2|+|first.a3| ≤ first.a0 :=
  (c450Segs_nonneg first first_mem).1
theorem nn1 : |first.b1|+|first.b2|+|first.b3| ≤ first.b0 :=
  (c450Segs_nonneg first first_mem).2
def W0 : TrigDensity := first.W0 nn0
def W1 : TrigDensity := first.W1 nn1

theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((191:ℝ)/250), model r < (cap:ℝ) :=
  interval_join
    (interval_join
      (interval_join C450FirstRadialG01.bound C450FirstRadialG02.bound)
      (interval_join C450FirstRadialG03.bound C450FirstRadialG04.bound))
    (interval_join
      (interval_join C450FirstRadialG05.bound C450FirstRadialG06.bound)
      (interval_join C450FirstRadialG07.bound C450FirstRadialG08.bound))

theorem far_bound (r : ℝ) (hr : r ∈ Set.Icc ((191:ℝ)/250) ((69:ℝ)/50)) :
    model r < (cap:ℝ) := by
  have hz := z_mem (by linarith [hr.1]) hr.2
  have hc : Real.cos (Real.arccos (zOf r)) = zOf r := Real.cos_arccos hz.1 hz.2
  have ht := t_le_global (by linarith [hr.1] : 0 < r) (Real.arccos_le_pi _) hc
  have hb : betaUpper r (E:ℝ) = 0 := by
    unfold betaUpper
    apply Real.arccos_of_one_le
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2*(19/50))]
    norm_num [E]
    linarith [hr.1]
  have hA : (0:ℝ) ≤ (A:ℝ) := by norm_num [A]
  have hm := mul_le_mul_of_nonneg_left ht hA
  have hnum : A*Tglobal < cap := by decide +kernel
  have hnr : (A:ℝ)*(Tglobal:ℝ) < (cap:ℝ) := by exact_mod_cast hnum
  unfold model
  rw [hb,mul_zero,add_zero]
  exact hm.trans_lt hnr

theorem model_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50), model r < (cap:ℝ) :=
  interval_join near_bound (fun r hr => far_bound r hr)

theorem model_eq (r : ℝ) : model r = majorant W0 W1 (1/250) r := by
  norm_num [model,majorant,densitySup,A,B,M,E,W0,W1,first,c450Segs,TenSeg.W0,TenSeg.W1]

theorem radial_paid : RadialBound W0 W1 (1/250) := by
  intro r hr0 hr1
  have hb := model_bound r ⟨by linarith,by linarith⟩
  rw [model_eq] at hb
  have hc := cap_lt_actual
  change (cap:ℝ) < Real.pi*(W0.a0+W1.a0)/10 at hc
  exact hb.trans hc

theorem first_paid : SegmentNormalized first := by
  intro h0 h1
  have hp := normalized_of_radial W0 W1
    (by norm_num [W0,first,c450Segs,TenSeg.W0])
    (by norm_num [W0,first,c450Segs,TenSeg.W0])
    (by norm_num [W0,first,c450Segs,TenSeg.W0])
    0 (1/250) (by norm_num) radial_paid
  have he0 : (first.eLo:ℝ) = 0 := by norm_num [first,c450Segs]
  have he1 : (first.eHi:ℝ) = (1/250:ℝ) := by norm_num [first,c450Segs]
  rw [he0,he1]
  exact hp

def RemainingSourceObligation : Prop :=
  ∀ s ∈ c450Segs, s ≠ first → SegmentNormalized s

theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation := by
  intro s hs
  by_cases heq : s = first
  · rw [heq]
    exact first_paid
  · exact hr s hs heq
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450FirstSegment
#check @N11Formalization.C450FirstSegment.first_paid
#check @N11Formalization.C450FirstSegment.atom_of_remaining
#print axioms N11Formalization.C450FirstSegment.radial_paid
#print axioms N11Formalization.C450FirstSegment.first_paid
#print axioms N11Formalization.C450FirstSegment.atom_of_remaining
