import N11Formalization.HarmonicFieldsB01
import N11Formalization.HarmonicFieldsB02
import N11Formalization.HarmonicField278
set_option autoImplicit false
namespace N11Formalization.HarmonicFieldsPaid16
open Finset CertifiedHarmonicField
def sourceID : Fin 16 → Fin 371 :=
  ![58,70,73,160,166,169,197,211,210,249,263,264,265,297,298,278]
def packet (f : Fin 16) : Packet :=
  if h : f.val < 8 then HarmonicFieldsB01.packet ⟨f.val,h⟩
  else if h2 : f.val < 15 then HarmonicFieldsB02.packet ⟨f.val-8,by omega⟩
  else HarmonicField278.packet
theorem all_valid (f : Fin 16) : Valid (packet f) := by
  by_cases h : f.val < 8
  · simpa only [packet,dif_pos h] using HarmonicFieldsB01.all_valid ⟨f.val,h⟩
  · by_cases h2 : f.val < 15
    · simpa only [packet,dif_neg h,dif_pos h2] using
        HarmonicFieldsB02.all_valid ⟨f.val-8,by omega⟩
    · simpa only [packet,dif_neg h,dif_neg h2] using HarmonicField278.valid
theorem sourceID_injective : Function.Injective sourceID := by
  unfold Function.Injective
  decide +kernel
theorem oracle (f : Fin 16) (y : Fin 9 → ℝ) :
    fieldEnergy (packet f) (FlashCosine.theta y) ≤
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  chart_energy_le_oracle (packet f) (all_valid f) y
end N11Formalization.HarmonicFieldsPaid16
#check @N11Formalization.HarmonicFieldsPaid16.all_valid
#check @N11Formalization.HarmonicFieldsPaid16.oracle
#print axioms N11Formalization.HarmonicFieldsPaid16.oracle
