import N11Formalization.HarmonicFieldsB01A
import N11Formalization.HarmonicFieldsB01B
import N11Formalization.CertifiedFieldMixtures
set_option autoImplicit false
namespace N11Formalization.HarmonicFieldsB01
open Finset CertifiedHarmonicField
def sourceID : Fin 8 → Fin 371 := ![58,70,73,160,166,169,197,211]
def packet (f : Fin 8) : Packet :=
  if h : f.val < 4 then HarmonicFieldsB01A.packet ⟨f.val,h⟩
  else HarmonicFieldsB01B.packet ⟨f.val-4,by have := f.isLt; omega⟩
theorem all_valid (f : Fin 8) : Valid (packet f) := by
  by_cases h : f.val < 4
  · simpa only [packet,dif_pos h] using HarmonicFieldsB01A.all_valid ⟨f.val,h⟩
  · simpa only [packet,dif_neg h] using
      HarmonicFieldsB01B.all_valid ⟨f.val-4,by have := f.isLt; omega⟩
theorem oracle (f : Fin 8) (y : Fin 9 → ℝ) :
    fieldEnergy (packet f) (FlashCosine.theta y) ≤
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  chart_energy_le_oracle (packet f) (all_valid f) y
theorem sourceID_injective : Function.Injective sourceID := by
  unfold Function.Injective
  decide +kernel
theorem mixture_oracle (b : Fin 8 → ℚ) (w : Fin 36 → ℚ)
    (hb0 : ∀ f,0 ≤ b f) (hb1 : ∑ f,b f=1)
    (hw : ∀ k,w k ≤ CertifiedFieldMixtures.mixWeight packet b k) (y : Fin 9 → ℝ) :
    ConvexMinorantCore.weightedEnergy w y ≤
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  CertifiedFieldMixtures.weightedEnergy_le_oracle packet all_valid b w hb0 hb1 hw y
end N11Formalization.HarmonicFieldsB01
#check @N11Formalization.HarmonicFieldsB01.all_valid
#check @N11Formalization.HarmonicFieldsB01.oracle
#check @N11Formalization.HarmonicFieldsB01.mixture_oracle
#print axioms N11Formalization.HarmonicFieldsB01.oracle
#print axioms N11Formalization.HarmonicFieldsB01.mixture_oracle
