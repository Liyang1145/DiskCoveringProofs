import N11Formalization.HarmonicFieldsB02
import N11Formalization.HarmonicField278
set_option autoImplicit false
namespace N11Formalization.HarmonicFieldsB03
open Finset CertifiedHarmonicField
def sourceID : Fin 6 → Fin 371 := ![210,249,264,265,278,297]
-- Index4 is unused in baseIndex; it is the new actual packet278, not an alias.
def baseIndex : Fin 6 → Fin 7 := ![0,1,3,4,0,5]
def packet (f : Fin 6) : Packet :=
  if f = 4 then HarmonicField278.packet else HarmonicFieldsB02.packet (baseIndex f)
theorem all_valid (f : Fin 6) : Valid (packet f) := by
  by_cases h : f = 4
  · simpa only [packet, if_pos h] using HarmonicField278.valid
  · simpa only [packet, if_neg h] using HarmonicFieldsB02.all_valid (baseIndex f)
theorem sourceID_injective : Function.Injective sourceID := by
  unfold Function.Injective
  decide +kernel
theorem new_packet : packet 4 = HarmonicField278.packet := rfl
theorem reuse_source_binding (f : Fin 6) (h : f ≠ 4) :
    sourceID f = HarmonicFieldsB02.sourceID (baseIndex f) := by
  have hn : ∀ f : Fin 6, f ≠ 4 →
      sourceID f = HarmonicFieldsB02.sourceID (baseIndex f) := by decide +kernel
  exact hn f h
theorem oracle (f : Fin 6) (y : Fin 9 → ℝ) :
    fieldEnergy (packet f) (FlashCosine.theta y) ≤
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  chart_energy_le_oracle (packet f) (all_valid f) y
theorem mixture_oracle (b : Fin 6 → ℚ) (w : Fin 36 → ℚ)
    (hb0 : ∀ f, 0 ≤ b f) (hb1 : ∑ f, b f = 1)
    (hw : ∀ k, w k ≤ CertifiedFieldMixtures.mixWeight packet b k) (y : Fin 9 → ℝ) :
    ConvexMinorantCore.weightedEnergy w y ≤
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  CertifiedFieldMixtures.weightedEnergy_le_oracle packet all_valid b w hb0 hb1 hw y
end N11Formalization.HarmonicFieldsB03
#check @N11Formalization.HarmonicFieldsB03.all_valid
#check @N11Formalization.HarmonicFieldsB03.reuse_source_binding
#check @N11Formalization.HarmonicFieldsB03.mixture_oracle
#print axioms N11Formalization.HarmonicFieldsB03.oracle
#print axioms N11Formalization.HarmonicFieldsB03.mixture_oracle
