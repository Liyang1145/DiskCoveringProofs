import N11Formalization.SourceCrossGeometry
import N11Formalization.FlashLocalFrobeniusEnclosure

/-! Exact64 raw8-deleted actual Cmat enclosures and rational Frobenius
comparison. Host endpoints are checked, never assumed equal to Cmat. -/
set_option autoImplicit false
namespace N11Formalization.SourceCrossPacket
open N11Formalization RatInterval SourceCrossGeometry
noncomputable section
set_option maxRecDepth 10000

def CL : Fin 8 → Fin 8 → ℤ :=
 ![![-2,-8402387,-2849707,-170819,-54161,585661,1290621,2310435],![8397676,-2,-9384742,-726250,-358403,-611818,629909,1290734],![2841620,9380277,-2,-9945629,-942210,-1967658,-612182,585299],![164072,718978,9938958,-2,-9512874,-940678,-358161,-54073],![51563,351950,933451,9507530,-1,-9944260,-725989,-170597],![-589382,609429,1960053,931994,9938237,-2,-9386013,-2851362],![-1297262,-632185,609683,351671,718639,9379893,-2,-8403211],![-2318311,-1297107,-588791,51459,163796,2842181,8396933,-2]]

def CH : Fin 8 → Fin 8 → ℤ :=
 ![![2,-8396933,-2842181,-163796,-51459,588791,1297107,2318311],![8403211,2,-9379893,-718639,-351671,-609683,632185,1297262],![2851362,9386013,2,-9938237,-931994,-1960053,-609429,589382],![170597,725989,9944260,2,-9507530,-933451,-351950,-51563],![54073,358161,940678,9512874,1,-9938958,-718978,-164072],![-585299,612182,1967658,942210,9945629,2,-9380277,-2841620],![-1290734,-629909,611818,358403,726250,9384742,2,-8397676],![-2310435,-1290621,-585661,54161,170819,2849707,8402387,2]]

def CB (k l : Fin 8) : RatInterval :=
  intv ((CL k l : ℚ)/1000000000) ((CH k l : ℚ)/1000000000)
private theorem row0 (l : Fin 8) : Contains (CB 0 l) (crossInput 0 l) := by
  fin_cases l <;> unfold Contains <;> decide +kernel
private theorem row1 (l : Fin 8) : Contains (CB 1 l) (crossInput 1 l) := by
  fin_cases l <;> unfold Contains <;> decide +kernel
private theorem row2 (l : Fin 8) : Contains (CB 2 l) (crossInput 2 l) := by
  fin_cases l <;> unfold Contains <;> decide +kernel
private theorem row3 (l : Fin 8) : Contains (CB 3 l) (crossInput 3 l) := by
  fin_cases l <;> unfold Contains <;> decide +kernel
private theorem row4 (l : Fin 8) : Contains (CB 4 l) (crossInput 4 l) := by
  fin_cases l <;> unfold Contains <;> decide +kernel
private theorem row5 (l : Fin 8) : Contains (CB 5 l) (crossInput 5 l) := by
  fin_cases l <;> unfold Contains <;> decide +kernel
private theorem row6 (l : Fin 8) : Contains (CB 6 l) (crossInput 6 l) := by
  fin_cases l <;> unfold Contains <;> decide +kernel
private theorem row7 (l : Fin 8) : Contains (CB 7 l) (crossInput 7 l) := by
  fin_cases l <;> unfold Contains <;> decide +kernel

theorem CB_contains (k l : Fin 8) : Contains (CB k l) (crossInput k l) := by
  fin_cases k
  · exact row0 l
  · exact row1 l
  · exact row2 l
  · exact row3 l
  · exact row4 l
  · exact row5 l
  · exact row6 l
  · exact row7 l

theorem CB_mem (k l : Fin 8) : (CB k l).Mem (rawCross k.castSucc l.castSucc) :=
  mem_of_contains (CB_contains k l) (crossInput_mem k l)

theorem frobenius_certificate :
    (∑ k : Fin 8,∑ l : Fin 8,(CB k l).abs.hi^2)≤(179/5000 : ℚ)^2 := by
  decide +kernel

theorem actual_raw_frobenius :
    (∑ k : Fin 8,∑ l : Fin 8,(rawCross k.castSucc l.castSucc)^2)≤(179/5000 : ℝ)^2 := by
  have h := FlashLocal.matrix_frob_sq_le_of_boxes
    (fun k l : Fin 8 => rawCross k.castSucc l.castSucc) CB CB_mem
  have hc : (((∑ k : Fin 8,∑ l : Fin 8,(CB k l).abs.hi^2) : ℚ) : ℝ)≤
      (179/5000 : ℝ)^2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr frobenius_certificate
    simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] using hh
  exact h.trans hc

end
end N11Formalization.SourceCrossPacket
#check @N11Formalization.SourceCrossPacket.CB_mem
#check @N11Formalization.SourceCrossPacket.frobenius_certificate
#check @N11Formalization.SourceCrossPacket.actual_raw_frobenius
#print axioms N11Formalization.SourceCrossPacket.actual_raw_frobenius
