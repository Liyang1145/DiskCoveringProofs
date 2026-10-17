import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20Data
def source20 : TenSeg := ⟨((9:ℚ)/125),((19:ℚ)/250),((499617:ℚ)/200000),((-111007:ℚ)/1000000),((-17749:ℚ)/250000),((-14717:ℚ)/500000),((21623:ℚ)/25000),((-14711:ℚ)/25000),((238913:ℚ)/1000000),((-18151:ℚ)/1000000)⟩
theorem source_eq : c450Segs[19]? = some source20 := by decide +kernel
theorem source_mem : source20 ∈ c450Segs := by decide +kernel
theorem nn0 : |source20.a1|+|source20.a2|+|source20.a3| ≤ source20.a0 := by decide +kernel
theorem nn1 : |source20.b1|+|source20.b2|+|source20.b3| ≤ source20.b0 := by decide +kernel
theorem eHi_le : source20.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source20Data
#print axioms N11Formalization.C450Source20Data.source_eq
#print axioms N11Formalization.C450Source20Data.nn0
#print axioms N11Formalization.C450Source20Data.nn1
