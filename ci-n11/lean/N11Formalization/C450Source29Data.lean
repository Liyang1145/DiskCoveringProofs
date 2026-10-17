import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29Data
def source29 : TenSeg := ⟨((27:ℚ)/250),((14:ℚ)/125),((44527:ℚ)/20000),((-212969:ℚ)/500000),((-59621:ℚ)/1000000),((28417:ℚ)/1000000),((1190153:ℚ)/1000000),((-365971:ℚ)/500000),((21743:ℚ)/62500),((-110323:ℚ)/1000000)⟩
theorem source_eq : c450Segs[28]? = some source29 := by decide +kernel
theorem source_mem : source29 ∈ c450Segs := by decide +kernel
theorem nn0 : |source29.a1|+|source29.a2|+|source29.a3| ≤ source29.a0 := by decide +kernel
theorem nn1 : |source29.b1|+|source29.b2|+|source29.b3| ≤ source29.b0 := by decide +kernel
theorem eHi_le : source29.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source29Data
#print axioms N11Formalization.C450Source29Data.source_eq
#print axioms N11Formalization.C450Source29Data.nn0
#print axioms N11Formalization.C450Source29Data.nn1
