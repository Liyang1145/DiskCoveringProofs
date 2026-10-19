import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25Data
def source25 : TenSeg := ⟨((23:ℚ)/250),((12:ℚ)/125),((1162893:ℚ)/500000),((-71319:ℚ)/200000),((-10451:ℚ)/62500),((-54393:ℚ)/1000000),((135621:ℚ)/125000),((-19723:ℚ)/31250),((393177:ℚ)/1000000),((-12131:ℚ)/200000)⟩
theorem source_eq : c450Segs[24]? = some source25 := by decide +kernel
theorem source_mem : source25 ∈ c450Segs := by decide +kernel
theorem nn0 : |source25.a1|+|source25.a2|+|source25.a3| ≤ source25.a0 := by decide +kernel
theorem nn1 : |source25.b1|+|source25.b2|+|source25.b3| ≤ source25.b0 := by decide +kernel
theorem eHi_le : source25.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source25Data
#print axioms N11Formalization.C450Source25Data.source_eq
#print axioms N11Formalization.C450Source25Data.nn0
#print axioms N11Formalization.C450Source25Data.nn1
