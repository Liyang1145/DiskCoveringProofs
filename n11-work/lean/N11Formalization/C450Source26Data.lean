import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26Data
def source26 : TenSeg := ⟨((12:ℚ)/125),((1:ℚ)/10),((14281:ℚ)/6250),((-11689:ℚ)/31250),((-153409:ℚ)/1000000),((-68827:ℚ)/1000000),((141171:ℚ)/125000),((-66779:ℚ)/100000),((50391:ℚ)/125000),((-1169:ℚ)/20000)⟩
theorem source_eq : c450Segs[25]? = some source26 := by decide +kernel
theorem source_mem : source26 ∈ c450Segs := by decide +kernel
theorem nn0 : |source26.a1|+|source26.a2|+|source26.a3| ≤ source26.a0 := by decide +kernel
theorem nn1 : |source26.b1|+|source26.b2|+|source26.b3| ≤ source26.b0 := by decide +kernel
theorem eHi_le : source26.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source26Data
#print axioms N11Formalization.C450Source26Data.source_eq
#print axioms N11Formalization.C450Source26Data.nn0
#print axioms N11Formalization.C450Source26Data.nn1
