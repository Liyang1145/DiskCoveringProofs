import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28Data
def source28 : TenSeg := ⟨((13:ℚ)/125),((27:ℚ)/250),((1110529:ℚ)/500000),((-438427:ℚ)/1000000),((-8223:ℚ)/62500),((-45257:ℚ)/1000000),((1195251:ℚ)/1000000),((-4413:ℚ)/6250),((50913:ℚ)/125000),((-81867:ℚ)/1000000)⟩
theorem source_eq : c450Segs[27]? = some source28 := by decide +kernel
theorem source_mem : source28 ∈ c450Segs := by decide +kernel
theorem nn0 : |source28.a1|+|source28.a2|+|source28.a3| ≤ source28.a0 := by decide +kernel
theorem nn1 : |source28.b1|+|source28.b2|+|source28.b3| ≤ source28.b0 := by decide +kernel
theorem eHi_le : source28.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source28Data
#print axioms N11Formalization.C450Source28Data.source_eq
#print axioms N11Formalization.C450Source28Data.nn0
#print axioms N11Formalization.C450Source28Data.nn1
