import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32Data
def source32 : TenSeg := ⟨((3:ℚ)/25),((31:ℚ)/250),((543489:ℚ)/250000),((-228903:ℚ)/500000),((-2217:ℚ)/1000000),((13601:ℚ)/200000),((1240349:ℚ)/1000000),((-793773:ℚ)/1000000),((161441:ℚ)/500000),((-61847:ℚ)/500000)⟩
theorem source_eq : c450Segs[31]? = some source32 := by decide +kernel
theorem source_mem : source32 ∈ c450Segs := by decide +kernel
theorem nn0 : |source32.a1|+|source32.a2|+|source32.a3| ≤ source32.a0 := by decide +kernel
theorem nn1 : |source32.b1|+|source32.b2|+|source32.b3| ≤ source32.b0 := by decide +kernel
theorem eHi_le : source32.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source32Data
#print axioms N11Formalization.C450Source32Data.source_eq
#print axioms N11Formalization.C450Source32Data.nn0
#print axioms N11Formalization.C450Source32Data.nn1
