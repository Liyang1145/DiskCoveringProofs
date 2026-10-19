import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22Data
def source22 : TenSeg := ⟨((2:ℚ)/25),((21:ℚ)/250),((2437379:ℚ)/1000000),((-106253:ℚ)/500000),((-125111:ℚ)/1000000),((-21421:ℚ)/500000),((118933:ℚ)/125000),((-597053:ℚ)/1000000),((319549:ℚ)/1000000),((-17431:ℚ)/500000)⟩
theorem source_eq : c450Segs[21]? = some source22 := by decide +kernel
theorem source_mem : source22 ∈ c450Segs := by decide +kernel
theorem nn0 : |source22.a1|+|source22.a2|+|source22.a3| ≤ source22.a0 := by decide +kernel
theorem nn1 : |source22.b1|+|source22.b2|+|source22.b3| ≤ source22.b0 := by decide +kernel
theorem eHi_le : source22.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source22Data
#print axioms N11Formalization.C450Source22Data.source_eq
#print axioms N11Formalization.C450Source22Data.nn0
#print axioms N11Formalization.C450Source22Data.nn1
