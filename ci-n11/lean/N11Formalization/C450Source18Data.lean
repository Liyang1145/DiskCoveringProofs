import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18Data
def source18 : TenSeg := ⟨((8:ℚ)/125),((17:ℚ)/250),((501443:ℚ)/200000),((-48167:ℚ)/500000),((-60391:ℚ)/1000000),((-11929:ℚ)/500000),((82963:ℚ)/100000),((-51559:ℚ)/100000),((95227:ℚ)/500000),((-453:ℚ)/50000)⟩
theorem source_eq : c450Segs[17]? = some source18 := by decide +kernel
theorem source_mem : source18 ∈ c450Segs := by decide +kernel
theorem nn0 : |source18.a1|+|source18.a2|+|source18.a3| ≤ source18.a0 := by decide +kernel
theorem nn1 : |source18.b1|+|source18.b2|+|source18.b3| ≤ source18.b0 := by decide +kernel
theorem eHi_le : source18.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source18Data
#print axioms N11Formalization.C450Source18Data.source_eq
#print axioms N11Formalization.C450Source18Data.nn0
#print axioms N11Formalization.C450Source18Data.nn1
