import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35Data
def source35 : TenSeg := ⟨((33:ℚ)/250),((17:ℚ)/125),((2125163:ℚ)/1000000),((-313:ℚ)/625),((1533:ℚ)/50000),((100773:ℚ)/1000000),((640781:ℚ)/500000),((-837559:ℚ)/1000000),((12459:ℚ)/40000),((-8283:ℚ)/62500)⟩
theorem source_eq : c450Segs[34]? = some source35 := by decide +kernel
theorem source_mem : source35 ∈ c450Segs := by decide +kernel
theorem nn0 : |source35.a1|+|source35.a2|+|source35.a3| ≤ source35.a0 := by decide +kernel
theorem nn1 : |source35.b1|+|source35.b2|+|source35.b3| ≤ source35.b0 := by decide +kernel
theorem eHi_le : source35.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source35Data
#print axioms N11Formalization.C450Source35Data.source_eq
#print axioms N11Formalization.C450Source35Data.nn0
#print axioms N11Formalization.C450Source35Data.nn1
