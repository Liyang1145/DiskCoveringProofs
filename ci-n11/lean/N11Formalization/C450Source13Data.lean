import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13Data
def source13 : TenSeg := ⟨((11:ℚ)/250),((6:ℚ)/125),((316023:ℚ)/125000),((-12353:ℚ)/200000),((-35689:ℚ)/1000000),((-2347:ℚ)/200000),((378969:ℚ)/500000),((-35023:ℚ)/100000),((96127:ℚ)/1000000),((261:ℚ)/250000)⟩
theorem source_eq : c450Segs[12]? = some source13 := by decide +kernel
theorem source_mem : source13 ∈ c450Segs := by decide +kernel
theorem nn0 : |source13.a1|+|source13.a2|+|source13.a3| ≤ source13.a0 := by decide +kernel
theorem nn1 : |source13.b1|+|source13.b2|+|source13.b3| ≤ source13.b0 := by decide +kernel
theorem eHi_le : source13.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source13Data
#print axioms N11Formalization.C450Source13Data.source_eq
#print axioms N11Formalization.C450Source13Data.nn0
#print axioms N11Formalization.C450Source13Data.nn1
