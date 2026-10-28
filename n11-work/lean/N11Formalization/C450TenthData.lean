import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthData
def tenth : TenSeg := ⟨((4:ℚ)/125),((9:ℚ)/250),((318087:ℚ)/125000),((-6853:ℚ)/200000),((-9577:ℚ)/500000),((-5873:ℚ)/1000000),((11257:ℚ)/15625),((-133077:ℚ)/500000),((51583:ℚ)/1000000),((1959:ℚ)/1000000)⟩
theorem source_eq : c450Segs[9]? = some tenth := by decide +kernel
theorem source_mem : tenth ∈ c450Segs := by decide +kernel
theorem nn0 : |tenth.a1|+|tenth.a2|+|tenth.a3| ≤ tenth.a0 := by decide +kernel
theorem nn1 : |tenth.b1|+|tenth.b2|+|tenth.b3| ≤ tenth.b0 := by decide +kernel
theorem eHi_le : tenth.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450TenthData
#print axioms N11Formalization.C450TenthData.source_eq
#print axioms N11Formalization.C450TenthData.nn0
#print axioms N11Formalization.C450TenthData.nn1
