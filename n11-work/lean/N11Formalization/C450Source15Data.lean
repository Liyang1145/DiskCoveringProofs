import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15Data
def source15 : TenSeg := ⟨((13:ℚ)/250),((7:ℚ)/125),((1260629:ℚ)/500000),((-9169:ℚ)/125000),((-43591:ℚ)/1000000),((-15237:ℚ)/1000000),((97841:ℚ)/125000),((-20801:ℚ)/50000),((25729:ℚ)/200000),((-2289:ℚ)/1000000)⟩
theorem source_eq : c450Segs[14]? = some source15 := by decide +kernel
theorem source_mem : source15 ∈ c450Segs := by decide +kernel
theorem nn0 : |source15.a1|+|source15.a2|+|source15.a3| ≤ source15.a0 := by decide +kernel
theorem nn1 : |source15.b1|+|source15.b2|+|source15.b3| ≤ source15.b0 := by decide +kernel
theorem eHi_le : source15.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source15Data
#print axioms N11Formalization.C450Source15Data.source_eq
#print axioms N11Formalization.C450Source15Data.nn0
#print axioms N11Formalization.C450Source15Data.nn1
