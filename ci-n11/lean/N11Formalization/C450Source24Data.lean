import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24Data
def source24 : TenSeg := ⟨((11:ℚ)/125),((23:ℚ)/250),((2361027:ℚ)/1000000),((-318149:ℚ)/1000000),((-81607:ℚ)/500000),((-26327:ℚ)/500000),((522331:ℚ)/500000),((-306827:ℚ)/500000),((377783:ℚ)/1000000),((-2129:ℚ)/40000)⟩
theorem source_eq : c450Segs[23]? = some source24 := by decide +kernel
theorem source_mem : source24 ∈ c450Segs := by decide +kernel
theorem nn0 : |source24.a1|+|source24.a2|+|source24.a3| ≤ source24.a0 := by decide +kernel
theorem nn1 : |source24.b1|+|source24.b2|+|source24.b3| ≤ source24.b0 := by decide +kernel
theorem eHi_le : source24.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source24Data
#print axioms N11Formalization.C450Source24Data.source_eq
#print axioms N11Formalization.C450Source24Data.nn0
#print axioms N11Formalization.C450Source24Data.nn1
