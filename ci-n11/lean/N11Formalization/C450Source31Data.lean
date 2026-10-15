import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31Data
def source31 : TenSeg := ⟨((29:ℚ)/250),((3:ℚ)/25),((21903:ℚ)/10000),((-4483:ℚ)/10000),((-21009:ℚ)/1000000),((54999:ℚ)/1000000),((612693:ℚ)/500000),((-38707:ℚ)/50000),((331669:ℚ)/1000000),((-119577:ℚ)/1000000)⟩
theorem source_eq : c450Segs[30]? = some source31 := by decide +kernel
theorem source_mem : source31 ∈ c450Segs := by decide +kernel
theorem nn0 : |source31.a1|+|source31.a2|+|source31.a3| ≤ source31.a0 := by decide +kernel
theorem nn1 : |source31.b1|+|source31.b2|+|source31.b3| ≤ source31.b0 := by decide +kernel
theorem eHi_le : source31.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source31Data
#print axioms N11Formalization.C450Source31Data.source_eq
#print axioms N11Formalization.C450Source31Data.nn0
#print axioms N11Formalization.C450Source31Data.nn1
