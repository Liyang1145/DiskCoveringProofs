import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12Data
def source12 : TenSeg := ⟨((1:ℚ)/25),((11:ℚ)/250),((126763:ℚ)/50000),((-24953:ℚ)/500000),((-1407:ℚ)/50000),((-549:ℚ)/62500),((46443:ℚ)/62500),((-162109:ℚ)/500000),((78211:ℚ)/1000000),((221:ℚ)/200000)⟩
theorem source_eq : c450Segs[11]? = some source12 := by decide +kernel
theorem source_mem : source12 ∈ c450Segs := by decide +kernel
theorem nn0 : |source12.a1|+|source12.a2|+|source12.a3| ≤ source12.a0 := by decide +kernel
theorem nn1 : |source12.b1|+|source12.b2|+|source12.b3| ≤ source12.b0 := by decide +kernel
theorem eHi_le : source12.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source12Data
#print axioms N11Formalization.C450Source12Data.source_eq
#print axioms N11Formalization.C450Source12Data.nn0
#print axioms N11Formalization.C450Source12Data.nn1
