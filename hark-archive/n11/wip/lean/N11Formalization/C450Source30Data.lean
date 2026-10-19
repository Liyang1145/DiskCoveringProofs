import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30Data
def source30 : TenSeg := ⟨((14:ℚ)/125),((29:ℚ)/250),((2208767:ℚ)/1000000),((-434279:ℚ)/1000000),((-36759:ℚ)/1000000),((42687:ℚ)/1000000),((603827:ℚ)/500000),((-755167:ℚ)/1000000),((168521:ℚ)/500000),((-23089:ℚ)/200000)⟩
theorem source_eq : c450Segs[29]? = some source30 := by decide +kernel
theorem source_mem : source30 ∈ c450Segs := by decide +kernel
theorem nn0 : |source30.a1|+|source30.a2|+|source30.a3| ≤ source30.a0 := by decide +kernel
theorem nn1 : |source30.b1|+|source30.b2|+|source30.b3| ≤ source30.b0 := by decide +kernel
theorem eHi_le : source30.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source30Data
#print axioms N11Formalization.C450Source30Data.source_eq
#print axioms N11Formalization.C450Source30Data.nn0
#print axioms N11Formalization.C450Source30Data.nn1
