import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14Data
def source14 : TenSeg := ⟨((6:ℚ)/125),((13:ℚ)/250),((1262853:ℚ)/500000),((-65913:ℚ)/1000000),((-2397:ℚ)/62500),((-12797:ℚ)/1000000),((768919:ℚ)/1000000),((-384303:ℚ)/1000000),((27543:ℚ)/250000),((-633:ℚ)/1000000)⟩
theorem source_eq : c450Segs[13]? = some source14 := by decide +kernel
theorem source_mem : source14 ∈ c450Segs := by decide +kernel
theorem nn0 : |source14.a1|+|source14.a2|+|source14.a3| ≤ source14.a0 := by decide +kernel
theorem nn1 : |source14.b1|+|source14.b2|+|source14.b3| ≤ source14.b0 := by decide +kernel
theorem eHi_le : source14.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source14Data
#print axioms N11Formalization.C450Source14Data.source_eq
#print axioms N11Formalization.C450Source14Data.nn0
#print axioms N11Formalization.C450Source14Data.nn1
