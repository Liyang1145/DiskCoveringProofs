import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17Data
def source17 : TenSeg := ⟨((3:ℚ)/50),((8:ℚ)/125),((1255837:ℚ)/500000),((-44577:ℚ)/500000),((-13717:ℚ)/250000),((-10379:ℚ)/500000),((406707:ℚ)/500000),((-240633:ℚ)/500000),((33789:ℚ)/200000),((-6647:ℚ)/1000000)⟩
theorem source_eq : c450Segs[16]? = some source17 := by decide +kernel
theorem source_mem : source17 ∈ c450Segs := by decide +kernel
theorem nn0 : |source17.a1|+|source17.a2|+|source17.a3| ≤ source17.a0 := by decide +kernel
theorem nn1 : |source17.b1|+|source17.b2|+|source17.b3| ≤ source17.b0 := by decide +kernel
theorem eHi_le : source17.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source17Data
#print axioms N11Formalization.C450Source17Data.source_eq
#print axioms N11Formalization.C450Source17Data.nn0
#print axioms N11Formalization.C450Source17Data.nn1
