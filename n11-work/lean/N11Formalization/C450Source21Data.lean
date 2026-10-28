import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21Data
def source21 : TenSeg := ⟨((19:ℚ)/250),((2:ℚ)/25),((2472381:ℚ)/1000000),((-153577:ℚ)/1000000),((-97517:ℚ)/1000000),((-39747:ℚ)/1000000),((452251:ℚ)/500000),((-598119:ℚ)/1000000),((17659:ℚ)/62500),((-23839:ℚ)/1000000)⟩
theorem source_eq : c450Segs[20]? = some source21 := by decide +kernel
theorem source_mem : source21 ∈ c450Segs := by decide +kernel
theorem nn0 : |source21.a1|+|source21.a2|+|source21.a3| ≤ source21.a0 := by decide +kernel
theorem nn1 : |source21.b1|+|source21.b2|+|source21.b3| ≤ source21.b0 := by decide +kernel
theorem eHi_le : source21.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source21Data
#print axioms N11Formalization.C450Source21Data.source_eq
#print axioms N11Formalization.C450Source21Data.nn0
#print axioms N11Formalization.C450Source21Data.nn1
