import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34Data
def source34 : TenSeg := ⟨((16:ℚ)/125),((33:ℚ)/250),((267611:ℚ)/125000),((-485807:ℚ)/1000000),((1083:ℚ)/50000),((90029:ℚ)/1000000),((79307:ℚ)/62500),((-206147:ℚ)/250000),((314617:ℚ)/1000000),((-129707:ℚ)/1000000)⟩
theorem source_eq : c450Segs[33]? = some source34 := by decide +kernel
theorem source_mem : source34 ∈ c450Segs := by decide +kernel
theorem nn0 : |source34.a1|+|source34.a2|+|source34.a3| ≤ source34.a0 := by decide +kernel
theorem nn1 : |source34.b1|+|source34.b2|+|source34.b3| ≤ source34.b0 := by decide +kernel
theorem eHi_le : source34.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source34Data
#print axioms N11Formalization.C450Source34Data.source_eq
#print axioms N11Formalization.C450Source34Data.nn0
#print axioms N11Formalization.C450Source34Data.nn1
