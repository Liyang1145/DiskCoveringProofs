import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27Data
def source27 : TenSeg := ⟨((1:ℚ)/10),((13:ℚ)/125),((2250997:ℚ)/1000000),((-396597:ℚ)/1000000),((-139349:ℚ)/1000000),((-67941:ℚ)/1000000),((145631:ℚ)/125000),((-694609:ℚ)/1000000),((20341:ℚ)/50000),((-63619:ℚ)/1000000)⟩
theorem source_eq : c450Segs[26]? = some source27 := by decide +kernel
theorem source_mem : source27 ∈ c450Segs := by decide +kernel
theorem nn0 : |source27.a1|+|source27.a2|+|source27.a3| ≤ source27.a0 := by decide +kernel
theorem nn1 : |source27.b1|+|source27.b2|+|source27.b3| ≤ source27.b0 := by decide +kernel
theorem eHi_le : source27.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source27Data
#print axioms N11Formalization.C450Source27Data.source_eq
#print axioms N11Formalization.C450Source27Data.nn0
#print axioms N11Formalization.C450Source27Data.nn1
