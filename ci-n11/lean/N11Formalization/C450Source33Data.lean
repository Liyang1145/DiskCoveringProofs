import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33Data
def source33 : TenSeg := ⟨((31:ℚ)/250),((16:ℚ)/125),((1078281:ℚ)/500000),((-118223:ℚ)/250000),((2337:ℚ)/250000),((7861:ℚ)/100000),((39243:ℚ)/31250),((-404747:ℚ)/500000),((63913:ℚ)/200000),((-126717:ℚ)/1000000)⟩
theorem source_eq : c450Segs[32]? = some source33 := by decide +kernel
theorem source_mem : source33 ∈ c450Segs := by decide +kernel
theorem nn0 : |source33.a1|+|source33.a2|+|source33.a3| ≤ source33.a0 := by decide +kernel
theorem nn1 : |source33.b1|+|source33.b2|+|source33.b3| ≤ source33.b0 := by decide +kernel
theorem eHi_le : source33.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source33Data
#print axioms N11Formalization.C450Source33Data.source_eq
#print axioms N11Formalization.C450Source33Data.nn0
#print axioms N11Formalization.C450Source33Data.nn1
