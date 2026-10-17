import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19Data
def source19 : TenSeg := ⟨((17:ℚ)/250),((9:ℚ)/125),((500141:ℚ)/200000),((-106689:ℚ)/1000000),((-13647:ℚ)/200000),((-28289:ℚ)/1000000),((424413:ℚ)/500000),((-68653:ℚ)/125000),((108613:ℚ)/500000),((-6511:ℚ)/500000)⟩
theorem source_eq : c450Segs[18]? = some source19 := by decide +kernel
theorem source_mem : source19 ∈ c450Segs := by decide +kernel
theorem nn0 : |source19.a1|+|source19.a2|+|source19.a3| ≤ source19.a0 := by decide +kernel
theorem nn1 : |source19.b1|+|source19.b2|+|source19.b3| ≤ source19.b0 := by decide +kernel
theorem eHi_le : source19.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source19Data
#print axioms N11Formalization.C450Source19Data.source_eq
#print axioms N11Formalization.C450Source19Data.nn0
#print axioms N11Formalization.C450Source19Data.nn1
