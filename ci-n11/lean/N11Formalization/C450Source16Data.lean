import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16Data
def source16 : TenSeg := ⟨((7:ℚ)/125),((3:ℚ)/50),((2516033:ℚ)/1000000),((-82023:ℚ)/1000000),((-6163:ℚ)/125000),((-221:ℚ)/12500),((79807:ℚ)/100000),((-44739:ℚ)/100000),((29563:ℚ)/200000),((-4237:ℚ)/1000000)⟩
theorem source_eq : c450Segs[15]? = some source16 := by decide +kernel
theorem source_mem : source16 ∈ c450Segs := by decide +kernel
theorem nn0 : |source16.a1|+|source16.a2|+|source16.a3| ≤ source16.a0 := by decide +kernel
theorem nn1 : |source16.b1|+|source16.b2|+|source16.b3| ≤ source16.b0 := by decide +kernel
theorem eHi_le : source16.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source16Data
#print axioms N11Formalization.C450Source16Data.source_eq
#print axioms N11Formalization.C450Source16Data.nn0
#print axioms N11Formalization.C450Source16Data.nn1
