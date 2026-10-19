import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthData
def eighth : TenSeg := ⟨((3:ℚ)/125),((7:ℚ)/250),((319043:ℚ)/125000),((-1083:ℚ)/50000),((-12181:ℚ)/1000000),((-3781:ℚ)/1000000),((702603:ℚ)/1000000),((-517:ℚ)/2500),((7717:ℚ)/250000),((2069:ℚ)/1000000)⟩
theorem source_eq : c450Segs[7]? = some eighth := by decide +kernel
theorem source_mem : eighth ∈ c450Segs := by decide +kernel
theorem nn0 : |eighth.a1|+|eighth.a2|+|eighth.a3| ≤ eighth.a0 := by decide +kernel
theorem nn1 : |eighth.b1|+|eighth.b2|+|eighth.b3| ≤ eighth.b0 := by decide +kernel
theorem eHi_le : eighth.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450EighthData
#print axioms N11Formalization.C450EighthData.source_eq
#print axioms N11Formalization.C450EighthData.nn0
#print axioms N11Formalization.C450EighthData.nn1
