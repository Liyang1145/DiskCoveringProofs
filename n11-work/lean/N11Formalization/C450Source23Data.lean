import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23Data
def source23 : TenSeg := ⟨((21:ℚ)/250),((11:ℚ)/125),((2402767:ℚ)/1000000),((-53503:ℚ)/200000),((-4563:ℚ)/31250),((-10659:ℚ)/250000),((995657:ℚ)/1000000),((-600839:ℚ)/1000000),((174061:ℚ)/500000),((-5837:ℚ)/125000)⟩
theorem source_eq : c450Segs[22]? = some source23 := by decide +kernel
theorem source_mem : source23 ∈ c450Segs := by decide +kernel
theorem nn0 : |source23.a1|+|source23.a2|+|source23.a3| ≤ source23.a0 := by decide +kernel
theorem nn1 : |source23.b1|+|source23.b2|+|source23.b3| ≤ source23.b0 := by decide +kernel
theorem eHi_le : source23.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source23Data
#print axioms N11Formalization.C450Source23Data.source_eq
#print axioms N11Formalization.C450Source23Data.nn0
#print axioms N11Formalization.C450Source23Data.nn1
