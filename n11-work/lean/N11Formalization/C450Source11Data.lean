import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11Data
def source11 : TenSeg := ⟨((9:ℚ)/250),((1:ℚ)/25),((2536217:ℚ)/1000000),((-1507:ℚ)/31250),((-6701:ℚ)/250000),((-8123:ℚ)/1000000),((11487:ℚ)/15625),((-144467:ℚ)/500000),((33703:ℚ)/500000),((1141:ℚ)/500000)⟩
theorem source_eq : c450Segs[10]? = some source11 := by decide +kernel
theorem source_mem : source11 ∈ c450Segs := by decide +kernel
theorem nn0 : |source11.a1|+|source11.a2|+|source11.a3| ≤ source11.a0 := by decide +kernel
theorem nn1 : |source11.b1|+|source11.b2|+|source11.b3| ≤ source11.b0 := by decide +kernel
theorem eHi_le : source11.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source11Data
#print axioms N11Formalization.C450Source11Data.source_eq
#print axioms N11Formalization.C450Source11Data.nn0
#print axioms N11Formalization.C450Source11Data.nn1
