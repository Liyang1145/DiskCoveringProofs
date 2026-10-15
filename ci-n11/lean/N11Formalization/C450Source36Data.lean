import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36Data
def source36 : TenSeg := ⟨((17:ℚ)/125),((7:ℚ)/50),((26531:ℚ)/12500),((-49061:ℚ)/100000),((28973:ℚ)/500000),((59453:ℚ)/500000),((640343:ℚ)/500000),((-856119:ℚ)/1000000),((291739:ℚ)/1000000),((-33207:ℚ)/250000)⟩
theorem source_eq : c450Segs[35]? = some source36 := by decide +kernel
theorem source_mem : source36 ∈ c450Segs := by decide +kernel
theorem nn0 : |source36.a1|+|source36.a2|+|source36.a3| ≤ source36.a0 := by decide +kernel
theorem nn1 : |source36.b1|+|source36.b2|+|source36.b3| ≤ source36.b0 := by decide +kernel
theorem eHi_le : source36.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450Source36Data
#print axioms N11Formalization.C450Source36Data.source_eq
#print axioms N11Formalization.C450Source36Data.nn0
#print axioms N11Formalization.C450Source36Data.nn1
