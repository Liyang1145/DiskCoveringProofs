import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthData
def ninth : TenSeg := ⟨((7:ℚ)/250),((4:ℚ)/125),((2546909:ℚ)/1000000),((-1923:ℚ)/62500),((-9061:ℚ)/500000),((-6211:ℚ)/1000000),((356397:ℚ)/500000),((-233439:ℚ)/1000000),((4319:ℚ)/100000),((3449:ℚ)/1000000)⟩
theorem source_eq : c450Segs[8]? = some ninth := by decide +kernel
theorem source_mem : ninth ∈ c450Segs := by decide +kernel
theorem nn0 : |ninth.a1|+|ninth.a2|+|ninth.a3| ≤ ninth.a0 := by decide +kernel
theorem nn1 : |ninth.b1|+|ninth.b2|+|ninth.b3| ≤ ninth.b0 := by decide +kernel
theorem eHi_le : ninth.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450NinthData
#print axioms N11Formalization.C450NinthData.source_eq
#print axioms N11Formalization.C450NinthData.nn0
#print axioms N11Formalization.C450NinthData.nn1
