import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhData
def seventh : TenSeg := ⟨((1:ℚ)/50),((3:ℚ)/125),((638997:ℚ)/250000),((-3923:ℚ)/250000),((-913:ℚ)/100000),((-1523:ℚ)/500000),((694981:ℚ)/1000000),((-88593:ℚ)/500000),((22417:ℚ)/1000000),((253:ℚ)/125000)⟩
theorem source_eq : c450Segs[6]? = some seventh := by decide +kernel
theorem source_mem : seventh ∈ c450Segs := by decide +kernel
theorem nn0 : |seventh.a1|+|seventh.a2|+|seventh.a3| ≤ seventh.a0 := by decide +kernel
theorem nn1 : |seventh.b1|+|seventh.b2|+|seventh.b3| ≤ seventh.b0 := by decide +kernel
theorem eHi_le : seventh.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.C450SeventhData
#print axioms N11Formalization.C450SeventhData.source_eq
#print axioms N11Formalization.C450SeventhData.nn0
#print axioms N11Formalization.C450SeventhData.nn1
