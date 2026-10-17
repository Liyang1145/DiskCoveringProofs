import N11Formalization.C921Sem
import N11Formalization.BoxRstar

/-! The initial C891 box does NOT imply the finer C922 threshold pin.
This is an exact diagnostic, not a disproof of Rstar < T. -/
namespace N11Formalization.ResumeThreshold
open N11Formalization.C921Sem N11Formalization.G3ArcConstants

 theorem threshold_lt_initial_box_hi : threshR < (boxHiCert 6 : ℝ) := by
  have hhi : boxHiCert 6 = 1837489169128606637938325 / 2 ^ 82 := rfl
  rw [hhi]
  norm_num [threshR, thresh]

 theorem initial_box_pin_impossible : ¬ ((boxHiCert 6 : ℝ) ≤ threshR) :=
  not_le_of_gt threshold_lt_initial_box_hi

/-- The upper endpoint recorded by exact_root_threshold.json; root inclusion is a
separate obligation and is deliberately NOT inferred from this rational check. -/
def contractedRadiusHi : ℚ :=
  41960834721747981615784295073567334841668387037962545903051432423660093 /
  110427941548649020598956093796432407239217743554726184882600387580788736

theorem contractedRadiusHi_lt_threshold : (contractedRadiusHi : ℝ) < threshR := by
  norm_num [contractedRadiusHi, threshR, thresh]

theorem root_lt_threshold_of_contracted_inclusion (S : C891RootSpec)
    (hinc : Rstar S ≤ (contractedRadiusHi : ℝ)) : Rstar S < threshR :=
  hinc.trans_lt contractedRadiusHi_lt_threshold

#print axioms threshold_lt_initial_box_hi
#print axioms contractedRadiusHi_lt_threshold
#print root_lt_threshold_of_contracted_inclusion
#print axioms root_lt_threshold_of_contracted_inclusion
end N11Formalization.ResumeThreshold
