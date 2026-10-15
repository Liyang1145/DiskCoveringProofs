import N11Formalization.SourceLoop

noncomputable section
namespace N11Formalization

open Real

/-- (A) `aFun BReal (sOf u) = angleVec u`（函数相等，便于 `rw`）。 -/
theorem aFun_sOf_eq_angleVec (u : Fin 12 → ℝ) :
    aFun BReal (sOf u) = angleVec u := by
  funext j
  fin_cases j <;> simp [aFun, aList, angleVec, a4Of, sOf, BReal]

/-- (B) `rhoLoop BReal (sOf u) = rhoK u`（函数相等）。 -/
theorem rhoLoop_sOf_eq_rhoK (u : Fin 12 → ℝ) :
    rhoLoop BReal (sOf u) = rhoK u := by
  funext j
  simp only [rhoLoop, rhoEntry, rhoK]
  rw [aFun_sOf_eq_angleVec]
  congr 2 <;> (simp only [sOf, BReal]; ring)

/-- (C) 坐标 0 的桥：`(Uvec u k).ofLp 0 = proj (ULoop BReal (sOf u) k) 0`。 -/
theorem Uvec_coord0_eq_proj (u : Fin 12 → ℝ) (k : Fin 9) :
    (Uvec u k).ofLp 0 = proj (ULoop BReal (sOf u) k) 0 := by
  rw [Uvec_coord0, ringCenter_coord0, ringCenter_coord0, arcEnd_coord0]
  rw [ULoop, CLoop_val, CLoop_val]
  simp only [proj, mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one, k2Of_eq_fin,
    thetaLoop_eq_thetaOf, rhoLoop_sOf_eq_rhoK, aFun_sOf_eq_angleVec, BReal]

/-- (D) 坐标 1 的桥：`(Uvec u k).ofLp 1 = proj (ULoop BReal (sOf u) k) 1`。 -/
theorem Uvec_coord1_eq_proj (u : Fin 12 → ℝ) (k : Fin 9) :
    (Uvec u k).ofLp 1 = proj (ULoop BReal (sOf u) k) 1 := by
  rw [Uvec_coord1, ringCenter_coord1, ringCenter_coord1, arcEnd_coord1]
  rw [ULoop, CLoop_val, CLoop_val]
  simp only [proj, mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one, k2Of_eq_fin,
    thetaLoop_eq_thetaOf, rhoLoop_sOf_eq_rhoK, aFun_sOf_eq_angleVec, BReal]

end N11Formalization
