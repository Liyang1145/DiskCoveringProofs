import N11Formalization.ResidualInterval

/-! 探针 7：**分层读数配方**（生成器要用的每个模式先小样验证） -/

namespace N11Formalization

open RatInterval

-- (0) 结构字面量的场投影与 ext
example : (⟨(1 / 2 : ℚ), (3 / 4 : ℚ)⟩ : RatInterval).lo = 1 / 2 := rfl

example : (neg (add (⟨(1 / 2 : ℚ), (3 / 4 : ℚ)⟩ : RatInterval)
    (⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩ : RatInterval))) = ⟨-(1 / 4), -(3 / 4)⟩ := by
  simp only [RatInterval.neg, RatInterval.add]
  ext <;> norm_num

-- (1) sqrt 值引理
example : sqrt (⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩ : RatInterval) = ⟨1 / 2, 3 / 4⟩ := by
  simp only [RatInterval.sqrt, sqrtLo, sqrtHi]
  ext <;> norm_num

-- (2) sq 值引理（正盒支）
example : sq (⟨(1 / 4 : ℚ), (1 / 2 : ℚ)⟩ : RatInterval) = ⟨1 / 16, 1 / 4⟩ := by
  rw [sq, if_pos (by norm_num : (0 : ℚ) ≤ 1 / 4)]
  ext <;> norm_num

-- (3) sinI / cosWin 值引理
example : sinI (⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩ : RatInterval) = ⟨sinLo (1 / 4), sinHi (1 / 4)⟩ := by
  rw [sinI, if_pos (by norm_num : (-1 : ℚ) ≤ 1 / 4 ∧ (1 / 4 : ℚ) ≤ 1)]

example : cosWin (⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩ : RatInterval)
    = ⟨cosLo (highAbs (⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩ : RatInterval)),
       cosHi (lowAbs (⟨(1 / 4 : ℚ), (1 / 4 : ℚ)⟩ : RatInterval))⟩ := by
  rw [cosWin, if_pos (by norm_num : (-1 : ℚ) ≤ 1 / 4 ∧ (1 / 4 : ℚ) ≤ 1)]

-- (4) 三角节点（相位 0）：`cosTot (angleVecInterval cCert 0)`
example : cosTot (angleVecInterval cCert 0)
    = ⟨9400333188822605251816370421980311697855720512820413282357377343483
        / 10109980000181489923000130657632361502613929158452714680413853843456,
       94220502500460499143076985022209948043368249587081666300293096562693
        / 10109980000181489923000130657632361502613929158452714680413853843456⟩ := by
  have hg : inWindow (angleVecInterval cCert 0) (phaseOf (angleVecInterval cCert 0)) := by
    rw [show angleVecInterval cCert 0 = ofRat (cCert 0) from rfl, ofRat, cCert,
      Matrix.cons_val_zero]
    simp only [inWindow, phaseOf, halfPiLo, halfPiHi, piLo, piHi]
    norm_num
  rw [cosTot_of_inWindow hg, phaseRed, phaseBoth]
  rw [if_pos (by
    rw [show angleVecInterval cCert 0 = ofRat (cCert 0) from rfl, ofRat, cCert,
      Matrix.cons_val_zero]
    simp only [reducedBox, phaseOf, halfPiLo, halfPiHi, piLo, piHi]
    norm_num)]
  simp only [phasePos]
  rw [cosWin]
  rw [if_pos (by
    rw [show angleVecInterval cCert 0 = ofRat (cCert 0) from rfl, ofRat, cCert,
      Matrix.cons_val_zero]
    norm_num)]
  simp only [highAbs, lowAbs, RatInterval.neg]
  rw [show angleVecInterval cCert 0 = ofRat (cCert 0) from rfl, ofRat, cCert,
    Matrix.cons_val_zero]
  simp only [cosLo, cosHi]
  norm_num

end N11Formalization
