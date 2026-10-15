import N11Formalization.ResidualInterval

/-! 探针 8：分层配方（v2：标量 lo/hi 引理 + 命名守卫引理） -/

namespace N11Formalization

open RatInterval

-- (1) `sq` 的展开（三种变体）
example : (sq (⟨(1 / 4 : ℚ), (1 / 2 : ℚ)⟩ : RatInterval)).lo = 1 / 16 := by
  simp only [RatInterval.sq]
  rw [if_pos (by norm_num : (0 : ℚ) ≤ 1 / 4)]
  norm_num

example : (sq (⟨(1 / 4 : ℚ), (1 / 2 : ℚ)⟩ : RatInterval)).hi = 1 / 4 := by
  have h : (0 : ℚ) ≤ (1 / 4 : ℚ) := by norm_num
  rw [sq, if_pos h]
  norm_num

example : (sq (⟨(-1 / 2 : ℚ), (-1 / 4 : ℚ)⟩ : RatInterval)).lo = 1 / 16 := by
  rw [sq, if_neg (by norm_num : ¬ ((0 : ℚ) ≤ -1 / 2))]
  rw [if_pos (by norm_num : (-1 / 4 : ℚ) ≤ 0)]
  norm_num

-- (2) `phaseOf` 值引理（命名）
theorem aI_0 : angleVecInterval cCert 0 = ofRat (cCert 0) := rfl

theorem cCert_0 : cCert 0 = 6701511529285631 / 18014398509481984 := rfl

theorem phaseOf_a0 : phaseOf (angleVecInterval cCert 0) = 0 := by
  rw [aI_0, ofRat, cCert_0]
  simp only [phaseOf, halfPiLo, piLo]
  norm_num

theorem phaseOf_a0' : phaseOf (ofRat (6701511529285631 / 18014398509481984)) = 0 := by
  simp only [phaseOf, ofRat, halfPiLo, piLo]
  norm_num

-- (3) `reducedBox` 值引理
theorem red_a0 : reducedBox (angleVecInterval cCert 0) (phaseOf (angleVecInterval cCert 0))
    = reducedBox (ofRat (6701511529285631 / 18014398509481984)) 0 := by
  rw [aI_0, ofRat, cCert_0, phaseOf_a0]

-- (4) 三角节点 v2：命名守卫 + 展开
theorem inw_a0 : inWindow (ofRat (6701511529285631 / 18014398509481984)) 0 := by
  simp only [inWindow, ofRat, halfPiLo, halfPiHi, piLo, piHi]
  norm_num

theorem cosWin_a0 : cosWin (ofRat (6701511529285631 / 18014398509481984))
    = ⟨cosLo (highAbs (ofRat (6701511529285631 / 18014398509481984))),
       cosHi (lowAbs (ofRat (6701511529285631 / 18014398509481984)))⟩ := by
  rw [cosWin, if_pos (by
    simp only [ofRat]
    norm_num : (-1 : ℚ) ≤ (ofRat (6701511529285631 / 18014398509481984)).lo ∧
      (ofRat (6701511529285631 / 18014398509481984)).hi ≤ 1)]

theorem cosTot_a0_v : cosTot (ofRat (6701511529285631 / 18014398509481984))
    = ⟨9400333188822605251816370421980311697855720512820413282357377343483
        / 10109980000181489923000130657632361502613929158452714680413853843456,
       94220502500460499143076985022209948043368249587081666300293096562693
        / 10109980000181489923000130657632361502613929158452714680413853843456⟩ := by
  rw [cosTot_of_inWindow (A := ofRat (6701511529285631 / 18014398509481984)) (by
    simp only [inWindow, ofRat, halfPiLo, halfPiHi, piLo, piHi]
    norm_num)]
  rw [phaseRed, phaseBoth]
  rw [if_pos (by simp only [phaseOf, reducedBox, ofRat, halfPiLo, piLo]; norm_num)]
  simp only [phasePos]
  rw [cosWin]
  rw [if_pos (by simp only [ofRat]; norm_num : (-1 : ℚ) ≤
      (ofRat (6701511529285631 / 18014398509481984)).lo ∧
      (ofRat (6701511529285631 / 18014398509481984)).hi ≤ 1)]
  simp only [highAbs, lowAbs, ofRat]
  simp only [cosLo, cosHi]
  norm_num

end N11Formalization
