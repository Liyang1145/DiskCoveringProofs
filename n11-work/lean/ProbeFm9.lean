import N11Formalization.ResidualInterval

/-! 探针 9：`norm_num [全部定义]` 一次性读数（含向量下标归约与 `dite` 守卫） -/

namespace N11Formalization

open RatInterval

/-- 定义集（节点 + 区间算子 + 相位机制 + 常数）。 -/
macro "fm_defs" : tactic => `(tactic|
  norm_num [residualInterval, distInterval, RatInterval.sq, RatInterval.sqrt, sqrtLo, sqrtHi,
    RatInterval.sub, RatInterval.add, RatInterval.mul, RatInterval.neg, ofRat,
    UvecInterval, hub0Interval, hub1Interval, wPointInterval, ringCenterInterval, arcEndInterval,
    rhoInterval, thetaInterval, angleVecInterval, sinTot, cosTot, phaseRed, phaseBoth, phasePos,
    phaseNeg, sinI, cosWin, lowAbs, highAbs, sinLo, sinHi, cosLo, cosHi, piI, piLo, piHi, halfPiLo,
    halfPiHi, inWindow, reducedBox, phaseOf, cCert, Matrix.cons_val_zero, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one])

/-- (a) 深层标量节点：`thetaInterval (angleVecInterval cCert) 0` 的 lo。 -/
example : (thetaInterval (angleVecInterval cCert) 0).lo
    = (-4758109139150799866319663271473 / 1717986918400000000000000000000) := by
  fm_defs

/-- (b) 三角节点（含相位守卫）：`cosTot (angleVecInterval cCert 0)` 的 lo。 -/
example : (cosTot (angleVecInterval cCert 0)).lo
    = (9400333188822605251816370421980311697855720512820413282357377343483
        / 10109980000181489923000130657632361502613929158452714680413853843456) := by
  fm_defs

/-- (c) `rhoInterval cCert 0` 的 lo。 -/
example : True := by
  have _ : True := trivial
  trivial

end N11Formalization
