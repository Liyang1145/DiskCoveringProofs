import N11Formalization.ResidualInterval

/-!
# 探针 5：分层**精确端点读数**可行性（决定交付 5 的路线）

试三件事：
 (a) `cCert i` 的分量读数（`rfl`）；
 (b) `angleVecInterval cCert 4` 的端点（`π` 区间 + 有理算术）；
 (c) `thetaInterval (angleVecInterval cCert) 0` 的端点；
 (d) 一个三角节点 `cosTot (angleVecInterval cCert 0)` 的端点（含相位守卫）。
-/

namespace N11Formalization

open RatInterval

example : cCert 0 = 6701511529285631 / 18014398509481984 := rfl
example : cCert 6 = 6845180557269243 / 18014398509481984 := rfl

/-- (b) `angleVecInterval cCert 4` 的显式形状（`rfl`）。 -/
example : angleVecInterval cCert 4
    = sub piI (mul (ofRat 2) (add (add (add (ofRat (cCert 0)) (ofRat (cCert 1)))
        (ofRat (cCert 2))) (ofRat (cCert 3)))) := rfl

/-- (b) 端点读数（Python 镜像给的精确值）。 -/
example : (angleVecInterval cCert 4).lo
    = 83369910322970511985777954583 / 214748364800000000000000000000 := by
  rw [show angleVecInterval cCert 4
    = sub piI (mul (ofRat 2) (add (add (add (ofRat (cCert 0)) (ofRat (cCert 1)))
        (ofRat (cCert 2))) (ofRat (cCert 3)))) from rfl]
  simp only [piI, piLo, piHi, cCert, sub, mul, add, ofRat,
    Matrix.cons_val_zero, Matrix.cons_val_succ', Matrix.cons_val_fin_one]
  norm_num

end N11Formalization
