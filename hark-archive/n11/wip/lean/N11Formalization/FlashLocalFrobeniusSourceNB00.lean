import N11Formalization.FlashLocalFrobeniusSourceN
import N11Formalization.TowerBC_N_anyx_layer1

/-!
# 源 B[0,0] 的实际 membership（从根盒出发，非 numeric 中点）

`B[0,0] = ρ_0 cos θ_0 − cos(θ_0+a_0)`（`srcB_00`）；本件对它给出**真实区间包含**：

* `srcB00Box Q`：用 `pad12Box Q`（7 槽盒 ⇒ 12 槽盒）组装
  `cosTotLag`/`sinTotLag`/`thetaInterval`/`sq`/`sub`/`mul`/`sqrt` 的 RatInterval 表达式；
* `srcB00Box_mem`：`z ∈ Q` 逐槽 ⇒ `(srcB00Box Q).Mem (srcB (pad12 z) 0 0)`。

链：`pad12Box_mem_pad12` → `ndAngleBox_mem` → `thetaInterval_mem`/`cosTotLag_mem`/`sinTotLag_mem`
→ `sq_mem_pow`/`sub_mem`/`sqrt_mem`/`mul_mem`/`sub_mem` → `srcB_00` 的 `rfl` 级坐标展开。
**盒口径**：`pad12Box` 只把前 7 槽照抄（`Q` 必须取自根盒前 7 槽；12 槽 `ndBox` 的后 5 槽是
证书尺度盒、不含 0，故 `pad12Box`/`ndBox` **不可**互当更宽盒使用——精确桥归 `hess-seam`）。
-/

namespace N11Formalization

noncomputable section

open RatInterval
open N11Formalization.TowerBC

/-- `B[0,0]` 的区间盒（`Q 6 = R`，角 = `ndAngleBox (pad12Box Q)`）。 -/
def srcB00Box (Q : Fin 7 → RatInterval) : RatInterval :=
  let A : Fin 9 → RatInterval := ndAngleBox (pad12Box Q)
  let rhoBox : RatInterval := sub (cosTotLag (A 0))
    ((sub (sq (pad12Box Q 6)) (sq (sinTotLag (A 0)))).sqrt)
  sub (mul rhoBox (cosTotLag (thetaInterval A 0)))
    (cosTotLag (add (thetaInterval A 0) (A 0)))

/-- **B[0,0] 实际 membership**：`z ∈ Q`（`Q : Fin 7` 盒）⇒
`srcB00Box Q ∋ srcB (pad12 z) 0 0 = (ringCenter − arcEnd)₀`。 -/
theorem srcB00Box_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) :
    (srcB00Box Q).Mem (srcB (pad12 z) 0 0) := by
  have hz12 : ∀ i : Fin 12, (pad12Box Q i).Mem (pad12 z i) := pad12Box_mem_pad12 hz
  have hA : ∀ j : Fin 9, (ndAngleBox (pad12Box Q) j).Mem (angleVec (pad12 z) j) :=
    fun j => ndAngleBox_mem hz12 j
  have hcos0 : (cosTotLag (ndAngleBox (pad12Box Q) 0)).Mem
      (Real.cos (angleVec (pad12 z) 0)) :=
    cosTotLag_mem (hA 0)
  have hsin0 : (sinTotLag (ndAngleBox (pad12Box Q) 0)).Mem
      (Real.sin (angleVec (pad12 z) 0)) :=
    sinTotLag_mem (hA 0)
  have hR : (pad12Box Q 6).Mem (pad12 z 6) := hz12 6
  have hρ : (sub (cosTotLag (ndAngleBox (pad12Box Q) 0))
      ((sub (sq (pad12Box Q 6)) (sq (sinTotLag (ndAngleBox (pad12Box Q) 0)))).sqrt)).Mem
      (rhoK (pad12 z) 0) :=
    sub_mem hcos0 (sqrt_mem (sub_mem (sq_mem_pow hR) (sq_mem_pow hsin0)))
  have hcosTA : (cosTotLag (add (thetaInterval (ndAngleBox (pad12Box Q)) 0)
      (ndAngleBox (pad12Box Q) 0))).Mem
      (Real.cos (thetaOf (angleVec (pad12 z)) 0 + angleVec (pad12 z) 0)) :=
    cosTotLag_theta_add_angle_mem 0 hz
  have hmain : (sub (mul (sub (cosTotLag (ndAngleBox (pad12Box Q) 0))
        ((sub (sq (pad12Box Q 6)) (sq (sinTotLag (ndAngleBox (pad12Box Q) 0)))).sqrt))
        (cosTotLag (thetaInterval (ndAngleBox (pad12Box Q)) 0)))
      (cosTotLag (add (thetaInterval (ndAngleBox (pad12Box Q)) 0)
        (ndAngleBox (pad12Box Q) 0)))).Mem
      (rhoK (pad12 z) 0 * Real.cos (thetaOf (angleVec (pad12 z)) 0)
        - Real.cos (thetaOf (angleVec (pad12 z)) 0 + angleVec (pad12 z) 0)) :=
    sub_mem (mul_mem hρ (cosTotLag_mem (thetaInterval_mem hA 0))) hcosTA
  have hring : (ringCenter (pad12 z) 0).ofLp 0
      = rhoK (pad12 z) 0 * Real.cos (thetaOf (angleVec (pad12 z)) 0) := rfl
  have harc : (arcEnd (pad12 z) 0).ofLp 0
      = Real.cos (thetaOf (angleVec (pad12 z)) 0 + angleVec (pad12 z) 0) := rfl
  rw [srcB_00, hring, harc]
  exact hmain

end

end N11Formalization

#print axioms N11Formalization.srcB00Box_mem
#check @N11Formalization.srcB00Box_mem
