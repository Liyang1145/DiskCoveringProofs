import N11Formalization.FlashLocalFrobeniusSourceNB00
import N11Formalization.NondegProof

/-!
# 源 B[0,0] 对**真实根盒** `ndBox` 的 membership（精确前 7 槽桥）

Lead：`pad12 z` 与原 12 维 root **不**相等（后 5 槽也是未知量），B[0,0] 只依赖前 7 槽，
但必须**显式同余定理**而不是假设 `S.root = pad12`。

* `srcQ7 : Fin 7 → RatInterval` = `ndBox` 的前 7 槽（**不是更宽盒**；`pad12Box` 后 5 槽是单点 0，
  与 `ndBox` 的后 5 槽证书盒不同，本件只用前 7 槽）；
* `srcB00Box_mem_rootbox`：`u` 逐槽 ∈ `ndBox` ⇒ `(srcB00Box srcQ7).Mem (srcB u 0 0)`；
  其中 `z := first7 u`、`pad12 (first7 u)` 与 `u` 在前 7 槽一致 ⇒ `angleVec/thetaOf/rhoK`
  逐一定理相等（`pad12_apply_lt` + `funext` + `fin_cases`），**不**断言 12 维相等。
-/

namespace N11Formalization

noncomputable section

open RatInterval
open N11Formalization.TowerBC

/-- 根盒前 7 槽（`Q` 口径与 `pad12Box` 一致：前 7 槽照抄）。 -/
def srcQ7 : Fin 7 → RatInterval := fun i => ndBox ⟨(i : ℕ), by omega⟩

/-- **前 7 槽同余**：`u` 与 `pad12 (first7 u)` 的 `angleVec` 相等。 -/
theorem angleVec_pad12_first7 (u : Fin 12 → ℝ) :
    angleVec (pad12 (fun i : Fin 7 => u ⟨(i : ℕ), by omega⟩)) = angleVec u := by
  funext k
  fin_cases k <;> simp [angleVec, pad12]

/-- **前 7 槽同余**：`θ` 相等。 -/
theorem thetaOf_pad12_first7 (u : Fin 12 → ℝ) :
    thetaOf (angleVec (pad12 (fun i : Fin 7 => u ⟨(i : ℕ), by omega⟩)))
      = thetaOf (angleVec u) := by
  rw [angleVec_pad12_first7]

/-- **前 7 槽同余**：`u 6 = pad12 (first7 u) 6`。 -/
theorem pad12_first7_six (u : Fin 12 → ℝ) :
    pad12 (fun i : Fin 7 => u ⟨(i : ℕ), by omega⟩) 6 = u 6 := by
  rw [pad12_apply_lt _ 6 (by norm_num)]

/-- `ρ_0` 前 7 槽同余。 -/
theorem rhoK_pad12_first7 (u : Fin 12 → ℝ) :
    rhoK (pad12 (fun i : Fin 7 => u ⟨(i : ℕ), by omega⟩)) 0 = rhoK u 0 := by
  simp only [rhoK, angleVec_pad12_first7, pad12_first7_six]

/-- `ringCenter 0` 前 7 槽同余（点相等）。 -/
theorem ringCenter_pad12_first7 (u : Fin 12 → ℝ) :
    ringCenter (pad12 (fun i : Fin 7 => u ⟨(i : ℕ), by omega⟩)) 0 = ringCenter u 0 := by
  simp only [ringCenter, rhoK_pad12_first7, thetaOf_pad12_first7, angleVec_pad12_first7]

/-- `arcEnd 0` 前 7 槽同余（点相等）。 -/
theorem arcEnd_pad12_first7 (u : Fin 12 → ℝ) :
    arcEnd (pad12 (fun i : Fin 7 => u ⟨(i : ℕ), by omega⟩)) 0 = arcEnd u 0 := by
  simp only [arcEnd, thetaOf_pad12_first7, angleVec_pad12_first7]

/-- **B[0,0] 前 7 槽同余**：`srcB (pad12 (first7 u)) 0 0 = srcB u 0 0`（显式定理）。 -/
theorem srcB00_pad12_first7 (u : Fin 12 → ℝ) :
    srcB (pad12 (fun i : Fin 7 => u ⟨(i : ℕ), by omega⟩)) 0 0 = srcB u 0 0 := by
  rw [srcB_00, srcB_00, ringCenter_pad12_first7, arcEnd_pad12_first7]

/-- **B[0,0] 真实根盒 membership**：`u ∈ ndBox`（逐槽）⇒ `(srcB00Box srcQ7).Mem (srcB u 0 0)`。 -/
theorem srcB00Box_mem_rootbox (u : Fin 12 → ℝ) (hu : ∀ i, (ndBox i).Mem (u i)) :
    (srcB00Box srcQ7).Mem (srcB u 0 0) := by
  have hz : ∀ i : Fin 7, (srcQ7 i).Mem (u ⟨(i : ℕ), by omega⟩) :=
    fun i => hu ⟨(i : ℕ), by omega⟩
  have hmem := srcB00Box_mem (Q := srcQ7) hz
  rwa [srcB00_pad12_first7] at hmem

end

end N11Formalization

#print axioms N11Formalization.srcB00_pad12_first7
#print axioms N11Formalization.srcB00Box_mem_rootbox
#check @N11Formalization.srcB00Box_mem_rootbox
