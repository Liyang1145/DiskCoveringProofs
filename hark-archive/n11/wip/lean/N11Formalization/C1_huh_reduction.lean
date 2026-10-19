/-
# T2 交付件 C1：`hUh` 阻断点的**形式化归约**（C 诊断的判据骨架）

**内容**：把任务书说的「`hUh` 与锥内 `DeltaAny.hasFDerivAt_fderiv_UvecC0_any` 在
`HasFDerivAt.unique` 下冲突」证成**一条定理**（零新前提、零计算）：

* `clm_zero_of_huh`：**由锥内具名件 ＋ `HasFDerivAt.unique`**，
  `hUh` 形状（右端 `0`）⇒ `L2UvecC0At z (resSlot k) = 0`；

**推论（写进报告）**：`hUh` 的开销 = **证 `L2UvecC0At z (resSlot k) = 0`**（等价），
而该 CLM 由 `DeltaAny` L260–266 是
`(L2RingC0At z (resSlot k) + L2RingC0At z (resSlot k+1)) − L2ArcAt z (resSlot k) 0`
—— 三个**非零具名块**的和 ⇒ 这是**非退化要求**（与 `STATUS.md` C1382 判读一致）。
本件**只证归约**，不证「该 CLM 非零」（见报告 ⑤：非零**未定名/未核**）。

口径：无 `sorry`/`admit`/自定义 `axiom`/`native_decide`；本件是**朴素件**（含 `#print axioms` 另置）。
-/
import N11Formalization.DeltaAny
import N11Formalization.D2IvBoxMem

open N11Formalization

namespace StarclassC1

/-- `hUh` 的**字面形状**（= `D2IvBoxMem.d2xIvBox_mem` 的 binder L436–437）。 -/
abbrev HUh (z : Fin 7 → ℝ) (k : Fin 5) : Prop :=
  HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
      (Uvec (pad12 x) (resSlot k)).ofLp 0) x)
    (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z

/-- **本件重点**：锥内 `DeltaAny.hasFDerivAt_fderiv_UvecC0_any` 给出
`HasFDerivAt … (L2UvecC0At z (resSlot k)) z`；与 `hUh` 的 `… (0) z` 在
`HasFDerivAt.unique` 下 ⇒ `L2UvecC0At z (resSlot k) = 0`。 -/
theorem clm_zero_of_huh {z : Fin 7 → ℝ} {k : Fin 5} (hW0 : 0 < Wfun (resSlot k) z)
    (hW1 : 0 < Wfun (resSlot k + 1) z) (h : HUh z k) :
    DeltaAny.L2UvecC0At z (resSlot k) = 0 :=
  (DeltaAny.hasFDerivAt_fderiv_UvecC0_any (resSlot k) z hW0 hW1).unique h

/-- **等价的逆否形式（本件推荐的读法）**：`L2UvecC0At ≠ 0` ⇒ `hUh` **假**。 -/
theorem not_huh_of_clm_ne_zero {z : Fin 7 → ℝ} {k : Fin 5} (hW0 : 0 < Wfun (resSlot k) z)
    (hW1 : 0 < Wfun (resSlot k + 1) z)
    (hne : DeltaAny.L2UvecC0At z (resSlot k) ≠ 0) : ¬ HUh z k :=
  fun h => hne (clm_zero_of_huh hW0 hW1 h)

/-- **y 侧同款**（`c = 1`，用 `L2UvecC1At`）。 -/
abbrev HUhY (z : Fin 7 → ℝ) (k : Fin 5) : Prop :=
  HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
      (Uvec (pad12 x) (resSlot k)).ofLp 1) x)
    (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z

theorem clm_zero_of_huhY {z : Fin 7 → ℝ} {k : Fin 5} (hW0 : 0 < Wfun (resSlot k) z)
    (hW1 : 0 < Wfun (resSlot k + 1) z) (h : HUhY z k) :
    DeltaAny.L2UvecC1At z (resSlot k) = 0 :=
  (DeltaAny.hasFDerivAt_fderiv_UvecC1_any (resSlot k) z hW0 hW1).unique h

end StarclassC1
