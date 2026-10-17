/-
  N11Formalization.Interval.IndexIf
  =================================

  **索引级 `if` 的消除引理**（供 `d-nodes` 的 `hD` 分层使用；本模块**不改动** `Trig.lean`
  或任何既有名字/语义，只新增）。

  背景（对照读数，见 `evidence/interval/_probe_ratdec.out.txt`）：
  * **`Rat`** 写成除法的字面量，其 `Decidable` 在内核**不**归约 ⟹ `by decide` 会失败
    （本工程 DEAD B1）；
  * **`Fin`** 的 `DecidableEq` 是 `Nat` 结构化的 ⟹ **具体索引相等在内核可归约** ✓，
    故 `by decide` / `rw [if_pos …]` / `rw [if_neg …]` 对 `if (3 : Fin 7) = 6 then … else …`
    这类**索引判断**直接可用，不需要任何新机制。

  本文件提供两组可复用的稳定名（跨文件引用用）：
  1. `ite_fin_eq_of_eq` / `ite_fin_eq_of_ne`：把索引 `if` **消成小项**（任意 `Fin n`、任意分支类型）；
  2. `ofRat_ite_fin_of_eq` / `ofRat_ite_fin_of_ne` 及其 `Fin 7`、`i = 6` 的具体形状
     （`drhoIv` 表查 `ofRat (if i = 6 then 1 else 0)`）：直接给出**小项等式**
     `ofRat (if i = 6 then 1 else 0) = ofRat 0`（或 `= ofRat 1`）；
  3. `lo_of_eq` / `hi_of_eq`：把**整区间等式**投影成**端点等式**
     （`h : A = ⟨lo, hi⟩` ⟹ `A.lo = lo`、`A.hi = hi`）——用于把 `read_endpoints_*`
     这类整区间读数接到 `(sq A).lo = …` 形态的目标上。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval`。
-/
import Mathlib
import N11Formalization.Interval.Core

namespace N11Formalization

namespace RatInterval

/-! ## 1. 索引 `if` 的通用消除（任意 `Fin n`） -/

/-- 索引命中：`(if i = m then a else b) = a`。 -/
theorem ite_fin_eq_of_eq {n : ℕ} {α : Type*} (i m : Fin n) (a b : α) (h : i = m) :
    (if i = m then a else b) = a := if_pos h

/-- 索引未命中：`(if i = m then a else b) = b`。 -/
theorem ite_fin_eq_of_ne {n : ℕ} {α : Type*} (i m : Fin n) (a b : α) (h : i ≠ m) :
    (if i = m then a else b) = b := if_neg h

/-! ## 2. `ofRat` 版本（表查形状 `ofRat (if i = 6 then 1 else 0)`） -/

/-- 通用：`ofRat (if i = m then a else b)` 的两条小项等式。 -/
theorem ofRat_ite_fin_of_eq {n : ℕ} (i m : Fin n) (a b : ℚ) (h : i = m) :
    ofRat (if i = m then a else b) = ofRat a := by
  rw [if_pos h]

theorem ofRat_ite_fin_of_ne {n : ℕ} (i m : Fin n) (a b : ℚ) (h : i ≠ m) :
    ofRat (if i = m then a else b) = ofRat b := by
  rw [if_neg h]

/-- `drhoIv` 的 `Fin 7` / `i = 6` 形状（命中）。 -/
theorem ofRat_ite_six_of_eq (i : Fin 7) (h : i = 6) :
    ofRat (if i = 6 then (1 : ℚ) else 0) = ofRat 1 := by
  rw [if_pos h]

/-- `drhoIv` 的 `Fin 7` / `i = 6` 形状（未命中）。 -/
theorem ofRat_ite_six_of_ne (i : Fin 7) (h : i ≠ 6) :
    ofRat (if i = 6 then (1 : ℚ) else 0) = ofRat 0 := by
  rw [if_neg h]

/-- 具体索引一步到位：`i = 3` 时索引判断由 `decide` 消去（`Fin` 可归约）。 -/
theorem ofRat_ite_six_three :
    ofRat (if (3 : Fin 7) = 6 then (1 : ℚ) else 0) = ofRat 0 := by
  rw [if_neg (by decide)]

/-- 具体索引一步到位（命中侧）：`i = 6`。 -/
theorem ofRat_ite_six_six :
    ofRat (if (6 : Fin 7) = 6 then (1 : ℚ) else 0) = ofRat 1 := by
  rw [if_pos (by decide)]

/-! ## 3. 整区间等式 → 端点等式（接 `read_endpoints_*` 用） -/

/-- `A = ⟨lo, hi⟩` ⟹ `A.lo = lo`。 -/
theorem lo_of_eq {A : RatInterval} {lo hi : ℚ} (h : A = ⟨lo, hi⟩) : A.lo = lo :=
  congrArg RatInterval.lo h

/-- `A = ⟨lo, hi⟩` ⟹ `A.hi = hi`。 -/
theorem hi_of_eq {A : RatInterval} {lo hi : ℚ} (h : A = ⟨lo, hi⟩) : A.hi = hi :=
  congrArg RatInterval.hi h

/-- 端点读数的常用形状：整区间等式 + `intv` ⟹ 两端点数值。 -/
theorem intv_eq_endpoints {A : RatInterval} {lo hi : ℚ} (h : A = intv lo hi) :
    A.lo = lo ∧ A.hi = hi :=
  ⟨congrArg RatInterval.lo h, congrArg RatInterval.hi h⟩

end RatInterval

end N11Formalization
