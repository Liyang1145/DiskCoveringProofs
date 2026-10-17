import N11Formalization.Statement
import N11Formalization.Certificates.RootBox

/-!
# **条件模块**：C891 根规格与未形式化的承重义务（GUIDE §6）

> GUIDE §6：「暂时假设可以用于开发，但必须隔离在 Conditional 模块并在账本列全。」

本文件把**唯一**未形式化的承重前提写成显式的 `Prop`/结构字段，绝不写成 `axiom`、
也不藏进 typeclass 参数。当前账本（见 `TRUST.md`）：

| 义务 | 负责的源结论 | 状态 |
|---|---|---|
| `C891RootSpec.exists_unique`：12 变量 TC/KKT 系统在有理盒内**存在唯一根** | C891 | **未形式化**（本文件作为显式前提） |
| 根落在证书包络内（Krawczyk 包含 `K(X) ⊆ X`） | C891 | **未形式化**（见 `Rstar_lt_R0_via_cert` 的前提） |
| `∃ c, Covers c (Rstar ·)` | C892 | **未形式化** |
| `∀ r c, 0 ≤ r → Covers c r → Rstar ≤ r` | C923 + C921 + C922 | **未形式化** |

**已** 形式化的部分见 `Definitions/Reduction/Statement/HexFloat/Certificates.RootBox`：
对象定义、强接口 ↔ `IsLeast` ↔ `sInf` 等价、`sInf` 前置（非空/下有界）、
十六进制字面量→精确有理数的可核验语义、证书 checker 的 soundness 与具体实例通过。

**不** 允许把本文件的结论当成"主定理已证"：本文件的主定理结论**带有显式前提**。
-/

namespace N11Formalization

/-- C891 的根规格：给定 12 变量系统 `sys` 与有理坐标盒 `[boxLo, boxHi]`，
**前提**是盒内存在唯一根。`radiusIndex` 指出 `R*` 是哪个坐标（源：零基第 6 坐标）。 -/
structure C891RootSpec where
  /-- 12 变量 TC/KKT 系统（其显式解析表达式尚未形式化）。 -/
  sys : (Fin 12 → ℝ) → (Fin 12 → ℝ)
  boxLo : Fin 12 → ℚ
  boxHi : Fin 12 → ℚ
  /-- **承重前提**：盒内存在且仅存在一个根。 -/
  exists_unique : ∃! z : Fin 12 → ℝ,
    (∀ i : Fin 12, (boxLo i : ℝ) ≤ z i ∧ z i ≤ (boxHi i : ℝ)) ∧ sys z = 0
  /-- `R*` 所在的坐标。 -/
  radiusIndex : Fin 12

namespace C891RootSpec

/-- 由 `exists_unique` 与 `Classical.choice` 取出的根。 -/
noncomputable def root (S : C891RootSpec) : Fin 12 → ℝ :=
  Classical.choose S.exists_unique

/-- 取出的根确实在盒内且是零点。 -/
theorem root_mem (S : C891RootSpec) :
    (∀ i : Fin 12, (S.boxLo i : ℝ) ≤ S.root i ∧ S.root i ≤ (S.boxHi i : ℝ)) ∧
      S.sys S.root = 0 :=
  (Classical.choose_spec S.exists_unique).1

/-- 盒内唯一性。 -/
theorem root_unique (S : C891RootSpec) {z : Fin 12 → ℝ}
    (hz : (∀ i : Fin 12, (S.boxLo i : ℝ) ≤ z i ∧ z i ≤ (S.boxHi i : ℝ)) ∧ S.sys z = 0) :
    z = S.root :=
  (Classical.choose_spec S.exists_unique).2 z hz

end C891RootSpec

/-- **`R*`**：C891 根的第 `radiusIndex` 坐标。 -/
noncomputable def Rstar (S : C891RootSpec) : ℝ := S.root S.radiusIndex

/-- `R*` 落在盒的 R 坐标投影内。 -/
theorem Rstar_mem_box (S : C891RootSpec) :
    (S.boxLo S.radiusIndex : ℝ) ≤ Rstar S ∧ Rstar S ≤ (S.boxHi S.radiusIndex : ℝ) :=
  (S.root_mem.1 S.radiusIndex)

/-- **C922 口径的数值内核**：只要盒上端 `< 19/50`，就有 `R* < 19/50`。 -/
theorem Rstar_lt_R0_of_bound (S : C891RootSpec)
    (h : (S.boxHi S.radiusIndex : ℝ) < 19 / 50) : Rstar S < 19 / 50 :=
  lt_of_le_of_lt (Rstar_mem_box S).2 h

/-- **端到端切片（假言形式）**：证书数据 → checker 通过 → `R*` 落在证书包络内
⇒ `R* < 19/50`。

两个前提分工明确：`hcheck` 是**已证**的证书通过；`hlo`/`hhi` 是 C891 的
Krawczyk 包含义务（尚未形式化）。 -/
theorem Rstar_lt_R0_via_cert (S : C891RootSpec) (c : RootBoxCert)
    (hcheck : c.check = true)
    (hlo : (c.encLo : ℝ) ≤ Rstar S) (hhi : Rstar S ≤ (c.encHi : ℝ)) :
    Rstar S < 19 / 50 :=
  RootBoxCert.check_sound_lt_R0 hcheck (Rstar S) hlo hhi

/-- **条件主定理**：两条归一接口给出主命题，且**两侧使用同一个 `Rstar`**。 -/
theorem n11_main_conditional (S : C891RootSpec)
    (hattain : ∃ c : Fin 11 → Point, Covers c (Rstar S))
    (hbound : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → Rstar S ≤ r) :
    N11MainStatement (Rstar S) :=
  n11_main_of_strongInterface ⟨hattain, hbound⟩

/-- 条件主定理的"更小半径不可能"读数。 -/
theorem n11_no_smaller_conditional (S : C891RootSpec)
    (hattain : ∃ c : Fin 11 → Point, Covers c (Rstar S))
    (hbound : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → Rstar S ≤ r)
    {r : ℝ} (hr : r < Rstar S) :
    ¬ ∃ c : Fin 11 → Point, Covers c r :=
  no_cover_below ⟨hattain, hbound⟩ hr

/-- 条件主定理 ⇒ `sInf` 读数（与 `IsLeast` 口径一致）。 -/
theorem n11_sInf_conditional (S : C891RootSpec)
    (hattain : ∃ c : Fin 11 → Point, Covers c (Rstar S))
    (hbound : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → Rstar S ≤ r) :
    sInf feasibleRadii = Rstar S :=
  (n11_main_conditional S hattain hbound).2

end N11Formalization
