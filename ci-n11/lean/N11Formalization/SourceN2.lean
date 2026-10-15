/-
n11-formalization — cline-six-20260930 / local-sharp — **unbuilt draft; Lead owns the serial slot**.

# SourceN2 — 源侧 29 点 / 45 边 / 41×45 B 的**正确重建**（面表直接引用，不改原源）

## 缘起（Lead 指派）
`FlashLocalFrobeniusSourceN.srcFaceSite : Fin 27 → Fin 9` 的字面量 `9/10` 被 Lean 按 `Fin 9`
**取模成 `0/1`** ⇒ 面表 **11/27 槽错（全部 hub 槽，9 面全中）**，其 `srcFaceC/srcZ/srcX/srcEdgeV/srcD/srcB`
全部被污染（B 面列 27/27、125 项、max|Δ|≈1.21；见 `IMPACT-srcFaceSite.md`）。
本文件按"**直接引用已核面表**"重建，**不修改原源**（原 `FlashLocalFrobeniusSourceN.lean` 一字不动）。

## 设计
* **面表不再重抄**：`srcFaceSite2 : Fin 27 → Fin 11 := fun i => sourceFaces (i/3) (i%3)`
  —— 类型就是源站点的真值域 `Fin 11`（0..10），**不存在取模塌陷**；
* `srcFaceC2` 直接取 `centersOfRoot u (sourceFaces j t)`（**无需** `Fin.castLE`）；
* `srcZ2` 用同一个 `circumcenter`（与源 `cc()` 逐项同式，见 C1626）⇒ `srcZ2 u = AuxZ 的 sourceAuxZ`（rfl）；
* `srcX2`（29 点：0..8 anchor、9..19 site、20..28 aux）、`srcEdgeV2/srcEdgeW2`（45 边，面边端点用真表）、
  `srcD2`（边向量）、`srcB2`（41×45）逐条与源 `interval_network_envelope.py` L27–L54 对齐；
* 交付**正确语义下的 sanity**：`srcB2 u 0 0`（旧源那份仍真的单点结论在正确语义下重证）、
  `srcEdgeV2_face`（面边端点 = 真表 hub）、`srcD2_face`/`srcD2_spoke`（45 边 ↔ `T` 侧 `srcVec` 的两支）。

## Scope / 不声称
* 只做**源侧几何/矩阵定义与桥接**；不含 α/N（source-stress 线）、不含 Λ（harmonic-response 线）。
* 旧模块 `FlashLocalFrobeniusSourceN` 只借它的 `circumcenter`（公式已核）；其表相关定义**一律不用**。
* 命名空间用 `N11Formalization.SourceN2`（`*2` 后缀），**不做同名替换**，便于 Lead 集成时改名。
* 无 sorry / 无自定义 axiom / 无 `native_decide`；draft 未编译，不计 proved。
-/
import Mathlib
import N11Formalization.TCSystem
import N11Formalization.ResumeLocalIncidence
import N11Formalization.FlashLocalFrobeniusSourceN
import N11Formalization.LocalSharpAuxZ

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.SourceN2

open Finset
open N11Formalization
open N11Formalization.ResumeLocalIncidence

noncomputable section

/-! ## 0. 库引理全类型（命名空间按实际源核对） -/

section checks

#check @N11Formalization.circumcenter
#check @ResumeLocalIncidence.sourceFaces
#check @ResumeLocalIncidence.faceMap
#check @ResumeLocalIncidence.siteMap
#check @N11Formalization.arcEnd
#check @N11Formalization.centersOfRoot

end checks

/-! ## 1. 面表：**直接引用** sourceFaces（Fin 11 值域，无取模塌陷） -/

/-- 摊平槽号：面 `j` 的第 `t` 个顶点（与源 L21/L30 的顺序一致）。 -/
def faceFlat (j : Fin 9) (t : Fin 3) : Fin 27 := ⟨3 * (j : ℕ) + (t : ℕ), by omega⟩

/-- 45 边编号：辐条 `2k+s`。 -/
def spokeFlat (k : Fin 9) (s : Fin 2) : Fin 45 := ⟨2 * (k : ℕ) + (s : ℕ), by omega⟩

/-- 45 边编号：面边 `18+3j+t`（源 L30 `edges.extend((9+s,20+j) for s in f)`）。 -/
def faceFlatEdge (j : Fin 9) (t : Fin 3) : Fin 45 := ⟨18 + 3 * (j : ℕ) + (t : ℕ), by omega⟩

/-- **源 9 面表（摊平 27 项）**：直接引用已核 `ResumeLocalIncidence.sourceFaces`，
值域为 `Fin 11`（源站点真值 0..10）——不再有 `Fin 9` 取模（9/10 变 0/1）的塌陷。 -/
def srcFaceSite2 (i : Fin 27) : Fin 11 :=
  sourceFaces ⟨(i : ℕ) / 3, by omega⟩ ⟨(i : ℕ) % 3, by omega⟩

/-- 槽号 ↔ (面,顶点) 一致：摊平表的第 `3j+t` 项就是 `sourceFaces j t`。 -/
theorem srcFaceSite2_faceFlat (j : Fin 9) (t : Fin 3) :
    srcFaceSite2 (faceFlat j t) = sourceFaces j t := by
  fin_cases j <;> fin_cases t <;> decide

/-- `.val` 形式（供 Nat 层比较/下游审计用）。 -/
theorem srcFaceSite2_val_faceFlat (j : Fin 9) (t : Fin 3) :
    (srcFaceSite2 (faceFlat j t)).val = (sourceFaces j t).val := by
  rw [srcFaceSite2_faceFlat]

/-- hub 槽真值不减：`sourceFaces` 里 hub 站点的 `.val` 可以是 9/10（对比旧表被塌陷成 0/1）。 -/
theorem srcFaceSite2_val_eq_source (i : Fin 27) :
    (srcFaceSite2 i).val = (sourceFaces ⟨(i : ℕ) / 3, by omega⟩ ⟨(i : ℕ) % 3, by omega⟩).val := rfl

/-! ## 2. 面心、面外心、29 点 -/

/-- 面 `j` 的第 `t` 个中心（直接用真表，无 castLE）。 -/
def srcFaceC2 (u : Fin 12 → ℝ) (j : Fin 9) (t : Fin 3) : Point :=
  centersOfRoot u (srcFaceSite2 (faceFlat j t))

theorem srcFaceC2_eq (u : Fin 12 → ℝ) (j : Fin 9) (t : Fin 3) :
    srcFaceC2 u j t = centersOfRoot u (sourceFaces j t) := by
  simp only [srcFaceC2, srcFaceSite2_faceFlat]

/-- 面外心 `Z_j`（节点 20+j）：同一个 `circumcenter`（= 源 `cc()` 同式）+ 同一张已核面表
⇒ 与 AuxZ 的 `sourceAuxZ u j` **定义同为** `circumcenter (centersOfRoot u (sourceFaces j ·))`（rfl）。 -/
def srcZ2 (u : Fin 12 → ℝ) (j : Fin 9) : Point :=
  circumcenter (srcFaceC2 u j 0) (srcFaceC2 u j 1) (srcFaceC2 u j 2)

theorem srcZ2_eq (u : Fin 12 → ℝ) (j : Fin 9) :
    srcZ2 u j =
      circumcenter (centersOfRoot u (sourceFaces j 0)) (centersOfRoot u (sourceFaces j 1))
        (centersOfRoot u (sourceFaces j 2)) := by
  simp only [srcZ2, srcFaceC2_eq]

/-- 源 29 点 `X = U + C + Z`（0..8 anchor、9..19 site、20..28 aux），与源 L27 同布局。 -/
def srcX2 (u : Fin 12 → ℝ) : Fin 29 → Point := fun i =>
  if h : (i : ℕ) < 9 then arcEnd u ⟨i, h⟩
  else if h2 : (i : ℕ) < 20 then centersOfRoot u ⟨(i : ℕ) - 9, by omega⟩
  else srcZ2 u ⟨(i : ℕ) - 20, by omega⟩

/-! ### 2.5 通用节点归约（V4：按 Lead 口径用 `isLt` + `rw`，不做 81 案例展开；多用途可复用） -/

/-- **通用 anchor 节点**：节点 `k`（`k : Fin 9`，即 `k.val < 9`）就是 `arcEnd u k`。
（V5：`rw [dif_pos …]` 已把目标化为 `arcEnd u ⟨↑k,_⟩ = arcEnd u k` 并由 `rfl` 关闭
—— 两个 `Fin 9` 项同值、仅证明分量不同；V4 里多余的 `congr 1 / Fin.ext` 因此报 no goals。） -/
theorem srcX2_anchor (u : Fin 12 → ℝ) (k : Fin 9) :
    srcX2 u ⟨(k : ℕ), by omega⟩ = arcEnd u k := by
  simp only [srcX2, Fin.val_mk]
  rw [dif_pos (show ((k : ℕ) : ℕ) < 9 by omega)]

/-- **通用 site 节点**：节点 `9 + i`（`i : Fin 11`）就是 `centersOfRoot u i`
（用 `i.isLt : i.val < 11` 判 `9 + i.val < 20`，无需分情形）。 -/
theorem srcX2_site (u : Fin 12 → ℝ) (i : Fin 11) :
    srcX2 u ⟨9 + (i : ℕ), by omega⟩ = centersOfRoot u i := by
  simp only [srcX2, Fin.val_mk]
  rw [dif_neg (show ¬ ((9 + (i : ℕ) : ℕ) < 9) by omega)]
  rw [dif_pos (show ((9 + (i : ℕ) : ℕ) : ℕ) < 20 by omega)]
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

/-- **通用 aux 节点**：节点 `20 + j`（`j : Fin 9`）就是 `srcZ2 u j`。 -/
theorem srcX2_aux (u : Fin 12 → ℝ) (j : Fin 9) :
    srcX2 u ⟨20 + (j : ℕ), by omega⟩ = srcZ2 u j := by
  simp only [srcX2, Fin.val_mk]
  rw [dif_neg (show ¬ ((20 + (j : ℕ) : ℕ) < 9) by omega)]
  rw [dif_neg (show ¬ ((20 + (j : ℕ) : ℕ) < 20) by omega)]
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

/-- **源外心 = AuxZ 的 `sourceAuxZ`**（集成后 rfl 级同一对象；此处以函数相等给出）。 -/
theorem srcZ2_eq_auxZ (u : Fin 12 → ℝ) :
    srcZ2 u = N11Formalization.LocalSharpAuxZ.sourceAuxZ u := by
  funext j
  simp only [srcZ2, srcFaceC2_eq, N11Formalization.LocalSharpAuxZ.sourceAuxZ]

/-! ## 3. 45 边、边向量、41×45 B -/

/-- 边 `e` 第一端：`e<18` 为辐条 site `9+(k+s)%9`；否则面边端点 site = **真表** `f[t]`。 -/
def srcEdgeV2 (e : Fin 45) : Fin 29 :=
  if h : (e : ℕ) < 18 then ⟨9 + (((e : ℕ) / 2 + (e : ℕ) % 2) % 9), by omega⟩
  else ⟨9 + (srcFaceSite2 ⟨(e : ℕ) - 18, by omega⟩).val, by omega⟩

/-- 边 `e` 第二端：`e<18` 为 anchor `k`；否则面心节点 `20+j`。 -/
def srcEdgeW2 (e : Fin 45) : Fin 29 :=
  if h : (e : ℕ) < 18 then ⟨(e : ℕ) / 2, by omega⟩
  else ⟨20 + ((e : ℕ) - 18) / 3, by omega⟩

/-- 边向量 `d_c = (X_v − X_w)_c`（源 L49）。 -/
def srcD2 (u : Fin 12 → ℝ) (e : Fin 45) (c : Fin 2) : ℝ :=
  (srcX2 u (srcEdgeV2 e)).ofLp c - (srcX2 u (srcEdgeW2 e)).ofLp c

/-- 源 41×45 B：行 `2*(node−9)+c`（node ∈ 9..28）给 `±d_c`；行 40 为 1（源 L47–L54）。 -/
def srcB2 (u : Fin 12 → ℝ) (i : Fin 41) (e : Fin 45) : ℝ :=
  if (i : ℕ) = 40 then 1
  else
    let node : ℕ := 9 + (i : ℕ) / 2
    let c : Fin 2 := ⟨(i : ℕ) % 2, by omega⟩
    (if (srcEdgeV2 e : ℕ) = node then srcD2 u e c else 0)
      + (if (srcEdgeW2 e : ℕ) = node then -srcD2 u e c else 0)

/-! ## 4. 正确语义下的 sanity（旧源那份仍真的单点结论 + 面边端点正确性 + 45 边 ↔ T 侧两支） -/

/-- `B[0,0] = (X_9 − X_0)₀ = C_0x − U_0x`（旧 `srcB_00` 在**正确面表**下重证；该式本就只涉辐条与 node 9/0，
故旧模块的 C1532/C1535 不受缺陷影响 —— 本定理给出同式的新语义版本）。 -/
theorem srcB2_00 (u : Fin 12 → ℝ) :
    srcB2 u 0 0 = (centersOfRoot u 0).ofLp 0 - (arcEnd u 0).ofLp 0 := by
  simp only [srcB2, srcEdgeV2, srcEdgeW2, srcX2, srcD2]
  norm_num

/-- **面边端点正确性**：`srcEdgeV2 (18+3j+t) = 9 + (sourceFaces j t).val`（旧表在此处给 site 0/1）。 -/
theorem srcEdgeV2_face (j : Fin 9) (t : Fin 3) :
    srcEdgeV2 (faceFlatEdge j t) = ⟨9 + (sourceFaces j t).val, by omega⟩ := by
  fin_cases j <;> fin_cases t <;> decide

/-- **面边 ↔ T 侧 `srcVec` 的 `.inr` 支**：`d = C_{f[t]} − Z_j`（组件形式）。
（V6：`hW` 改在 **`.val`（ℕ）层**做 `Fin.ext` + `split` + `omega` —— V4 在 `dite` 层用 `dif_neg` 会因
`Decidable` 实例仍是 `(↑(faceFlatEdge j t)).decLt 18` 而匹配失败（gate4 L203，目标"not type-correct
under implicit transparency"）。） -/
theorem srcD2_face (u : Fin 12 → ℝ) (j : Fin 9) (t : Fin 3) (c : Fin 2) :
    srcD2 u (faceFlatEdge j t) c = (centersOfRoot u (sourceFaces j t)).ofLp c - (srcZ2 u j).ofLp c := by
  have hV : srcEdgeV2 (faceFlatEdge j t) = ⟨9 + (sourceFaces j t).val, by omega⟩ :=
    srcEdgeV2_face j t
  have hW : srcEdgeW2 (faceFlatEdge j t) = ⟨20 + (j : ℕ), by omega⟩ := by
    apply Fin.ext
    simp only [srcEdgeW2, Fin.val_mk]
    split
    · rename_i h
      exfalso
      simp only [faceFlatEdge, Fin.val_mk] at h
      omega
    · rename_i h
      simp only [faceFlatEdge, Fin.val_mk]
      omega
  have h1 : srcX2 u (srcEdgeV2 (faceFlatEdge j t)) = centersOfRoot u (sourceFaces j t) := by
    rw [hV]
    exact srcX2_site u (sourceFaces j t)
  have h2 : srcX2 u (srcEdgeW2 (faceFlatEdge j t)) = srcZ2 u j := by
    rw [hW]
    exact srcX2_aux u j
  simp only [srcD2, h1, h2]

/-- **辐条 ↔ T 侧 `srcVec` 的 `.inl` 支**：`d = C_{(k+s)%9} − U_k`（组件形式）。
（保持 V1 已被 gate 证明可行的 `simp only` 形态。） -/
theorem srcD2_spoke (u : Fin 12 → ℝ) (k : Fin 9) (s : Fin 2) (c : Fin 2) :
    srcD2 u (spokeFlat k s) c =
      (centersOfRoot u ⟨(((k : ℕ) + (s : ℕ)) % 9), by omega⟩).ofLp c - (arcEnd u k).ofLp c := by
  fin_cases k <;> fin_cases s <;> fin_cases c <;>
    simp only [srcD2, srcX2, srcEdgeV2, srcEdgeW2, spokeFlat]
  all_goals norm_num

/-- 计数：45 边 = 18 辐条 + 27 面边；面表 27 槽的值域是 `Fin 11`（含 9/10）。 -/
theorem srcFaceSite2_hub_values :
    (srcFaceSite2 (faceFlat 0 1)).val = 9 ∧ (srcFaceSite2 (faceFlat 0 2)).val = 10 := by
  decide

/-! ## 5. 与 legacy 模块的 **kernel 级** 桥（不用 numeric 相等充当依赖证据）

Lead 口径：旧 C1532/C1535 只涉单点 `srcB u 0 0`，其"不受缺陷影响"必须以 **kernel 等式**落在新模块上，
不能只靠数值相等。下面两条给出：① 新表下该单点的同式结论（`srcB2_00`，§4）；② 新旧定义的**等式桥**
`srcB2 u 0 0 = srcB u 0 0`（legacy 定义不改，仅引用其已证 `srcB_00`）。 -/

/-- **新旧单点相等（kernel）**：`srcB2 u 0 0 = srcB u 0 0` —— legacy 的 C1532/C1535 所依赖的那一个
条目在新语义下**同一**，且新表版本由 `srcB2_00` 独立给出。 -/
theorem srcB2_eq_legacy_00 (u : Fin 12 → ℝ) : srcB2 u 0 0 = srcB u 0 0 := by
  rw [srcB2_00, srcB_00]
  simp [centersOfRoot]

/-- **缺陷在图层的 kernel 计数**：面边端点（新 `srcEdgeV2` vs legacy `srcEdgeV`）在 **11** 条面边上不同
（= 全部 hub 槽；与 `srcFaceSite_mismatch_card = 11` 一致）。 -/
theorem srcEdgeV2_ne_legacy_face_edge_count :
    (Finset.univ.filter (fun p : Fin 9 × Fin 3 =>
        srcEdgeV2 (faceFlatEdge p.1 p.2) ≠ srcEdgeV (faceFlatEdge p.1 p.2))).card = 11 := by
  decide

end

end N11Formalization.SourceN2

#print axioms N11Formalization.SourceN2.srcFaceSite2_faceFlat
#print axioms N11Formalization.SourceN2.srcX2_anchor
#print axioms N11Formalization.SourceN2.srcX2_site
#print axioms N11Formalization.SourceN2.srcX2_aux
#print axioms N11Formalization.SourceN2.srcZ2_eq_auxZ
#print axioms N11Formalization.SourceN2.srcB2_00
#print axioms N11Formalization.SourceN2.srcB2_eq_legacy_00
#print axioms N11Formalization.SourceN2.srcEdgeV2_face
#print axioms N11Formalization.SourceN2.srcD2_face
#print axioms N11Formalization.SourceN2.srcD2_spoke
#print axioms N11Formalization.SourceN2.srcFaceSite2_hub_values
#print axioms N11Formalization.SourceN2.srcEdgeV2_ne_legacy_face_edge_count
#check @N11Formalization.SourceN2.srcFaceSite2
#check @N11Formalization.SourceN2.srcZ2
#check @N11Formalization.SourceN2.srcB2
#check @N11Formalization.SourceN2.srcB2_eq_legacy_00
#check @N11Formalization.SourceN2.srcEdgeV2_face
