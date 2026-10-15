/-
n11-formalization — cline-six-20260930 / local-sharp — **unbuilt draft; Lead owns the serial slot**.

# LocalSharpAuxZ — 源外心 Z ↔ canonical 辅助 Z 在活跃 9 面的**精确等式**（无 `hZ` 前件）

## 任务（Lead 指派）
"实际 hZ 来源 / 45 自由 20 → 51 自由 22 的消零接线；先查已存在 canonicalZ 定义；给 source exteriorZ
与 canonicalZ 活跃 9 面的精确等式，不给另一个带 hZ 前件 wrapper；若根结构阻断请指出具体待证 TC 方程。"

## 本件结论
1. **canonical 侧取内禀定义**（新名）：`canonFaceZ u j = circumcenter (canonCenters u (face j 0)) … (face j 2)`
   —— 对 11 个 canonical 面（含 slack 面 5,7）都给出辅助点，不依赖任何根/TC 数据。
2. **源侧用已核面表**定义：`sourceAuxZ u f = circumcenter (centersOfRoot u (sourceFaces f 0)) … (f 2)`，
   其中 `sourceFaces` 是 `ResumeLocalIncidence` 里与源文件 `interval_network_envelope.py` L21
   **逐项一致**的那张表（本 scope 审计 `audit_c920_pin_transport.py` D3 已验证）。
3. **主定理**（无 `hZ`、无根数据）：
   `canonFaceZ_active : ∀ f : Fin 9, canonFaceZ u (faceMap f) = sourceAuxZ u f`，
   由已证 `faceMap_exact`（**有序**顶点对应）+ `hC_rawToCanon` 直接得到；
   这正是 T3 `edgeVector_edgeMap`/`Tmat_edgeMap` 的 `hZ` 前件的来源，**不是另一条带 hZ 的 wrapper**。
4. **消零接线（45/20 → 51/22）**：`not_mem_range_iff_slack` 证明 canonical 51 边中**不在源 45 边像内**
   的边恰是面 5、7 的 6 条边；`faceMap_ne_five_seven`/`faceMap_surj_active` 给出活跃 9 面的标号事实；
   `source_free_card`/`canon_free_card` 记录自由节点 20（11 site + 9 aux）→ 22（11 site + 11 aux）。
   两个多出的 aux 点（面 5,7）**只承载这 6 条边**，因此 C920 的 G/T 数据在 `N = 0`（V3 的 `hNz`）下
   与它们的位置无关。
5. **缺陷报告（不是 TC 方程）**：`N11Formalization.srcFaceSite`（文件 `FlashLocalFrobeniusSourceN.lean`，
   `srcZ` 用它）的**类型是 `Fin 27 → Fin 9`** —— 字面量 `9`/`10` 被 Lean 按 `Fin 9` **模约简成 `0`/`1`**
   （负控：`(9 : Fin 9) = 0`、`(10 : Fin 9) = 1`；`Fin.castLE` 只做单射嵌入、**不会**把 `0/1` 复原成 `9/10`）。
   故按 Lean 语义：**27 槽里 11 槽错，恰是全部 hub 槽；9 个面全被污染**（不是"3 处 hub 写反"——那是
   把字面文本当整数读出的假读数）。后果（精确计数见 §4）：`srcFaceC`/`srcZ` 的 9 个面外心全错、
   `srcEdgeV` 的 27 条面边里 11 条端点 site 错、`srcX` 的 aux 节点 20..28 全错、`srcB` 的 27 条面边列
   全错（行 0..3 多出伪项、行 18..21 缺项、行 22..39 值错）。
   ⇒ **整 SourceN 的 "source identity" 已否**，不能把它的 `srcB`/`srcZ` 提升为源矩阵/源外心；
   但 `srcB_00`（B(0,0)：行 0 = node 9、边 0 = spoke (node 9, node 0)，不涉 hub 也不涉 aux）**仍真**，
   故 SourceNB00/SourceNB00Root 的 C1532/C1535 **不受影响**。修法 = 重抄面表为 `Fin 11`（或改引 `sourceFaces`）。

## 接线（等 T3 被 integrate 后一行用上）
```lean
-- theorem edgeVector_edgeMap_actual (u : Fin 12 → ℝ) (s : SourceEdge) :
--     edgeVector (canonAnchors u) (canonCenters u) (canonFaceZ u) (edgeMap s)
--       = srcVec u (sourceAuxZ u) s :=
--   edgeVector_edgeMap u (canonFaceZ u) (sourceAuxZ u) (fun f => canonFaceZ_active u f) s
-- theorem Tmat_edgeMap_actual (u) (tang) (s) (j) :
--     Tmat anchorIncidence (edgeVector (canonAnchors u) (canonCenters u) (canonFaceZ u)) tang j (edgeMap s)
--       = Tmat sgnRaw (srcVec u (sourceAuxZ u)) tang j s :=
--   Tmat_edgeMap u (canonFaceZ u) (sourceAuxZ u) (fun f => canonFaceZ_active u f) tang s j
```

## Scope / 不声称
* 只做 **Z / 辅助点侧**；N、Λ、α 一律不碰（source-stress / harmonic-response 线）。
* 不声称 `canonFaceZ u 5`、`canonFaceZ u 7` 满足覆盖/距离界（那条由 attainment 的 `O0`/镜像 witness 线负责）。
* 无 sorry / 无自定义 axiom / 无 `native_decide`；draft 未编译，不计 proved。
-/
import Mathlib
import N11Formalization.ResumeLocalIncidence
import N11Formalization.ResumeNetwork
import N11Formalization.FlashLeafRootNetwork
import N11Formalization.FlashLocalFrobeniusSourceN

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.LocalSharpAuxZ

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeLocalIncidence
open N11Formalization.FlashRootNetwork

/-! 注：`FlashLocalFrobeniusSourceN.lean` 在 **`namespace N11Formalization`** 下声明
（不是以文件名命名空间），故 `circumcenter`/`srcFaceSite`/`srcFaceIdx`/`srcFaceC`/`srcZ`
的全名是 `N11Formalization.…`，由上面的 `open N11Formalization` 取用（**不** open 文件名空间）。 -/

noncomputable section

/-! ## 0. 用到的库引理全类型（按实际命名空间核对，不按文件名推断） -/

section checks

#check @N11Formalization.circumcenter
#check @N11Formalization.srcFaceSite
#check @N11Formalization.srcFaceIdx
#check @N11Formalization.srcFaceC
#check @N11Formalization.srcZ
#check @ResumeLocalIncidence.sourceFaces
#check @ResumeLocalIncidence.faceMap
#check @ResumeLocalIncidence.faceMap_exact
#check @ResumeLocalIncidence.edgeMap
#check @ResumeLocalIncidence.edgeMap_injective
#check @ResumeLocalIncidence.edgeMap_image
#check @ResumeLocalIncidence.source_edge_card
#check @ResumeNetwork.face
#check @ResumeNetwork.edge_card
#check @FlashRootNetwork.canonCenters
#check @FlashRootNetwork.hC_rawToCanon
#check @FlashRootNetwork.edgeMap_preimage_zero
#check @FlashRootNetwork.edgeMap_preimage_one

end checks

/-! ## 1. 两侧辅助点（canonical 面外心 / 源面外心） -/

/-- **canonical 辅助点（内禀）**：面 `j` 的三个中心的外心。
对 11 个 canonical 面都有定义（含 slack 面 5,7）；不依赖根/TC 数据。 -/
def canonFaceZ (u : Fin 12 → ℝ) (j : Fin 11) : Point :=
  circumcenter (canonCenters u (face j 0)) (canonCenters u (face j 1)) (canonCenters u (face j 2))

/-- **源外心**：源面 `f` 的三个中心的外心，面表用已核的 `sourceFaces`
（与 `interval_network_envelope.py` L21 逐项一致；**不是** `srcFaceSite`，见 §4 缺陷报告）。 -/
def sourceAuxZ (u : Fin 12 → ℝ) (f : Fin 9) : Point :=
  circumcenter (centersOfRoot u (sourceFaces f 0)) (centersOfRoot u (sourceFaces f 1))
    (centersOfRoot u (sourceFaces f 2))

/-! ## 2. 顶点逐项对应（有序）与主等式 -/

/-- 活跃 9 面的**有序**顶点对应：canonical 面 `faceMap f` 的第 `v` 个中心就是源面 `f` 的第 `v` 个中心。 -/
theorem canonAux_vertex (u : Fin 12 → ℝ) (f : Fin 9) (v : Fin 3) :
    canonCenters u (face (faceMap f) v) = centersOfRoot u (sourceFaces f v) := by
  rw [← faceMap_exact f v, hC_rawToCanon u (sourceFaces f v)]

/-- **主等式**：源外心与 canonical 辅助点在活跃 9 面上逐面相等。
证明只用 `canonAux_vertex`（三次），**没有 hZ 前件、没有根数据**。 -/
theorem canonFaceZ_active (u : Fin 12 → ℝ) (f : Fin 9) :
    canonFaceZ u (faceMap f) = sourceAuxZ u f := by
  simp only [canonFaceZ, sourceAuxZ]
  rw [canonAux_vertex u f 0, canonAux_vertex u f 1, canonAux_vertex u f 2]

/-- 反向（活跃面侧）：每个非 slack 的 canonical 面都来自唯一一个源面。 -/
theorem faceMap_surj_active (j : Fin 11) (h5 : j ≠ 5) (h7 : j ≠ 7) :
    ∃ f : Fin 9, faceMap f = j := by
  fin_cases j <;>
    first
      | exact absurd rfl h5
      | exact absurd rfl h7
      | decide

/-! ## 3. 消零接线：45/20 → 51/22 -/

/-- 活跃 9 面避开 slack 面 5、7。 -/
theorem faceMap_ne_five_seven (f : Fin 9) : faceMap f ≠ 5 ∧ faceMap f ≠ 7 := by
  fin_cases f <;> decide

/-- **canonical 51 边中不在源 45 边像内的边，恰是面 5、7 的 6 条边。**
（`⇐` 方向用 `edgeMap_image`；`⇒` 方向用 `edgeMap_preimage_zero/one` 造边界原像 + `edgeMap_image` 排除面边。） -/
theorem not_mem_range_iff_slack (e : Edge) :
    e ∉ Set.range edgeMap ↔
      (∃ v : Fin 3, e = Sum.inr (5, v)) ∨ (∃ v : Fin 3, e = Sum.inr (7, v)) := by
  constructor
  · intro h
    rcases e with ⟨i, s⟩ | ⟨f, v⟩
    · exfalso
      apply h
      fin_cases s
      · exact ⟨Sum.inl (i + 1, (⟨1, by decide⟩ : Fin 2)), edgeMap_preimage_zero i⟩
      · exact ⟨Sum.inl (i + 2, (⟨0, by decide⟩ : Fin 2)), edgeMap_preimage_one i⟩
    · by_cases hf : f = 5 ∨ f = 7
      · rcases hf with h5 | h7
        · exact Or.inl ⟨v, by rw [h5]⟩
        · exact Or.inr ⟨v, by rw [h7]⟩
      · exfalso
        apply h
        have hne : f ≠ 5 ∧ f ≠ 7 :=
          ⟨fun h5 => hf (Or.inl h5), fun h7 => hf (Or.inr h7)⟩
        exact (edgeMap_image (Sum.inr (f, v))).2 hne
  · intro h hr
    obtain ⟨s, hs⟩ := hr
    rcases h with ⟨v, hv⟩ | ⟨v, hv⟩
    · have hff := (edgeMap_image (Sum.inr (5, v))).1 ⟨s, by rw [hv] at hs; exact hs⟩
      exact hff.1 rfl
    · have hff := (edgeMap_image (Sum.inr (7, v))).1 ⟨s, by rw [hv] at hs; exact hs⟩
      exact hff.2 rfl

/-- 自由节点计数：源 20（11 site + 9 aux），canonical 22（11 site + 11 aux）。 -/
theorem source_free_card : Fintype.card ((Fin 11) ⊕ (Fin 9)) = 20 := by decide

theorem canon_free_card : Fintype.card ((Fin 11) ⊕ (Fin 11)) = 22 := by decide

/-! ## 4. 缺陷报告（**Lean 语义**版）：`srcFaceSite : Fin 27 → Fin 9` 的 11 个 hub 槽全部错

**gate1 教训（本人 v1 审计错在哪）**：v1 把 `.lean` 里的字面量当**整数文本**读，得出"3 处 hub 写反"。
但 `srcFaceSite` 的类型是 `Fin 27 → Fin 9`，Lean 对字面量 `9`/`10` 按 `Fin 9` **取模**：`(9 : Fin 9) = 0`、
`(10 : Fin 9) = 1`。故实际语义表里，凡是 hub 槽都变成了 **site 0/1**；`srcFaceC` 的
`Fin.castLE (Fin 9 → Fin 11)` 只做单射嵌入，**不会**把 `0/1` 还原成 `9/10`。
按 Lean 语义：**27 槽错 11 槽（= 全部 hub 槽）、9 个面全被污染**。

下面 4 条把该缺陷在 kernel 里封成可判定事实（`.val` 比较，避开 `Fin 9` vs `Fin 11` 的类型错配；
与 `FlashLocalFrobeniusSourceN.lean` 的**当前 SHA** 绑定，修表后可删）。 -/

/-- 负控（Lean 取模语义）：`(9 : Fin 9) = 0`、`(10 : Fin 9) = 1`。 -/
theorem fin9_nine_is_zero : (9 : Fin 9) = 0 ∧ (10 : Fin 9) = 1 := by decide

/-- 缺陷计数（Lean 语义，`.val` 比较）：与已核 `sourceFaces` 不一致的槽数 = **11**。 -/
theorem srcFaceSite_mismatch_card :
    (Finset.univ.filter (fun p : Fin 9 × Fin 3 =>
        (srcFaceSite (srcFaceIdx p.1 p.2)).val ≠ (sourceFaces p.1 p.2).val)).card = 11 := by
  decide

/-- 缺陷计数：一致的槽数 = **16**（恰好是 27 − 11 的 ring 槽）。 -/
theorem srcFaceSite_agree_card :
    (Finset.univ.filter (fun p : Fin 9 × Fin 3 =>
        (srcFaceSite (srcFaceIdx p.1 p.2)).val = (sourceFaces p.1 p.2).val)).card = 16 := by
  decide

/-- **保留被否的那条（非真）声明**：`∀ f t, val 相等` 在原表下为假（11 处反例，例如面 0 顶点 1）。 -/
theorem srcFaceSite_not_all_agree :
    ¬ (∀ (f : Fin 9) (t : Fin 3), (srcFaceSite (srcFaceIdx f t)).val = (sourceFaces f t).val) := by
  intro h
  exact absurd (h 0 1) (by decide)

/-- 每个面都至少有一个 hub 槽被污染（9 个面全中），故 `srcZ` 的 9 个面外心全错。
（用 `card > 0` 而非 `∃ t, …`，避免有限 `∃` 的 `decide` 路径；两者等价：见 `srcFaceSite_mismatch_card`。） -/
theorem srcFaceSite_every_face_polluted (f : Fin 9) :
    0 < (Finset.univ.filter (fun t : Fin 3 =>
        (srcFaceSite (srcFaceIdx f t)).val ≠ (sourceFaces f t).val)).card := by
  fin_cases f <;> decide

/-- 面边端点计数：`srcEdgeV` 在面边 `18+3f+t` 处用 `(srcFaceSite …).val` 当 site 索引，
故 27 条面边里 **11 条**端点 site 错（用在 kernel 侧只需记这个数）。 -/
theorem srcFaceSite_face_edge_tips_wrong :
    (Finset.univ.filter (fun p : Fin 9 × Fin 3 =>
        (srcFaceSite (srcFaceIdx p.1 p.2)).val ≠ (sourceFaces p.1 p.2).val)).card = 11 :=
  srcFaceSite_mismatch_card

end

end N11Formalization.LocalSharpAuxZ

#print axioms N11Formalization.LocalSharpAuxZ.canonFaceZ_active
#print axioms N11Formalization.LocalSharpAuxZ.not_mem_range_iff_slack
#check @N11Formalization.LocalSharpAuxZ.canonFaceZ
#check @N11Formalization.LocalSharpAuxZ.sourceAuxZ
#check @N11Formalization.LocalSharpAuxZ.canonFaceZ_active
#check @N11Formalization.LocalSharpAuxZ.not_mem_range_iff_slack
