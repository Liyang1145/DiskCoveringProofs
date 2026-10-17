/-
n11-formalization — cline-six-20260930 / local-sharp — **unbuilt draft; Lead owns the serial slot**.

# SourceN2Geom — 面列 `B2` 的**几何形式同一**（actual geometry + small incidence）

## 缘起（Lead 指派）
"立即准备面列 B2 形式同一到 actual geometry small incidence。"
`FlashLocalFrobeniusSourceN2`（= 本 scope 的 `SourceN2.V6`，gate 绿）已给出正确面表下的
`srcFaceSite2 / srcFaceC2 / srcZ2 / srcX2 / srcEdgeV2 / srcEdgeW2 / srcD2 / srcB2`；
本件把**面边列**接回 canonical 几何与源的小 incidence：

1. **端点行**：`srcEdgeV2 (faceFlatEdge j t) = 9 + (sourceFaces j t).val`（已证，SourceN2），
   `srcEdgeW2 (faceFlatEdge j t) = 20 + j`（本件 `srcEdgeW2_face`）；
2. **几何形式**：`srcD2 u (faceFlatEdge j t) c = (canonCenters u (face (faceMap j) t)).ofLp c
   − (LocalSharpAuxZ.canonFaceZ u (faceMap j)).ofLp c` —— 即 `edgeVector (canonAnchors u) (canonCenters u)
   (canonFaceZ u) (.inr (faceMap j, t))`（= `edgeMap (.inr (j,t))`）的 `.inr` 分支，分量形式
   （`edgeVector` 的 `.inr` 分支定义为 `C (face f v) − Z f`；分量差同 `ofLp_sub`）；
3. **small incidence**：面边列在两行上取值 `±d`（`+d` 在其 site 行 `2·(sourceFaces j t).val + c`，
   `−d` 在其 aux 行 `22 + 2j + c`），与 `ResumeDirichlet.incidence (.inr (f,v))` 的
   `+1 on .inl (face f v)` / `−1 on .inr f` 一致（本件给出两条 incidence 取值 + 两条行定理）。

## 依赖假设
`import N11Formalization.SourceN2`（Lead 已 copy V6 为模块；若改名，仅需同步本行）
与 `N11Formalization.LocalSharpAuxZ`（已 copy，sha DEA9）。

## Scope / 不声称
* 只做**源侧 B2 面列 ↔ canonical 几何/incidence**的桥；不做 α/N 解、不做力平衡、不做 Λ。
* 辐条列（`.inl` 侧）与 `T` 行同法可加，本件先只做面列（Lead 指定）。
* 无 sorry / 无自定义 axiom / 无 `native_decide`；draft 未编译，不计 proved。
-/
import Mathlib
import N11Formalization.TCSystem
import N11Formalization.ResumeLocalIncidence
import N11Formalization.ResumeDirichlet
import N11Formalization.FlashLeafRootNetwork
import N11Formalization.FlashLocalFrobeniusSourceN
import N11Formalization.LocalSharpAuxZ
import N11Formalization.SourceN2

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.SourceN2Geom

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.FlashRootNetwork
open N11Formalization.ResumeLocalIncidence
open N11Formalization.ResumeDirichlet
open N11Formalization.SourceN2

noncomputable section

/-! ## 0. 库引理全类型（按实际源核对） -/

section checks

#check @ResumeDirichlet.edgeVector
#check @ResumeDirichlet.incidence
#check @N11Formalization.LocalSharpAuxZ.canonFaceZ
#check @N11Formalization.LocalSharpAuxZ.sourceAuxZ
#check @N11Formalization.LocalSharpAuxZ.canonAux_vertex
#check @N11Formalization.LocalSharpAuxZ.canonFaceZ_active
#check @N11Formalization.SourceN2.srcD2_face
#check @N11Formalization.SourceN2.srcEdgeV2_face
#check @N11Formalization.SourceN2.srcZ2_eq_auxZ

end checks

/-! ## 1. 面边 W 端点（从 V6 已 gate 的 `hW` 块提取为独立引理） -/

/-- 面边 `18+3j+t` 的第二端点是 aux 节点 `20+j`。 -/
theorem srcEdgeW2_face (j : Fin 9) (t : Fin 3) :
    srcEdgeW2 (faceFlatEdge j t) = ⟨20 + (j : ℕ), by omega⟩ := by
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

/-! ## 2. 面列的几何形式（canonical 面顶点 + canonical 面外心） -/

/-- **面列几何形式**：源面边 `18+3j+t` 的边向量分量 = canonical 面 `faceMap j` 的
`edgeVector` 分支 `C (face (faceMap j) t) − canonFaceZ (faceMap j)` 的相应分量。
（`edgeVector` 的 `.inr` 分支定义即 `C (face f v) − Z f`；分量差 = `ofLp_sub`。） -/
theorem srcD2_face_eq_canonEdge (u : Fin 12 → ℝ) (j : Fin 9) (t : Fin 3) (c : Fin 2) :
    srcD2 u (faceFlatEdge j t) c =
      (canonCenters u (face (faceMap j) t)).ofLp c -
        (N11Formalization.LocalSharpAuxZ.canonFaceZ u (faceMap j)).ofLp c := by
  rw [srcD2_face u j t c, N11Formalization.LocalSharpAuxZ.canonAux_vertex u j t,
    N11Formalization.LocalSharpAuxZ.canonFaceZ_active u j, ← srcZ2_eq_auxZ u]

/-! ## 3. small incidence：面边列在两行上 ±d（与 `ResumeDirichlet.incidence` 的符号一致） -/

/-- `edgeMap (.inr (j,t)) = .inr (faceMap j, t)`（定义式）。 -/
theorem edgeMap_inr (j : Fin 9) (t : Fin 3) :
    edgeMap (Sum.inr (j, t)) = Sum.inr (faceMap j, t) := rfl

/-- incidence（site 侧）：`incidence (.inr (f,v)) (.inl (face f v)) = 1`。 -/
theorem incidence_face_site (f : Fin 11) (v : Fin 3) :
    ResumeDirichlet.incidence (Sum.inr (f, v)) (Sum.inl (face f v)) = 1 := by
  simp [ResumeDirichlet.incidence]

/-- incidence（aux 侧）：`incidence (.inr (f,v)) (.inr f) = -1`。 -/
theorem incidence_face_aux (f : Fin 11) (v : Fin 3) :
    ResumeDirichlet.incidence (Sum.inr (f, v)) (Sum.inr f) = -1 := by
  simp [ResumeDirichlet.incidence]

/-- **面列的 site 行**：行 `2·(sourceFaces j t).val + c`（= site 站点 `sourceFaces j t` 的第 `c` 分量）
取值 `+d_c`（incidence 符号 `+1`）。 -/
theorem srcB2_face_site_row (u : Fin 12 → ℝ) (j : Fin 9) (t : Fin 3) (c : Fin 2) :
    srcB2 u ⟨2 * (sourceFaces j t).val + (c : ℕ), by omega⟩ (faceFlatEdge j t)
      = srcD2 u (faceFlatEdge j t) c := by
  simp only [srcB2, Fin.val_mk, srcEdgeV2_face j t, srcEdgeW2_face j t]
  split_ifs with h1 h2 h3
  all_goals first
    | rfl
    | (exfalso; omega)
    | (have hidx : (⟨(2 * (sourceFaces j t).val + (c : ℕ)) % 2, by omega⟩ : Fin 2) = c := by
         apply Fin.ext
         simp only [Fin.val_mk]
         omega
       rw [hidx]
       simp)
    | simp

/-- **面列的 aux 行**：行 `22 + 2j + c`（= aux 节点 `20+j` 的第 `c` 分量）取值 `-d_c`
（incidence 符号 `-1`）。 -/
theorem srcB2_face_aux_row (u : Fin 12 → ℝ) (j : Fin 9) (t : Fin 3) (c : Fin 2) :
    srcB2 u ⟨22 + 2 * (j : ℕ) + (c : ℕ), by omega⟩ (faceFlatEdge j t)
      = - srcD2 u (faceFlatEdge j t) c := by
  simp only [srcB2, Fin.val_mk, srcEdgeV2_face j t, srcEdgeW2_face j t]
  split_ifs with h1 h2 h3
  all_goals first
    | rfl
    | (exfalso; omega)
    | (have hidx : (⟨(22 + 2 * (j : ℕ) + (c : ℕ)) % 2, by omega⟩ : Fin 2) = c := by
         apply Fin.ext
         simp only [Fin.val_mk]
         omega
       rw [hidx]
       simp)
    | simp

/-- **面列零行**（其余行）：若 `i` 既不是该 site 行也不是该 aux 行，则面边列在该行为 `0`
（incidence 支撑恰为两个端点 ⇒ "小 incidence" 的零处）。 -/
theorem srcB2_face_zero_row (u : Fin 12 → ℝ) (j : Fin 9) (t : Fin 3) (i : Fin 41)
    (h40 : (i : ℕ) ≠ 40)
    (hV : (i : ℕ) / 2 ≠ (sourceFaces j t).val) (hW : (i : ℕ) / 2 ≠ 11 + (j : ℕ)) :
    srcB2 u i (faceFlatEdge j t) = 0 := by
  simp only [srcB2, Fin.val_mk, srcEdgeV2_face j t, srcEdgeW2_face j t]
  split_ifs with h1 h2 h3
  all_goals first | rfl | (exfalso; omega) | (congr 1; apply Fin.ext; omega) | simp

end

end N11Formalization.SourceN2Geom

#print axioms N11Formalization.SourceN2Geom.srcEdgeW2_face
#print axioms N11Formalization.SourceN2Geom.srcD2_face_eq_canonEdge
#print axioms N11Formalization.SourceN2Geom.srcB2_face_site_row
#print axioms N11Formalization.SourceN2Geom.srcB2_face_aux_row
#print axioms N11Formalization.SourceN2Geom.srcB2_face_zero_row
#check @N11Formalization.SourceN2Geom.srcD2_face_eq_canonEdge
#check @N11Formalization.SourceN2Geom.srcB2_face_site_row
