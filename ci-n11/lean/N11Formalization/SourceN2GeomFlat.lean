/-
n11-formalization — cline-six-20260930 / local-sharp — **unbuilt draft; Lead owns the serial slot**.

# SourceN2GeomFlat — `srcEdgeOf` 的**逆方向**（harmonic 需要）与 source-edge 索引的 consumer 形式

## 缘起（Lead 指派）
"GeomEdge2 GREEN … 可发 harmonic；accurate orientation inverse 需 `srcEdgeOf (srcFlat s) = s`，
优先桥整个 actual geometry consumer `hEV`。"
本件给出：
1. `srcFlat : SourceEdge → Fin 45`（`srcEdgeOf` 的逆：`(k,s) ↦ 2k+s`、`(j,t) ↦ 18+3j+t`）；
2. **`srcEdgeOf_srcFlat : ∀ s, srcEdgeOf (srcFlat s) = s`**（harmonic 要的正向逆式）与反向 `srcFlat_srcEdgeOf`；
3. **consumer 形式 `hEV_srcEdge`**：以**源边 `s`** 索引，直接给 canonical `edgeVector`：
   `srcEdgeVec u (srcFlat s) = edgeVector (canonAnchors u) (canonCenters u) (canonFaceZ u) (edgeMap s)`，
   并给分量版 `srcD2_srcEdge`（= `hEV_srcEdge` + `srcD2_eq_srcEdgeVec`）。
⇒ 下游（harmonic 的 force → small balance）可只用 `s : SourceEdge` 索引，不必再碰 45-边重标号。

## 依赖
`N11Formalization.SourceN2GeomEdge`（= 本 scope 的 GeomEdge **V2**，gate2 绿，sha 以树内副本为准）、
`SourceN2`、`SourceN2Geom`、`LocalSharpAuxZ`、`FlashLeafRootNetwork`、`ResumeDirichlet`。
（注意：需 Lead 先把 `SourceN2GeomEdge` copy 进树，本件的 import 才可解析。）

## Scope / 不声称
只做编号逆式与 consumer 桥；不做 force/balance/H、不做 α/N/Λ。
无 sorry / 无自定义 axiom / 无 `native_decide`；draft 未编译，不计 proved。
-/
import Mathlib
import N11Formalization.TCSystem
import N11Formalization.ResumeLocalIncidence
import N11Formalization.ResumeDirichlet
import N11Formalization.FlashLeafRootNetwork
import N11Formalization.LocalSharpAuxZ
import N11Formalization.SourceN2
import N11Formalization.SourceN2Geom
import N11Formalization.SourceN2GeomEdge

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.SourceN2GeomFlat

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.FlashRootNetwork
open N11Formalization.ResumeLocalIncidence
open N11Formalization.ResumeDirichlet
open N11Formalization.SourceN2
open N11Formalization.SourceN2Geom
open N11Formalization.SourceN2GeomEdge

noncomputable section

/-! ## 1. `srcEdgeOf` 的逆 -/

/-- **源边 → 45 边编号**（`srcEdgeOf` 的逆）：`(k,s) ↦ 2k+s`、`(j,t) ↦ 18+3j+t`。 -/
def srcFlat : SourceEdge → Fin 45
  | Sum.inl (k, s) => ⟨2 * (k : ℕ) + (s : ℕ), by omega⟩
  | Sum.inr (j, t) => ⟨18 + 3 * (j : ℕ) + (t : ℕ), by omega⟩

theorem srcFlat_spoke (k : Fin 9) (s : Fin 2) :
    srcFlat (Sum.inl (k, s)) = spokeFlat k s := rfl

theorem srcFlat_face (j : Fin 9) (t : Fin 3) :
    srcFlat (Sum.inr (j, t)) = faceFlatEdge j t := rfl

/-- **harmonic 要的逆式**：`srcEdgeOf (srcFlat s) = s`。 -/
theorem srcEdgeOf_srcFlat (s : SourceEdge) : srcEdgeOf (srcFlat s) = s := by
  rcases s with ⟨k, s'⟩ | ⟨j, t⟩
  · rw [srcFlat_spoke, srcEdgeOf_spoke]
  · rw [srcFlat_face, srcEdgeOf_face]

/-- 反向：`srcFlat (srcEdgeOf e) = e`。 -/
theorem srcFlat_srcEdgeOf (e : Fin 45) : srcFlat (srcEdgeOf e) = e := by
  by_cases h : (e : ℕ) < 18
  · have he : e = spokeFlat ⟨(e : ℕ) / 2, by omega⟩ ⟨(e : ℕ) % 2, by omega⟩ := by
      apply Fin.ext
      simp only [spokeFlat, Fin.val_mk]
      omega
    rw [he, srcEdgeOf_spoke, srcFlat_spoke]
  · have he : e = faceFlatEdge ⟨((e : ℕ) - 18) / 3, by omega⟩ ⟨((e : ℕ) - 18) % 3, by omega⟩ := by
      apply Fin.ext
      simp only [faceFlatEdge, Fin.val_mk]
      omega
    rw [he, srcEdgeOf_face, srcFlat_face]

/-! ## 2. consumer 形式：以源边 `s` 索引的 `hEV` -/

/-- **actual-geometry consumer 形式**：以源边 `s` 索引，直接给 canonical `edgeVector`。 -/
theorem hEV_srcEdge (u : Fin 12 → ℝ) (s : SourceEdge) :
    srcEdgeVec u (srcFlat s)
      = edgeVector (canonAnchors u) (canonCenters u)
          (N11Formalization.LocalSharpAuxZ.canonFaceZ u) (edgeMap s) := by
  rcases s with ⟨k, s'⟩ | ⟨j, t⟩
  · exact hEV_spoke u k s'
  · exact hEV_face u j t

/-- 分量版 consumer：`srcD2` 在源边 `s` 上 = canonical `edgeVector` 的相应分量。 -/
theorem srcD2_srcEdge (u : Fin 12 → ℝ) (s : SourceEdge) (c : Fin 2) :
    srcD2 u (srcFlat s) c
      = (edgeVector (canonAnchors u) (canonCenters u)
          (N11Formalization.LocalSharpAuxZ.canonFaceZ u) (edgeMap s)).ofLp c := by
  rw [srcD2_eq_srcEdgeVec, hEV_srcEdge]

end

end N11Formalization.SourceN2GeomFlat

#print axioms N11Formalization.SourceN2GeomFlat.srcEdgeOf_srcFlat
#print axioms N11Formalization.SourceN2GeomFlat.srcFlat_srcEdgeOf
#print axioms N11Formalization.SourceN2GeomFlat.hEV_srcEdge
#print axioms N11Formalization.SourceN2GeomFlat.srcD2_srcEdge
#check @N11Formalization.SourceN2GeomFlat.srcFlat
#check @N11Formalization.SourceN2GeomFlat.hEV_srcEdge
