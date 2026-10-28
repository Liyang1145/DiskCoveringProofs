/-
n11-formalization — cline-six-20260930 / local-sharp — **unbuilt draft; Lead owns the serial slot**.

# SourceN2GeomEdge.V2 — 全 45 边 point edge identity `hEV`（与 harmonic 的 `srcEdgeVec` 精确兼容）

**V2（post gate1）**：V1 gate1 红点我自读整份 log 分组为两处并修：
1. `srcEdgeOf` 的 `Fin 9` 索引在 `then` 分支用 `(e:ℕ)/2` **界不成立**（`e` 可达 44 ⇒ `e/2` 可达 22）——
   omega 的 counterexample 正是 `a := ↑↑e / 2, b := ↑↑e`。改为 **`% 9` 截断**（`x % 9 < 9`，与 `srcEdgeV2`
   的辐条 `% 9` 同法）。
2. `hEV_spoke` 用 `simp only [edgeVector]` 时参数还不是构造子，留下 `match` 残项；且 `edgeMap_side0`
   的 simp 匹配失败（未用）。改为**显式 `have hV/hW/hR`（`rw` 只在自写的词形上匹配）+ 显式 `Fin.ext` 索引等式**，
   不用 `simp only` 链、不用 `congr`。

## 依赖（全部已进树、已 gate）
`N11Formalization.SourceN2`（V6）、`SourceN2Geom`（V3）、`LocalSharpAuxZ`（DEA9）、
`FlashLeafRootNetwork`、`ResumeDirichlet`、`ResumeLocalIncidence`。

## 形状（与 harmonic 精确兼容）
`srcEdgeVec (u : Fin 12 → ℝ) (e : Fin 45) : Point := srcX2 u (srcEdgeV2 e) − srcX2 u (srcEdgeW2 e)`
（`X_V − X_W` 的 Point 差、两参数，同 `SourceN2` 的 29 点/45 边对象）。

## Scope / 不声称
只做边侧几何恒等（Point 差 ↔ canonical `edgeVector`）；不做 force/balance/H（归 harmonic）。
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

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.SourceN2GeomEdge

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.FlashRootNetwork
open N11Formalization.ResumeLocalIncidence
open N11Formalization.ResumeDirichlet
open N11Formalization.SourceN2
open N11Formalization.SourceN2Geom

noncomputable section

/-! ## 1. 源 45 边的 Point 差与编号映射 -/

/-- **源边向量（Point 差）**：`X_V − X_W`，只依赖 `u` 与边编号 `e : Fin 45`。 -/
noncomputable def srcEdgeVec (u : Fin 12 → ℝ) (e : Fin 45) : Point :=
  srcX2 u (srcEdgeV2 e) - srcX2 u (srcEdgeW2 e)

/-- 45 边编号 → 源边：`2k+s ↦ .inl (k,s)`、`18+3j+t ↦ .inr (j,t)`。
索引一律 **`% 9` 截断**（`x % 9 < 9`），避免 `then` 分支的界不成立。 -/
def srcEdgeOf (e : Fin 45) : SourceEdge :=
  if (e : ℕ) < 18 then
    Sum.inl (⟨(e : ℕ) / 2 % 9, by omega⟩, ⟨(e : ℕ) % 2, by omega⟩)
  else
    Sum.inr (⟨((e : ℕ) - 18) / 3 % 9, by omega⟩, ⟨((e : ℕ) - 18) % 3, by omega⟩)

theorem srcEdgeOf_spoke (k : Fin 9) (s : Fin 2) :
    srcEdgeOf (spokeFlat k s) = Sum.inl (k, s) := by
  simp only [srcEdgeOf]
  split
  · rename_i h
    have h1 : (⟨(2 * (k : ℕ) + (s : ℕ)) / 2 % 9, by omega⟩ : Fin 9) = k := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    have h2 : (⟨(2 * (k : ℕ) + (s : ℕ)) % 2, by omega⟩ : Fin 2) = s := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    simp only [spokeFlat, Fin.val_mk]
    rw [h1, h2]
  · rename_i h
    exfalso
    simp only [spokeFlat, Fin.val_mk] at h
    omega

theorem srcEdgeOf_face (j : Fin 9) (t : Fin 3) :
    srcEdgeOf (faceFlatEdge j t) = Sum.inr (j, t) := by
  simp only [srcEdgeOf]
  split
  · rename_i h
    exfalso
    simp only [faceFlatEdge, Fin.val_mk] at h
    omega
  · rename_i h
    have h1 : (⟨(18 + 3 * (j : ℕ) + (t : ℕ) - 18) / 3 % 9, by omega⟩ : Fin 9) = j := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    have h2 : (⟨(18 + 3 * (j : ℕ) + (t : ℕ) - 18) % 3, by omega⟩ : Fin 3) = t := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    simp only [faceFlatEdge, Fin.val_mk]
    rw [h1, h2]

/-! ## 2. 端点/记账（辐条端点 + canonical 面-顶点 wiring） -/

theorem srcEdgeV2_spoke (k : Fin 9) (s : Fin 2) :
    srcEdgeV2 (spokeFlat k s) = ⟨9 + (((k : ℕ) + (s : ℕ)) % 9), by omega⟩ := by
  apply Fin.ext
  simp only [srcEdgeV2, Fin.val_mk]
  split
  · rename_i h
    simp only [spokeFlat, Fin.val_mk]
    omega
  · rename_i h
    exfalso
    simp only [spokeFlat, Fin.val_mk] at h
    omega

theorem srcEdgeW2_spoke (k : Fin 9) (s : Fin 2) :
    srcEdgeW2 (spokeFlat k s) = ⟨(k : ℕ), by omega⟩ := by
  apply Fin.ext
  simp only [srcEdgeW2, Fin.val_mk]
  split
  · rename_i h
    simp only [spokeFlat, Fin.val_mk]
    omega
  · rename_i h
    exfalso
    simp only [spokeFlat, Fin.val_mk] at h
    omega

theorem canonCenters_siteMap (u : Fin 12 → ℝ) (k : Fin 9) :
    canonCenters u ⟨(siteMap k).val, by omega⟩ = centersOfRoot u ⟨(k : ℕ), by omega⟩ := by
  simp only [canonCenters]
  congr 1
  fin_cases k <;> decide

theorem canonCenters_siteMap_succ (u : Fin 12 → ℝ) (k : Fin 9) :
    canonCenters u ⟨(siteMap (k + 1)).val, by omega⟩ =
      centersOfRoot u ⟨((k : ℕ) + 1) % 9, by omega⟩ := by
  simp only [canonCenters]
  congr 1
  fin_cases k <;> decide

theorem anchorIndex_side_one (i : Fin 9) : anchorIndex i (1 : Fin 2) = i := by
  simp [anchorIndex]

theorem anchorIndex_side_zero_succ (k : Fin 9) :
    anchorIndex (siteMap (k + 1)) (0 : Fin 2) = siteMap k := by
  simpa using boundary_anchor_exact k 1

theorem edgeMap_side0 (k : Fin 9) :
    edgeMap (Sum.inl (k, (0 : Fin 2))) = Sum.inl (siteMap k, (1 : Fin 2)) := by
  simp [edgeMap]

theorem edgeMap_side1 (k : Fin 9) :
    edgeMap (Sum.inl (k, (1 : Fin 2))) = Sum.inl (siteMap (k + 1), (0 : Fin 2)) := by
  simp [edgeMap]

/-! ## 3. 分量桥 -/

theorem srcD2_eq_srcEdgeVec (u : Fin 12 → ℝ) (e : Fin 45) (c : Fin 2) :
    srcD2 u e c = (srcEdgeVec u e).ofLp c := by
  simp [srcD2, srcEdgeVec]

/-! ## 4. 逐边 point edge identity（面 + 辐条） -/

theorem hEV_face (u : Fin 12 → ℝ) (j : Fin 9) (t : Fin 3) :
    srcEdgeVec u (faceFlatEdge j t)
      = edgeVector (canonAnchors u) (canonCenters u)
          (N11Formalization.LocalSharpAuxZ.canonFaceZ u) (edgeMap (Sum.inr (j, t))) := by
  simp only [srcEdgeVec, srcEdgeV2_face j t, srcEdgeW2_face j t, srcX2_site, srcX2_aux,
    edgeMap, edgeVector, N11Formalization.LocalSharpAuxZ.canonAux_vertex u j t,
    N11Formalization.LocalSharpAuxZ.canonFaceZ_active u j, srcZ2_eq_auxZ u]

/-- **辐条**（V2：显式 have/rw，绕开 `match` 残项与 simp 匹配）。 -/
theorem hEV_spoke (u : Fin 12 → ℝ) (k : Fin 9) (s : Fin 2) :
    srcEdgeVec u (spokeFlat k s)
      = edgeVector (canonAnchors u) (canonCenters u)
          (N11Formalization.LocalSharpAuxZ.canonFaceZ u) (edgeMap (Sum.inl (k, s))) := by
  fin_cases s
  · have hV : srcX2 u (srcEdgeV2 (spokeFlat k (0 : Fin 2)))
        = centersOfRoot u ⟨(((k : ℕ) + (0 : ℕ)) % 9), by omega⟩ := by
      rw [srcEdgeV2_spoke]
      exact srcX2_site u ⟨(((k : ℕ) + (0 : ℕ)) % 9), by omega⟩
    have hW : srcX2 u (srcEdgeW2 (spokeFlat k (0 : Fin 2))) = arcEnd u k := by
      rw [srcEdgeW2_spoke]
      exact srcX2_anchor u k
    have hR : edgeVector (canonAnchors u) (canonCenters u)
          (N11Formalization.LocalSharpAuxZ.canonFaceZ u) (edgeMap (Sum.inl (k, (0 : Fin 2))))
        = centersOfRoot u ⟨(k : ℕ), by omega⟩ - arcEnd u k := by
      rw [edgeMap_side0 k]
      simp only [edgeVector, anchorIndex_side_one, hU_siteMap, canonCenters_siteMap]
    have hfin : (⟨(((k : ℕ) + (0 : ℕ)) % 9), by omega⟩ : Fin 11) = ⟨(k : ℕ), by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    show srcX2 u (srcEdgeV2 (spokeFlat k (0 : Fin 2))) -
        srcX2 u (srcEdgeW2 (spokeFlat k (0 : Fin 2))) =
      edgeVector (canonAnchors u) (canonCenters u)
        (N11Formalization.LocalSharpAuxZ.canonFaceZ u) (edgeMap (Sum.inl (k, (0 : Fin 2))))
    rw [hV, hW, hR, hfin]
  · have hV : srcX2 u (srcEdgeV2 (spokeFlat k (1 : Fin 2)))
        = centersOfRoot u ⟨(((k : ℕ) + (1 : ℕ)) % 9), by omega⟩ := by
      rw [srcEdgeV2_spoke]
      exact srcX2_site u ⟨(((k : ℕ) + (1 : ℕ)) % 9), by omega⟩
    have hW : srcX2 u (srcEdgeW2 (spokeFlat k (1 : Fin 2))) = arcEnd u k := by
      rw [srcEdgeW2_spoke]
      exact srcX2_anchor u k
    have hR : edgeVector (canonAnchors u) (canonCenters u)
          (N11Formalization.LocalSharpAuxZ.canonFaceZ u) (edgeMap (Sum.inl (k, (1 : Fin 2))))
        = centersOfRoot u ⟨((k : ℕ) + 1) % 9, by omega⟩ - arcEnd u k := by
      rw [edgeMap_side1 k]
      simp only [edgeVector, anchorIndex_side_zero_succ, hU_siteMap, canonCenters_siteMap_succ]
    show srcX2 u (srcEdgeV2 (spokeFlat k (1 : Fin 2))) -
        srcX2 u (srcEdgeW2 (spokeFlat k (1 : Fin 2))) =
      edgeVector (canonAnchors u) (canonCenters u)
        (N11Formalization.LocalSharpAuxZ.canonFaceZ u) (edgeMap (Sum.inl (k, (1 : Fin 2))))
    rw [hV, hW, hR]

/-- **全 45 边**（以 `srcEdgeOf` 重标号）。 -/
theorem hEV (u : Fin 12 → ℝ) (e : Fin 45) :
    srcEdgeVec u e
      = edgeVector (canonAnchors u) (canonCenters u)
          (N11Formalization.LocalSharpAuxZ.canonFaceZ u) (edgeMap (srcEdgeOf e)) := by
  by_cases h : (e : ℕ) < 18
  · have he : e = spokeFlat ⟨(e : ℕ) / 2, by omega⟩ ⟨(e : ℕ) % 2, by omega⟩ := by
      apply Fin.ext
      simp only [spokeFlat, Fin.val_mk]
      omega
    rw [he, srcEdgeOf_spoke]
    exact hEV_spoke u _ _
  · have he : e = faceFlatEdge ⟨((e : ℕ) - 18) / 3, by omega⟩ ⟨((e : ℕ) - 18) % 3, by omega⟩ := by
      apply Fin.ext
      simp only [faceFlatEdge, Fin.val_mk]
      omega
    rw [he, srcEdgeOf_face]
    exact hEV_face u _ _

end

end N11Formalization.SourceN2GeomEdge

#print axioms N11Formalization.SourceN2GeomEdge.srcEdgeOf_spoke
#print axioms N11Formalization.SourceN2GeomEdge.srcEdgeOf_face
#print axioms N11Formalization.SourceN2GeomEdge.canonCenters_siteMap_succ
#print axioms N11Formalization.SourceN2GeomEdge.srcD2_eq_srcEdgeVec
#print axioms N11Formalization.SourceN2GeomEdge.hEV_face
#print axioms N11Formalization.SourceN2GeomEdge.hEV_spoke
#print axioms N11Formalization.SourceN2GeomEdge.hEV
#check @N11Formalization.SourceN2GeomEdge.srcEdgeVec
#check @N11Formalization.SourceN2GeomEdge.hEV
