import N11Formalization.FlashSlackFace1
import N11Formalization.FlashBoundaryCapsFaces

/-!
# FlashSlackConsumer —— 面 0 的 `FaceCoverable` + 端到端组合（只剩 hu / hres / hcover）

**输入**（只读，不改）：
* `N11Formalization.FlashSlackFace1`：`O0 : Point` 与三条
  `dist (ringCenter u 0) O0 ≤ u 6`、`dist (ringCenter u 1) O0 ≤ u 6`、`dist (hub1 u) O0 ≤ u 6`（`u ∈ InCertBox`）。
* `N11Formalization.FlashBoundaryCapsFaces`：`FaceCoverable`（= `∃O` 三顶点距离 ≤ `u 6`）、
  `faceOK_table`、`covers_of_box_of_faces`（λ `hF0` + `hcover` ⇒ `Covers`）。

**输出**：
1. `faceCoverable01_10`：`FaceCoverable u ⟨0⟩ ⟨1⟩ 10`（见证 = `O0`，把 `centersOfRoot` 解回三顶点并**核 dist 方向**）；
2. `covers_of_box_of_slackFace`：只余 `hu`（`InCertBox`）、`hres`（`residual u = 0`）、
   `hcover`（11 面凸包表示）三个前提。
-/

noncomputable section

namespace N11Formalization.FlashSlackConsumer

open N11Formalization

/-- **面 0 的 `FaceCoverable`**：见证取 `FlashSlackFace1.O0`。
`dist` 方向逐条核：`FaceCoverable` 要求 `dist (centersOfRoot …) O ≤ u 6`，
而本件供给的是 `dist (ringCenter …) O0 ≤ u 6`，故用 `centersOfRoot_ring`/`centersOfRoot_ten` 改写主语
（`dist` 的方向一致，无需 `dist_comm`）。 -/
theorem faceCoverable01_10 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    FlashBoundaryCapsFaces.FaceCoverable u ⟨0, by omega⟩ ⟨1, by omega⟩ 10 := by
  have h0 : centersOfRoot u ⟨0, by omega⟩ = ringCenter u 0 := centersOfRoot_ring u 0
  have h1 : centersOfRoot u ⟨1, by omega⟩ = ringCenter u 1 := centersOfRoot_ring u 1
  have h10 : centersOfRoot u 10 = hub1 u := centersOfRoot_ten u
  exact ⟨FlashSlackFace1.O0,
    by rw [h0]; exact FlashSlackFace1.dist_ring0_le u hu,
    by rw [h1]; exact FlashSlackFace1.dist_ring1_le u hu,
    by rw [h10]; exact FlashSlackFace1.dist_hub1_le u hu⟩

/-- **端到端**：`InCertBox u` + `residual u = 0` + 11 面凸包表示 ⇒ `Covers (centersOfRoot u) (u 6)`。
（`Covers` 的定义域已含 `‖center‖ ≤ 1 + r` 型约束，由 `centersOfRoot` 的既有接口处理；
本件只负责把 `hF0` 从 slack 面的三条距离补齐。） -/
theorem covers_of_box_of_slackFace (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u)
    (hres : residual u = 0)
    (hcover : ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot u)) →
      ∃ n : Fin 11, ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
        p = la • centersOfRoot u (FlashBoundaryCapsFaces.faceI1 n)
              + lb • centersOfRoot u (FlashBoundaryCapsFaces.faceI2 n)
              + lc • centersOfRoot u (FlashBoundaryCapsFaces.faceI3 n)) :
    Covers (centersOfRoot u) (u 6) :=
  FlashBoundaryCapsFaces.covers_of_box_of_faces u hu hres (faceCoverable01_10 u hu) hcover

end N11Formalization.FlashSlackConsumer

#print axioms N11Formalization.FlashSlackConsumer.faceCoverable01_10
#print axioms N11Formalization.FlashSlackConsumer.covers_of_box_of_slackFace
