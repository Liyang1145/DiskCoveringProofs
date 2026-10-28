import N11Formalization.FlashSlackConsumer
import N11Formalization.RootRangeBoxFull
import N11Formalization.GridBridge

/-!
# FlashSlackRoot —— 把 generic 的 `u` 定理实例到**真实 C891 根** `S.root`

**关键读源结论（不猜）**：
* `C891RootSpec`（`Conditional/RootSpec.lean:30`）的字段只有 `sys/boxLo/boxHi/exists_unique/radiusIndex`；
  `exists_unique : ∃! z, (盒内) ∧ sys z = 0` ⇒ **S 自身担保"盒内存在唯一根"**；
  `S.root = Classical.choose S.exists_unique`（`:44`）、`S.root_mem : (盒内) ∧ sys (S.root) = 0`（`:48`）。
* `Rstar S := S.root S.radiusIndex`（`:62`）。
* `TCSystem_first`（`TCSystem.lean:162`）：`TCSystem u i = residual u i`（`i : Fin 5`）
  ⇒ `sys = TCSystem` + `Sys (S.root) = 0` **直接给出** `residual S.root = 0`；
* `RootRangeBookFull.InCertBox S.root` 由 `S.root_mem.1` + `S.boxLo = boxLoCert` + `S.boxHi = boxHiCert`
  **逐坐标改写**即得（无额外前提）；
* `RootRangeBoxFull.rootRange_of_box`（`:205`）由 `InCertBox` 给 `RootRange`（其余五个域条件全在件内已证）。

⇒ 本件**不重新引入** `hu : InCertBox S.root` / `hres : residual S.root = 0`：两者都由 S 的字段**导出**。
⇒ 最终只剩 `hsys`（源同一性：`S.sys = TCSystem`）+ `hlo`/`hhi`（盒同一性）+ `hidx`（半径坐标）+ `hcover`（11 面剖分）。

**存在性口径**：`S : C891RootSpec` 的 `exists_unique` 字段本身就断言"盒内存在唯一根"；
`GridBridge.nd_box_final`（`:1576`，**无条件终定理**）给出满足该字段的 `S`。
故用 `nd_box_final` 实例化时，根存在性是 S 字段/上游定理担保的，**不是**本件新增前提；
本件既不 weakening 也不 over-claim 同根存在性。
-/

noncomputable section

namespace N11Formalization.FlashSlackRoot

open N11Formalization

/-- **generic root 消费者**（对**任意** `S`）：只给源同一性/盒同一性/半径坐标 + `hcover`，
`hu` 与 `hres` 由 S 的字段**导出**，不重复引入。 -/
theorem covers_of_root (S : C891RootSpec) (hsys : S.sys = TCSystem)
    (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6)
    (hcover : ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot S.root)) →
      ∃ n : Fin 11, ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
        p = la • centersOfRoot S.root (FlashBoundaryCapsFaces.faceI1 n)
              + lb • centersOfRoot S.root (FlashBoundaryCapsFaces.faceI2 n)
              + lc • centersOfRoot S.root (FlashBoundaryCapsFaces.faceI3 n)) :
    Covers (centersOfRoot S.root) (Rstar S) := by
  -- `residual S.root = 0`：由 `sys = TCSystem` + 根方程 + `TCSystem_first` 逐分量导出
  have hres : residual S.root = 0 := by
    funext k
    have hz : TCSystem S.root = 0 := by rw [← hsys]; exact S.root_mem.2
    have h := congrFun hz ⟨(k : ℕ), by omega⟩
    rw [TCSystem_first] at h
    simpa using h
  -- `InCertBox S.root`：由 `root_mem` 的盒 + 盒同一性
  have hu : RootRangeBoxFull.InCertBox S.root := by
    intro i
    have h := S.root_mem.1 i
    rw [hlo, hhi] at h
    exact h
  -- 半径确实是第 6 坐标 ⇒ `u 6 = Rstar S`
  have h6 : S.root 6 = Rstar S := by rw [Rstar, hidx]
  have h := FlashSlackConsumer.covers_of_box_of_slackFace S.root hu hres hcover
  rwa [h6] at h

/-- **端到端：真实 `nd_box_final` 的根**（无条件终定理供给 `S`）。
只剩 `hcover`（11 面凸包表示）；`Rstar S < 19/50` 一并给出（与主定理阈值接口一致）。 -/
theorem exists_root_covers (hcover : ∀ (S : C891RootSpec),
      S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert → S.radiusIndex = 6 →
      ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot S.root)) →
      ∃ n : Fin 11, ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
        p = la • centersOfRoot S.root (FlashBoundaryCapsFaces.faceI1 n)
              + lb • centersOfRoot S.root (FlashBoundaryCapsFaces.faceI2 n)
              + lc • centersOfRoot S.root (FlashBoundaryCapsFaces.faceI3 n)) :
    ∃ S : C891RootSpec, S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧
      S.radiusIndex = 6 ∧ Rstar S < 19 / 50 ∧ Covers (centersOfRoot S.root) (Rstar S) := by
  obtain ⟨S, hs, hlo, hhi, hidx, _, hlt⟩ := GridBridge.nd_box_final
  exact ⟨S, hs, hlo, hhi, hidx, hlt, covers_of_root S hs hlo hhi hidx (hcover S hs hlo hhi hidx)⟩

end N11Formalization.FlashSlackRoot

#print axioms N11Formalization.FlashSlackRoot.covers_of_root
#print axioms N11Formalization.FlashSlackRoot.exists_root_covers
