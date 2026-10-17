import N11Formalization.TCSystem

/-!
# 源网络（interval_network_envelope.py）几何的实际 Lean 定义

Lead 2026-09-30 指派：明确实际 B 条目的 Lean 定义（root 点 + edge incidence），
为逐 entry 的 source membership 校准做准备。**逐行对照**源文件：

* `srcFaceSite` = 源 L21 `F` 摊平的 27 项 site 表（9 面 × 3）；
* `circumcenter` = 源 L25 `cc()` 的外心公式（逐符号）；
* `srcZ` = 源 L27 `Z=[cc(f) for f in F]`（9 个面外心，节点 20..28）；
* `srcX` = 源 L27 `X = U + C + Z`（29 点：0..8 = `arcEnd`（源 L20 `U`，**不是** `Uvec`）、
  9..19 = `centersOfRoot`（源 L19 `C`，9 环心 + 2 hub）、20..28 = `srcZ`）；
* `srcEdgeV/W` = 源 L28–30 的 45 边（18 辐条 `(9+k,k)`、`(9+(k+1)%9,k)` + 27 面边 `(9+s,20+j)`）；
* `srcB` = 源 L47–54 的 41×45 B（行 `2*(node-9)+c`，node ∈ 9..28，第 40 行 = 1）。

**已验证的 sanity**：`srcB u 0 0 = (ringCenter u 0).ofLp 0 − (arcEnd u 0).ofLp 0`
（源 probe：`B[0,0] ∈ [−0.028952366821406013205, −0.028952323431160029862]`）。

**下一步（未付）**：逐 entry membership——对 `u ∈ ndBox`（`RootRangeBoxFull`）用
`ndAngleBox`/`cosTotLag`/`sinTotLag`/`ResumeGlobalCapWidth` 一类的区间核证明实际 box 包含。
源的列选择（数值 pivoting）：`dep = [32,22,21,30,31,19,44,26,27,40,36,33,42,43,24,28,34,25,37,39,23,20,35,2,13,17,16,29,9,11,12,6,4,1,14,8,3,15,0,38,41]`，`free = [18,10,7,5]`；
`N` 为 45×4，`N[free k, k] = 1` 且 `B · N_col = 0`（由 41×41 子系统解出）。
-/

namespace N11Formalization

noncomputable section

open Finset

/-- 源 9 面表（摊平 27 项；`interval_network_envelope.py` L21）。 -/
def srcFaceSite : Fin 27 → Fin 9 :=
  ![2, 9, 10, 6, 9, 10, 1, 2, 9, 2, 3, 9, 3, 4, 9, 4, 5, 10, 5, 6, 10, 6, 7, 10, 8, 0, 10]

/-- 面 `j` 的第 `t` 个 site（`t = 0,1,2`）。 -/
def srcFaceIdx (j : Fin 9) (t : Fin 3) : Fin 27 :=
  ⟨3 * (j : ℕ) + (t : ℕ), by omega⟩

/-- 三角形外心（源 `cc()`：`v=b−a, w=c−a, d=(|b|²−|a|²)/2, e=(|c|²−|a|²)/2`，
`det=v₀w₁−v₁w₀`，中心 `=((d w₁−e v₁)/det, (v₀ e−w₀ d)/det)`）。 -/
def circumcenter (A B Cc : Point) : Point :=
  !₂[(((‖B‖ ^ 2 - ‖A‖ ^ 2) / 2) * (Cc - A).ofLp 1 - ((‖Cc‖ ^ 2 - ‖A‖ ^ 2) / 2) * (B - A).ofLp 1)
        / ((B - A).ofLp 0 * (Cc - A).ofLp 1 - (B - A).ofLp 1 * (Cc - A).ofLp 0),
      ((B - A).ofLp 0 * ((‖Cc‖ ^ 2 - ‖A‖ ^ 2) / 2) - (Cc - A).ofLp 0 * ((‖B‖ ^ 2 - ‖A‖ ^ 2) / 2))
        / ((B - A).ofLp 0 * (Cc - A).ofLp 1 - (B - A).ofLp 1 * (Cc - A).ofLp 0)]

/-- 面 `j` 的三个中心（`centersOfRoot` 的 0..10 号，site 索引 < 9）。 -/
def srcFaceC (u : Fin 12 → ℝ) (j : Fin 9) (t : Fin 3) : Point :=
  centersOfRoot u (Fin.castLE (by omega) (srcFaceSite (srcFaceIdx j t)))

/-- 面外心 `Z_j`（节点 20+j）。 -/
def srcZ (u : Fin 12 → ℝ) (j : Fin 9) : Point :=
  circumcenter (srcFaceC u j 0) (srcFaceC u j 1) (srcFaceC u j 2)

/-- 源 29 点 `X = U + C + Z`。 -/
def srcX (u : Fin 12 → ℝ) : Fin 29 → Point :=
  fun i =>
    if h : (i : ℕ) < 9 then arcEnd u ⟨i, h⟩
    else if h2 : (i : ℕ) < 20 then centersOfRoot u ⟨(i : ℕ) - 9, by omega⟩
    else srcZ u ⟨(i : ℕ) - 20, by omega⟩

/-- 边 `e` 的第一端点：`e<18` 为 `2k`/`2k+1` 的 `9+k` / `9+(k+1)%9`；否则面边 `9+site`。 -/
def srcEdgeV (e : Fin 45) : Fin 29 :=
  if h : (e : ℕ) < 18 then ⟨9 + (((e : ℕ) / 2 + (e : ℕ) % 2) % 9), by omega⟩
  else ⟨9 + (srcFaceSite ⟨(e : ℕ) - 18, by omega⟩ : ℕ), by omega⟩

/-- 边 `e` 的第二端点：`e<18` 为 site `k`；否则面心节点 `20+j`。 -/
def srcEdgeW (e : Fin 45) : Fin 29 :=
  if h : (e : ℕ) < 18 then ⟨(e : ℕ) / 2, by omega⟩
  else ⟨20 + ((e : ℕ) - 18) / 3, by omega⟩

/-- 边向量 `d_c = (X_v − X_w)_c`（源 L49）。 -/
def srcD (u : Fin 12 → ℝ) (e : Fin 45) (c : Fin 2) : ℝ :=
  (srcX u (srcEdgeV e)).ofLp c - (srcX u (srcEdgeW e)).ofLp c

/-- 源 41×45 B：行 `2*(node−9)+c`（node ∈ 9..28）给 `sgn·d_c` 的有符号贡献（`node=v` 取 `+d_c`、
`node=w` 取 `−d_c`）；行 40 为 1。 -/
def srcB (u : Fin 12 → ℝ) (i : Fin 41) (e : Fin 45) : ℝ :=
  if (i : ℕ) = 40 then 1
  else
    let node : ℕ := 9 + (i : ℕ) / 2
    let c : Fin 2 := ⟨(i : ℕ) % 2, by omega⟩
    (if (srcEdgeV e : ℕ) = node then srcD u e c else 0)
      + (if (srcEdgeW e : ℕ) = node then -srcD u e c else 0)

/-- sanity：`B[0,0] = (X_9 − X_0)₀ = C_0x − U_0x = ringCenter 0 − arcEnd 0`（源 probe 值
`≈ −0.0289523451`，属于 `[−0.028952366821406013205, −0.028952323431160029862]`）。 -/
theorem srcB_00 (u : Fin 12 → ℝ) :
    srcB u 0 0 = (ringCenter u 0).ofLp 0 - (arcEnd u 0).ofLp 0 := by
  simp only [srcB, srcEdgeV, srcEdgeW, srcX, srcD]
  norm_num
  simp [centersOfRoot]

/-- sanity：辐条 `k=8`，`e=16`（`(9+8,8)`）。 -/
theorem srcEdge_sixteen :
    srcEdgeV 16 = ⟨17, by omega⟩ ∧ srcEdgeW 16 = ⟨8, by omega⟩ := by
  simp only [srcEdgeV, srcEdgeW]
  norm_num

/-- sanity：面边首条（`e=18`：`(9+2, 20+0)`）。 -/
theorem srcEdge_eighteen :
    srcEdgeV 18 = ⟨11, by omega⟩ ∧ srcEdgeW 18 = ⟨20, by omega⟩ := by
  simp only [srcEdgeV, srcEdgeW, srcFaceSite]
  norm_num

end

end N11Formalization

#print axioms N11Formalization.srcB_00
#print axioms N11Formalization.srcEdge_sixteen
#print axioms N11Formalization.srcEdge_eighteen
