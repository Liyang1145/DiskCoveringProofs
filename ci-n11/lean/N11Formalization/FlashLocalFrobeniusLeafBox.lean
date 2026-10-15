import N11Formalization.FlashLocalFrobeniusLeaf
import N11Formalization.ResumeIntervalAugmented

/-!
# FlashLocal — 120 局部叶承重链 · 第十八环：**Box 版 leaf**（源 H/G entry boxes）

Lead 2026-09-30：新 leaf 消掉 `B8`（任意同余矩阵的 membership）+ `hmem/hintrow`，
改用**源 H/G entry boxes**：`HB : Fin 8 → Fin 8 → RatInterval`、`GB : Fin 8 → Fin 4 → RatInterval`
（只对 pinned 8 行）、有理同余矩阵 `Cq : Matrix (Fin 8) (Fin 8) ℚ`、`η : ℚ`；
行界用**计算出的** `congruenceBox Cq (augmentedBox HB GB 734 (9/5000))`，不再手填 B8。
经已核 `ResumeIntervalAugmented.coercivity_of_boxes`（`t=734`, `μ=9/5000`）直接得
`(9/5000)Σx² ≤ Σ H0mat x x + 2·734·Σ(Gᵀx)²`，再与 pinned-G gate、方向下界、
标量余量合成为 `(Σx²)/100000 ≤ V2(U + disp θ x) − R*²`。

`hHsym`（受限 H0mat 对称）由 `hsym` 经 `H0mat_symm` 内部导出，不作前件。
pin 传输复用 `ResumePinnedCoercivity.sum_delete_pin`/`quadratic_delete_pin`；排列（canonical6.succAbove ↦ raw8=[2,3,4,5,6,7,0,1]）由 Lead 的 Fin8 transport 供给，本件不重复。
`hpsd` **不再作前件**：由 `hresp` + 已有 `energy_nonneg` + `le_csInf` 直接导出（不复制 PSD 核）。
**未付**：`hrow/hNcol/hNbal/hs/ha/hl/hUeq/hdiag/hr/hresp/hpin/hsym/hCfrob/hFsq/hρ/hfluxα`
与 `hHbox/hGbox/hrowBox/hgFrob/hη`（源身份与区间证书）。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset
open N11Formalization.ResumeNetwork N11Formalization.ResumeDirichlet
  N11Formalization.ResumeDirichletShift N11Formalization.ResumeStressComparison
  N11Formalization.ResumeAdaptiveRoot N11Formalization.ResumeAnchorFlux
  N11Formalization.ResumeAdaptiveRows N11Formalization.ResumeAdaptiveBalance
  N11Formalization.ResumeResponseBound
  N11Formalization.ResumeFluxTaylor N11Formalization.ResumeFluxRemainder
  N11Formalization.ResumeAdaptiveShift
  N11Formalization.ResumeCoercivityCertificate N11Formalization.ResumePinnedCoercivity
  N11Formalization.ResumeIntervalCoercivity N11Formalization.ResumeIntervalMatrix
  N11Formalization.ResumeIntervalAugmented

/-- **Box 版 pinned coercivity**：H/G entry boxes + 计算出的同余行界
⇒ `(9/5000)q² ≤ Σ H0mat x x + 1468 p²`（full 9 维形式，pin 由 `sum_delete_pin` 处理）。 -/
theorem pinned_coercivity_box (pidx : Fin 9) (Λα : Fin 9 → Fin 9 → ℝ) (ρ θ : Fin 9 → ℝ)
    (N : Edge → Fin 4 → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point)
    (HB : Fin 8 → Fin 8 → RatInterval) (GB : Fin 8 → Fin 4 → RatInterval)
    (Cq : Matrix (Fin 8) (Fin 8) ℚ) (η : ℚ) {q p : ℝ}
    (hη : 0 < η) (hsym : ∀ i j, Λα i j = Λα j i)
    (hHbox : ∀ i j, RatInterval.Mem (HB i j)
        (H0mat Λα ρ (fun k => circleTangent (θ k)) (pidx.succAbove i) (pidx.succAbove j)))
    (hGbox : ∀ i a, RatInterval.Mem (GB i a)
        (Gmat anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N
          (pidx.succAbove i) a))
    (hrowBox : ∀ i, η + (∑ j, if j = i then 0 else
        (congruenceBox Cq (augmentedBox HB GB 734 (9 / 5000)) i j).abs.hi) ≤
      (congruenceBox Cq (augmentedBox HB GB 734 (9 / 5000)) i i).lo)
    (x : Fin 9 → ℝ) (hpin : x pidx = 0)
    (hq2 : q ^ 2 = ∑ i, x i ^ 2)
    (hp2 : p ^ 2 = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N x a) ^ 2) :
    (9 / 5000 : ℝ) * q ^ 2 ≤
      (∑ i, ∑ j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j * x i * x j) + 1468 * p ^ 2 := by
  have hHsym : ∀ i j, H0mat Λα ρ (fun k => circleTangent (θ k))
        (pidx.succAbove i) (pidx.succAbove j)
      = H0mat Λα ρ (fun k => circleTangent (θ k)) (pidx.succAbove j) (pidx.succAbove i) :=
    fun i j => H0mat_symm _ _ _ hsym _ _
  have hc := coercivity_of_boxes
    (fun i j => H0mat Λα ρ (fun k => circleTangent (θ k)) (pidx.succAbove i) (pidx.succAbove j))
    (fun i a => Gmat anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N
      (pidx.succAbove i) a)
    HB GB Cq 734 (9 / 5000) η hη hHsym hHbox hGbox hrowBox (fun k => x (pidx.succAbove k))
  have hx2 : (∑ k : Fin 8, x (pidx.succAbove k) ^ 2) = ∑ i, x i ^ 2 :=
    (sum_delete_pin pidx (fun i => x i ^ 2) (by simp [hpin])).symm
  have hHq : (∑ i : Fin 8, ∑ j : Fin 8, H0mat Λα ρ (fun k => circleTangent (θ k))
        (pidx.succAbove i) (pidx.succAbove j) * x (pidx.succAbove i) * x (pidx.succAbove j))
      = ∑ i, ∑ j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j * x i * x j :=
    (quadratic_delete_pin pidx (H0mat Λα ρ (fun k => circleTangent (θ k))) x hpin).symm
  have hGsum : (∑ a, (∑ k : Fin 8, Gmat anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N (pidx.succAbove k) a * x (pidx.succAbove k)) ^ 2)
      = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
          (fun k => circleTangent (θ k)) N x a) ^ 2 := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (∑ k : Fin 8, Gmat anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N (pidx.succAbove k) a * x (pidx.succAbove k))
        = GtX anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N x a := by
      rw [show (∑ k : Fin 8, Gmat anchorIncidence (edgeVector U C Z)
            (fun k => circleTangent (θ k)) N (pidx.succAbove k) a * x (pidx.succAbove k))
          = ∑ i, Gmat anchorIncidence (edgeVector U C Z)
              (fun k => circleTangent (θ k)) N i a * x i from
        (sum_delete_pin pidx (fun i => Gmat anchorIncidence (edgeVector U C Z)
          (fun k => circleTangent (θ k)) N i a * x i) (by simp [hpin])).symm]
      simp only [GtX]
    rw [h1]
  rw [hx2, hHq, hGsum, ← hq2, ← hp2] at hc
  linarith [hc]

/-- **Box 版 leaf**：`local_gain_actual_frobenius_leaf` 的证书层替换为源 H/G boxes +
有理同余行界；结论同为 `(Σx²)/100000 ≤ V2(U + disp θ x) − R*²`。 -/
theorem local_gain_actual_frobenius_leaf_box
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (θ x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ} (pidx : Fin 9) {Λα : Fin 9 → Fin 9 → ℝ}
    {Rstar : ℝ} (HB : Fin 8 → Fin 8 → RatInterval) (GB : Fin 8 → Fin 4 → RatInterval)
    (Cq : Matrix (Fin 8) (Fin 8) ℚ) (η : ℚ)
    (hα : ∀ e, 0 ≤ α e)
    (hgFrob : ∑ k : Fin 8, ∑ a, (Gmat anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N (pidx.succAbove k) a) ^ 2
        ≤ (15363 / 1000000 : ℝ) ^ 2)
    (hrow : ∀ e, Real.sqrt (∑ a, (N e a) ^ 2) ≤ (99 / 200) * α e)
    (hNcol : ∀ a, ∑ e, N e a = 0)
    (hNbal : ∀ a v, ∑ e, (N e a * incidence e v) • edgeVector U C Z e = 0)
    (hs : ∑ e, α e = 1)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = Rstar ^ 2)
    (hUeq : ∀ i, U i = circleMap (θ i))
    (hdiag : ∀ j, anchorWeight α j ≤ 2 / 25)
    (hr : Real.sqrt (∑ i, x i ^ 2) ≤ 729 / 50000)
    (hresp : ∀ W : Fin 9 → Point, Eform Λα W W = dirichletEnergy α W)
    (hpin : x pidx = 0) (hsym : ∀ i j, Λα i j = Λα j i)
    (hCfrob : ∑ i, ∑ j, (if i = pidx ∨ j = pidx then 0 else Cmat Λα θ i j) ^ 2
        ≤ (179 / 5000 : ℝ) ^ 2)
    (hFsq : ∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2 ≤ (429 / 50000 : ℝ) ^ 2)
    (hρ : ∀ i, 0 ≤ ρ i) (hfluxα : ∀ i, flux α U C Z i = ρ i • circleMap (θ i))
    (hη : 0 < η)
    (hHbox : ∀ i j, RatInterval.Mem (HB i j)
        (H0mat Λα ρ (fun k => circleTangent (θ k)) (pidx.succAbove i) (pidx.succAbove j)))
    (hGbox : ∀ i a, RatInterval.Mem (GB i a)
        (Gmat anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N
          (pidx.succAbove i) a))
    (hrowBox : ∀ i, η + (∑ j, if j = i then 0 else
        (congruenceBox Cq (augmentedBox HB GB 734 (9 / 5000)) i j).abs.hi) ≤
      (congruenceBox Cq (augmentedBox HB GB 734 (9 / 5000)) i i).lo) :
    (∑ i, x i ^ 2) / 100000 ≤ V2 (U + disp θ x) - Rstar ^ 2 := by
  have hpsd : ∀ W : Fin 9 → Point, 0 ≤ Eform Λα W W := by
    intro W
    rw [hresp W]
    exact le_csInf ⟨energy α W 0 0, ⟨(0, 0), rfl⟩⟩
      (by rintro q ⟨⟨C', Z'⟩, rfl⟩; exact energy_nonneg hα W C' Z')
  have hsx : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hgy : 0 ≤ ∑ a, (GtX anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N x a) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have hq0 : 0 ≤ Real.sqrt (∑ i, x i ^ 2) := Real.sqrt_nonneg _
  have hq2 : (Real.sqrt (∑ i, x i ^ 2)) ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hsx
  have hp0 : 0 ≤ Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N x a) ^ 2) := Real.sqrt_nonneg _
  have hp2 : (Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N x a) ^ 2)) ^ 2
      = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
          (fun k => circleTangent (θ k)) N x a) ^ 2 := Real.sq_sqrt hgy
  have hgate : 1468 * (99 / 200) * Real.sqrt (∑ a, (GtX anchorIncidence
      (edgeVector U C Z) (fun k => circleTangent (θ k)) N x a) ^ 2) < 1 := by
    have hp_le : Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N x a) ^ 2) ≤ (15363 / 1000000 : ℝ) * Real.sqrt (∑ i, x i ^ 2) :=
      gtX_norm_le_frobenius_pinned pidx
        (Gmat anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N) x
        (by norm_num) hgFrob hq0 hq2 hp0 hp2 hpin
    calc 1468 * (99 / 200) * Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
            (fun k => circleTangent (θ k)) N x a) ^ 2)
        ≤ 1468 * (99 / 200) * ((15363 / 1000000 : ℝ) * Real.sqrt (∑ i, x i ^ 2)) :=
          mul_le_mul_of_nonneg_left hp_le (by norm_num)
      _ ≤ 1468 * (99 / 200) * ((15363 / 1000000 : ℝ) * (729 / 50000)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hr (by norm_num)
      _ < 1 := by norm_num
  have hdir := directional_lower_actual_frobenius (α := α) (U := U) (C := C) (Z := Z)
    θ x ρ (N := N) (τ := 1468) (d := 2 / 25) (A := 429 / 50000) (B := 99 / 200)
    (Ccross := 179 / 5000) (Rstar := Rstar) (q := Real.sqrt (∑ i, x i ^ 2))
    (p := Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N x a) ^ 2)) pidx (Λα := Λα)
    hα (by norm_num) (by norm_num) hp0 (by norm_num) hgate hrow hNcol hNbal hs ha hl
    (hU_of_circle hUeq) hdiag hq0 hq2 hresp hpin hsym hpsd (by norm_num) hCfrob hFsq
    hρ hfluxα (by norm_num) hp2
  have hc := pinned_coercivity_box pidx Λα ρ θ N U C Z HB GB Cq η hη hsym hHbox hGbox
    hrowBox x hpin hq2 hp2
  have hdir' : (∑ i, ∑ j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j * x i * x j) / 2
      + 1468 * (Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
          (fun k => circleTangent (θ k)) N x a) ^ 2)) ^ 2
      - (179 / 5000) * (Real.sqrt (∑ i, x i ^ 2)) ^ 3
      - ((2 / 25) / 3) * (Real.sqrt (∑ i, x i ^ 2)) ^ 4
      - 1468 * ((99 / 200) * (2 / 25) + 429 / 50000)
        * Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
            (fun k => circleTangent (θ k)) N x a) ^ 2) * (Real.sqrt (∑ i, x i ^ 2)) ^ 2
      ≤ V2 (U + disp θ x) - Rstar ^ 2 := by
    linarith [hdir]
  have h := directional_to_local_gain (V2 (U + disp θ x) - Rstar ^ 2)
    (∑ i, ∑ j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j * x i * x j)
    (Real.sqrt (∑ i, x i ^ 2))
    (Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N x a) ^ 2)) hq0 hr hc hdir'
  rw [hq2] at h
  exact h

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.pinned_coercivity_box
#print axioms N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf_box
#check @N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf_box
