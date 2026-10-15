import N11Formalization.FlashLocalFrobeniusLeafBox

/-!
# FlashLocal — 120 局部叶承重链 · 第十九环：**G 证书由 box 计算**（all-rational 版本）

把 `local_gain_actual_frobenius_leaf_box` 里唯一非 box 的 G 常数（`hgFrob : ℝ` 的
`Σ_{k,a} Gmat(p k)a² ≤ (15363/10⁶)²`）换成**从 `GB` box 直接计算**的有理证书：

* `hgFrob_of_boxes`：`hGbox`（每个 pinned entry 的 `RatInterval.Mem`）给出
  `|Gmat(p k)a| ≤ (GB k a).abs.hi`，平方求和 ⇒
  `Σ_{k,a} Gmat² ≤ ↑(Σ_{k,a} (GB k a).abs.hi²)`；再用 ℚ 证书
  `hgNorm : Σ_{k,a} (GB k a).abs.hi² ≤ (15363/10⁶)²` 收尾。
* `local_gain_actual_frobenius_leaf_box_norm`：把上面代入冻结的 box leaf，
  得到所有证书都可由 box/有理数据检查的最终 leaf（结论不变）。

**未付**：`hrow/hNcol/hNbal/hs/ha/hl/hdiag/hr/hresp/hpin/hsym/hCfrob/hFsq/hρ/hfluxα`
与 `hHbox/hGbox/hrowBox/hgNorm/hη`（源身份与区间/有理证书）。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset Matrix
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

/-- **Box ⇒ pinned G Frobenius 证书**：逐 entry `Mem` + ℚ 范数界
⇒ `Σ_{k,a} Gmat(p k)a² ≤ (15363/10⁶)²`（ℝ 形式，供 gate 使用）。 -/
theorem hgFrob_of_boxes (s : Edge → Fin 9 → ℝ) (D : Edge → Point) (tang : Fin 9 → Point)
    (N : Edge → Fin 4 → ℝ) (pidx : Fin 9) (GB : Fin 8 → Fin 4 → RatInterval)
    (hgNorm : ∑ k : Fin 8, ∑ a, (GB k a).abs.hi ^ 2 ≤ (15363 / 1000000 : ℚ) ^ 2)
    (hGbox : ∀ i a, RatInterval.Mem (GB i a) (Gmat s D tang N (pidx.succAbove i) a)) :
    ∑ k : Fin 8, ∑ a, (Gmat s D tang N (pidx.succAbove k) a) ^ 2
      ≤ (15363 / 1000000 : ℝ) ^ 2 := by
  have hle : ∀ k a, (Gmat s D tang N (pidx.succAbove k) a) ^ 2
      ≤ ((GB k a).abs.hi : ℝ) ^ 2 := by
    intro k a
    have h1 : |Gmat s D tang N (pidx.succAbove k) a| ≤ ((GB k a).abs.hi : ℝ) :=
      RatInterval.mem_le_hi (RatInterval.abs_mem (hGbox k a))
    calc (Gmat s D tang N (pidx.succAbove k) a) ^ 2
        = |Gmat s D tang N (pidx.succAbove k) a| ^ 2 := (sq_abs _).symm
      _ ≤ ((GB k a).abs.hi : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc ∑ k : Fin 8, ∑ a, (Gmat s D tang N (pidx.succAbove k) a) ^ 2
      ≤ ∑ k : Fin 8, ∑ a, ((GB k a).abs.hi : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun a _ => hle k a))
    _ = ((∑ k : Fin 8, ∑ a, (GB k a).abs.hi ^ 2 : ℚ) : ℝ) := by
        simp only [Rat.cast_sum, Rat.cast_pow]
    _ ≤ (((15363 / 1000000 : ℚ) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hgNorm
    _ = (15363 / 1000000 : ℝ) ^ 2 := by norm_num

/-- **All-rational 版 leaf**：`hgFrob` 换成由 `GB` box 计算的 `hgNorm`（ℚ），其余与
`local_gain_actual_frobenius_leaf_box` 相同；结论 `(Σx²)/100000 ≤ V2(U + disp θ x) − R*²`。 -/
theorem local_gain_actual_frobenius_leaf_box_norm
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (θ x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ} (pidx : Fin 9) {Λα : Fin 9 → Fin 9 → ℝ}
    {Rstar : ℝ} (HB : Fin 8 → Fin 8 → RatInterval) (GB : Fin 8 → Fin 4 → RatInterval)
    (Cq : Matrix (Fin 8) (Fin 8) ℚ) (η : ℚ)
    (hα : ∀ e, 0 ≤ α e)
    (hgNorm : ∑ k : Fin 8, ∑ a, (GB k a).abs.hi ^ 2 ≤ (15363 / 1000000 : ℚ) ^ 2)
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
    (∑ i, x i ^ 2) / 100000 ≤ V2 (U + disp θ x) - Rstar ^ 2 :=
  local_gain_actual_frobenius_leaf_box (α := α) (U := U) (C := C) (Z := Z) θ x ρ (N := N)
    (Rstar := Rstar) pidx (Λα := Λα) HB GB Cq η hα
    (hgFrob_of_boxes anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N
      pidx GB hgNorm hGbox)
    hrow hNcol hNbal hs ha hl hUeq hdiag hr hresp hpin hsym hCfrob hFsq hρ hfluxα
    hη hHbox hGbox hrowBox

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.hgFrob_of_boxes
#print axioms N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf_box_norm
#check @N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf_box_norm
