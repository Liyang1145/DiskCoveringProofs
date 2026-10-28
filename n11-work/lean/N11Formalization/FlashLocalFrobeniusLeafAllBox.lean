import N11Formalization.FlashLocalFrobeniusEnclosure

/-!
# FlashLocal — 120 局部叶承重链 · 第二十一环：**all-box leaf**（证书层全区间化）

把 `FrobeniusEnclosure` 的统一核用于 `local_gain_actual_frobenius_leaf_box_norm`，
使该 leaf 的**全部证书前件**变成"逐 entry `RatInterval.Mem` + ℚ 证书"：

| 原前件 | 替换为 |
|---|---|
| `hα : ∀e, 0≤α e` | `AB` 的 `lo ≥ 0` + `Mem`（`hα0`） |
| `hgFrob` | `GB` box + `hgNorm`（`hgFrob_of_boxes`） |
| `hFsq` | `FB` 分量 box + `hFsqCert`（`hFsq_of_boxes`） |
| `hCfrob` | `CB` 8×8 box + `hCcert`（`hCfrob_of_boxes`） |
| `hrow` | `NB`/`AB` box + `sqrtHi` 证书 `hBcert`（`hrow_of_boxes`） |
| `hdiag` | `AB` 上界 + `hDcert`（`hdiag_of_boxes`） |

结论不变：`(Σ i, x_i²)/100000 ≤ V2(U + disp θ x) − R*²`。
仍显式未付：源身份（`hNcol/hNbal/hs/ha/hl/hUeq/hr/hresp/hpin/hsym/hρ/hfluxα`）与
各 `Mem`/ℚ 证书本身（源 N/α/flux/Cmat/G/H 的实际数值包含）。
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

/-- **All-box leaf**：证书层全部由区间/有理数据供给，其余前件显式保留。 -/
theorem local_gain_actual_frobenius_leaf_all_box
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (θ x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ} (pidx : Fin 9) {Λα : Fin 9 → Fin 9 → ℝ}
    {Rstar : ℝ}
    (HB : Fin 8 → Fin 8 → RatInterval) (GB : Fin 8 → Fin 4 → RatInterval)
    (NB : Edge → Fin 4 → RatInterval) (AB : Edge → RatInterval)
    (FB : Fin 4 → Fin 9 → Fin 2 → RatInterval)
    (CB : Fin 8 → Fin 8 → RatInterval)
    (Cq : Matrix (Fin 8) (Fin 8) ℚ) (η : ℚ)
    -- 源身份（仍显式）
    (hNcol : ∀ a, ∑ e, N e a = 0)
    (hNbal : ∀ a v, ∑ e, (N e a * incidence e v) • edgeVector U C Z e = 0)
    (hs : ∑ e, α e = 1)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = Rstar ^ 2)
    (hUeq : ∀ i, U i = circleMap (θ i))
    (hr : Real.sqrt (∑ i, x i ^ 2) ≤ 729 / 50000)
    (hresp : ∀ W : Fin 9 → Point, Eform Λα W W = dirichletEnergy α W)
    (hpin : x pidx = 0) (hsym : ∀ i j, Λα i j = Λα j i)
    (hρ : ∀ i, 0 ≤ ρ i) (hfluxα : ∀ i, flux α U C Z i = ρ i • circleMap (θ i))
    -- 逐 entry 包含（源数值 membership；未付）
    (hNB : ∀ e a, RatInterval.Mem (NB e a) (N e a))
    (hAB : ∀ e, RatInterval.Mem (AB e) (α e))
    (hFB : ∀ a j c, RatInterval.Mem (FB a j c)
        ((flux (fun e => N e a) U C Z j).ofLp c))
    (hCB : ∀ k l, RatInterval.Mem (CB k l)
        (Cmat Λα θ (pidx.succAbove k) (pidx.succAbove l)))
    (hGB : ∀ k a, RatInterval.Mem (GB k a)
        (Gmat anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N
          (pidx.succAbove k) a))
    (hHB : ∀ k l, RatInterval.Mem (HB k l)
        (H0mat Λα ρ (fun k => circleTangent (θ k)) (pidx.succAbove k) (pidx.succAbove l)))
    -- ℚ 证书（源区间计算可检查）
    (hα0 : ∀ e, 0 ≤ (AB e).lo)
    (hgNorm : ∑ k : Fin 8, ∑ a, (GB k a).abs.hi ^ 2 ≤ (15363 / 1000000 : ℚ) ^ 2)
    (hFsqCert : ∑ a : Fin 4, ∑ j : Fin 9, ∑ c : Fin 2, (FB a j c).abs.hi ^ 2
        ≤ (429 / 50000 : ℚ) ^ 2)
    (hCcert : ∑ k : Fin 8, ∑ l : Fin 8, (CB k l).abs.hi ^ 2 ≤ (179 / 5000 : ℚ) ^ 2)
    (hBcert : ∀ e, RatInterval.sqrtHi (∑ a, (NB e a).abs.hi ^ 2)
        ≤ (99 / 200 : ℚ) * (AB e).lo)
    (hDcert : ∀ j : Fin 9, (∑ i : Fin 9, ∑ side : Fin 2,
        if anchorIndex i side = j then (AB (.inl (i, side))).hi else 0) ≤ (2 / 25 : ℚ))
    (hη : 0 < η)
    (hrowBox : ∀ i, η + (∑ j, if j = i then 0 else
        (congruenceBox Cq (augmentedBox HB GB 734 (9 / 5000)) i j).abs.hi) ≤
      (congruenceBox Cq (augmentedBox HB GB 734 (9 / 5000)) i i).lo) :
    (∑ i, x i ^ 2) / 100000 ≤ V2 (U + disp θ x) - Rstar ^ 2 := by
  have hα : ∀ e, 0 ≤ α e := fun e =>
    le_trans (by exact_mod_cast hα0 e) (RatInterval.mem_lo_le (hAB e))
  have hFsq := hFsq_of_boxes N U C Z FB hFB hFsqCert
  have hCfrob := hCfrob_of_boxes pidx Λα θ CB hCB hCcert
  have hrow := hrow_of_boxes N α NB AB hNB hAB hBcert
  have hdiag := hdiag_of_boxes α AB hAB hDcert
  exact local_gain_actual_frobenius_leaf_box_norm (α := α) (U := U) (C := C) (Z := Z)
    θ x ρ (N := N) (Rstar := Rstar) pidx (Λα := Λα) HB GB Cq η
    hα hgNorm hrow hNcol hNbal hs ha hl hUeq hdiag hr hresp hpin hsym hCfrob hFsq
    hρ hfluxα hη hHB hGB hrowBox

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf_all_box
#check @N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf_all_box
