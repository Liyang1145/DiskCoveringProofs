import N11Formalization.FlashLocalFrobeniusLeafBoxNorm

/-!
# FlashLocal — 120 局部叶承重链 · 第二十环：**统一 entry enclosure → norm 证书核**

Lead 2026-09-30：源 A/Ccross/B/d 的证书应统一走"per-entry 有理区间包含 → 范数证书"，
不为每个常数特写新核。本件给统一核 + 四个实际消费者：

* 核：`sum_sq_le_of_boxes`（1 指标：`Mem (B i) (x i)` ⇒ `Σ x_i² ≤ ↑(Σ (B_i).abs.hi²)`）、
  `matrix_frob_sq_le_of_boxes`（2 指标，由 1 指标经 `Fintype.sum_prod_type` 得到）、
  `sum_ite_pin_sq_eq`（pin：`Σ_ij (if i=p∨j=p then 0 else f_ij)² = Σ_{k,l:Fin n} f(p k)(p l)²`，
  只用 `sum_delete_pin`+`Fin.succAbove_ne`）；
* **A** `hFsq_of_boxes`：flux 每个分量 box ⇒ `Σ_a (frob F_a)² ≤ (429/50000)²`；
* **Ccross** `hCfrob_of_boxes`：pinned Cmat 8×8 entry box ⇒ 指标形式 `Σ(if…)² ≤ (179/5000)²`；
* **B** `hrow_of_boxes`：N entry box + α **下界** box + `sqrtHi` 有理证书
  ⇒ `∀ e, √(Σ_a N_ea²) ≤ (99/200)·α_e`（复用 `Interval.Sqrt.sqrt_le_sqrtHi`）；
* **d** `hdiag_of_boxes`：α **上界** box ⇒ `∀ j, anchorWeight α j ≤ 2/25`。

**未付**：这些 box 的 `Mem`（源 N/α/flux/Cmat 的实际数值包含）与有理证书本身。
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

/-! ## 统一核 -/

/-- **1 指标核**：逐 entry 有理区间包含 ⇒ 平方和的 sharp box 界（RHS 是 ℚ 和的 cast）。 -/
theorem sum_sq_le_of_boxes {ι : Type*} [Fintype ι] (x : ι → ℝ) (B : ι → RatInterval)
    (h : ∀ i, RatInterval.Mem (B i) (x i)) :
    ∑ i, x i ^ 2 ≤ ((∑ i, (B i).abs.hi ^ 2 : ℚ) : ℝ) := by
  have hle : ∀ i, x i ^ 2 ≤ ((B i).abs.hi : ℝ) ^ 2 := by
    intro i
    have h1 : |x i| ≤ ((B i).abs.hi : ℝ) :=
      RatInterval.mem_le_hi (RatInterval.abs_mem (h i))
    calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
      _ ≤ ((B i).abs.hi : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc ∑ i, x i ^ 2 ≤ ∑ i, ((B i).abs.hi : ℝ) ^ 2 := Finset.sum_le_sum (fun i _ => hle i)
    _ = ((∑ i, (B i).abs.hi ^ 2 : ℚ) : ℝ) := by simp only [Rat.cast_sum, Rat.cast_pow]

/-- **1 指标核（带有理上界）**：`Σ (B_i).abs.hi² ≤ C²` ⇒ `Σ x_i² ≤ C²`。 -/
theorem sum_sq_le_of_boxes_of_bound {ι : Type*} [Fintype ι] (x : ι → ℝ) (B : ι → RatInterval)
    (h : ∀ i, RatInterval.Mem (B i) (x i)) {C : ℚ}
    (hC : ∑ i, (B i).abs.hi ^ 2 ≤ C ^ 2) :
    ∑ i, x i ^ 2 ≤ (C : ℝ) ^ 2 := by
  calc ∑ i, x i ^ 2 ≤ ((∑ i, (B i).abs.hi ^ 2 : ℚ) : ℝ) := sum_sq_le_of_boxes x B h
    _ ≤ ((C ^ 2 : ℚ) : ℝ) := by exact_mod_cast hC
    _ = (C : ℝ) ^ 2 := by rw [Rat.cast_pow]

/-- **2 指标核**（Frobenius）：由 1 指标核经 `Fintype.sum_prod_type` 得到。 -/
theorem matrix_frob_sq_le_of_boxes {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℝ) (B : ι → κ → RatInterval) (h : ∀ i j, RatInterval.Mem (B i j) (M i j)) :
    ∑ i, ∑ j, M i j ^ 2 ≤ ((∑ i, ∑ j, (B i j).abs.hi ^ 2 : ℚ) : ℝ) := by
  have h1 := sum_sq_le_of_boxes (fun p : ι × κ => M p.1 p.2) (fun p : ι × κ => B p.1 p.2)
    (fun p => h p.1 p.2)
  simpa only [Fintype.sum_prod_type] using h1

/-- **pin 重标**：指标形式（`p` 行列为 0）的双重平方和 = `Fin n` 上的双重和。
只用 `sum_delete_pin`（两次）与 `Fin.succAbove_ne`，不重复 lead 的 Fin8 表。 -/
theorem sum_ite_pin_sq_eq {n : ℕ} (p : Fin (n + 1)) (f : Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ i, ∑ j, (if i = p ∨ j = p then 0 else f i j) ^ 2)
      = ∑ k : Fin n, ∑ l : Fin n, f (p.succAbove k) (p.succAbove l) ^ 2 := by
  rw [sum_delete_pin p (fun i => ∑ j, (if i = p ∨ j = p then 0 else f i j) ^ 2)
    (by simp)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [sum_delete_pin p
    (fun j => (if p.succAbove k = p ∨ j = p then 0 else f (p.succAbove k) j) ^ 2)
    (by simp)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [if_neg]
  rintro (h | h)
  · exact Fin.succAbove_ne p k h
  · exact Fin.succAbove_ne p l h

/-! ## A：flux 分量 box ⇒ `hFsq` -/

/-- **A 证书**：flux 每个分量 `(F_a j).ofLp c` 的 box ⇒
`Σ_a (frob F_a)² ≤ (429/50000)²`。 -/
theorem hFsq_of_boxes (N : Edge → Fin 4 → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point)
    (FB : Fin 4 → Fin 9 → Fin 2 → RatInterval)
    (hFB : ∀ a j c, RatInterval.Mem (FB a j c) ((flux (fun e => N e a) U C Z j).ofLp c))
    (hcert : ∑ a : Fin 4, ∑ j : Fin 9, ∑ c : Fin 2, (FB a j c).abs.hi ^ 2
        ≤ (429 / 50000 : ℚ) ^ 2) :
    ∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2 ≤ (429 / 50000 : ℝ) ^ 2 := by
  have hdec : ∀ a, (frob (flux (fun e => N e a) U C Z)) ^ 2
      = ∑ j, ∑ c, ((flux (fun e => N e a) U C Z j).ofLp c) ^ 2 := by
    intro a
    rw [frob, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  have hbound : ∀ a j c, ((flux (fun e => N e a) U C Z j).ofLp c) ^ 2
      ≤ ((FB a j c).abs.hi : ℝ) ^ 2 := by
    intro a j c
    have h1 : |((flux (fun e => N e a) U C Z j).ofLp c)| ≤ ((FB a j c).abs.hi : ℝ) :=
      RatInterval.mem_le_hi (RatInterval.abs_mem (hFB a j c))
    calc ((flux (fun e => N e a) U C Z j).ofLp c) ^ 2
        = |((flux (fun e => N e a) U C Z j).ofLp c)| ^ 2 := (sq_abs _).symm
      _ ≤ ((FB a j c).abs.hi : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc ∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2
      = ∑ a, ∑ j, ∑ c, ((flux (fun e => N e a) U C Z j).ofLp c) ^ 2 :=
        Finset.sum_congr rfl (fun a _ => hdec a)
    _ ≤ ∑ a, ∑ j, ∑ c, ((FB a j c).abs.hi : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun j _ =>
          Finset.sum_le_sum (fun c _ => hbound a j c)))
    _ = ((∑ a : Fin 4, ∑ j : Fin 9, ∑ c : Fin 2, (FB a j c).abs.hi ^ 2 : ℚ) : ℝ) := by
        simp only [Rat.cast_sum, Rat.cast_pow]
    _ ≤ (((429 / 50000 : ℚ) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hcert
    _ = (429 / 50000 : ℝ) ^ 2 := by norm_num

/-! ## Ccross：pinned Cmat 8×8 entry box ⇒ `hCfrob` -/

/-- **Ccross 证书**：pinned 8×8 Cmat entry box + ℚ 范数界 ⇒ 指标形式 `hCfrob`。 -/
theorem hCfrob_of_boxes (pidx : Fin 9) (Λα : Fin 9 → Fin 9 → ℝ) (θ : Fin 9 → ℝ)
    (CB : Fin 8 → Fin 8 → RatInterval)
    (hCB : ∀ k l, RatInterval.Mem (CB k l)
        (Cmat Λα θ (pidx.succAbove k) (pidx.succAbove l)))
    (hcert : ∑ k : Fin 8, ∑ l : Fin 8, (CB k l).abs.hi ^ 2 ≤ (179 / 5000 : ℚ) ^ 2) :
    ∑ i, ∑ j, (if i = pidx ∨ j = pidx then 0 else Cmat Λα θ i j) ^ 2
      ≤ (179 / 5000 : ℝ) ^ 2 := by
  rw [sum_ite_pin_sq_eq pidx (fun i j => Cmat Λα θ i j)]
  calc ∑ k : Fin 8, ∑ l : Fin 8, Cmat Λα θ (pidx.succAbove k) (pidx.succAbove l) ^ 2
      ≤ ((∑ k : Fin 8, ∑ l : Fin 8, (CB k l).abs.hi ^ 2 : ℚ) : ℝ) :=
        matrix_frob_sq_le_of_boxes _ CB hCB
    _ ≤ (((179 / 5000 : ℚ) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hcert
    _ = (179 / 5000 : ℝ) ^ 2 := by norm_num

/-! ## B：N entry box + α 下界 ⇒ `hrow` -/

/-- **B 证书**：`N_ea` entry box + `α_e` 下界 box + `sqrtHi` 有理证书
⇒ `√(Σ_a N_ea²) ≤ (99/200)·α_e`。 -/
theorem hrow_of_boxes (N : Edge → Fin 4 → ℝ) (α : Edge → ℝ)
    (NB : Edge → Fin 4 → RatInterval) (AB : Edge → RatInterval)
    (hNB : ∀ e a, RatInterval.Mem (NB e a) (N e a))
    (hAB : ∀ e, RatInterval.Mem (AB e) (α e))
    (hcert : ∀ e, RatInterval.sqrtHi (∑ a, (NB e a).abs.hi ^ 2)
        ≤ (99 / 200 : ℚ) * (AB e).lo) :
    ∀ e, Real.sqrt (∑ a, (N e a) ^ 2) ≤ (99 / 200) * α e := by
  intro e
  have hsharp : ∑ a, (N e a) ^ 2 ≤ ((∑ a, (NB e a).abs.hi ^ 2 : ℚ) : ℝ) :=
    sum_sq_le_of_boxes (fun a => N e a) (fun a => NB e a) (fun a => hNB e a)
  calc Real.sqrt (∑ a, (N e a) ^ 2)
      ≤ Real.sqrt (((∑ a, (NB e a).abs.hi ^ 2 : ℚ)) : ℝ) := Real.sqrt_le_sqrt hsharp
    _ ≤ ((RatInterval.sqrtHi (∑ a, (NB e a).abs.hi ^ 2) : ℚ) : ℝ) :=
        RatInterval.sqrt_le_sqrtHi _
    _ ≤ (((99 / 200 : ℚ) * (AB e).lo : ℚ) : ℝ) := by exact_mod_cast hcert e
    _ ≤ (99 / 200) * α e := by
        have h := RatInterval.mem_lo_le (hAB e)
        have hcast : (((99 / 200 : ℚ) * (AB e).lo : ℚ) : ℝ)
            = ((99 / 200 : ℚ) : ℝ) * ((AB e).lo : ℝ) := by
          rw [Rat.cast_mul]
        have h99 : ((99 / 200 : ℚ) : ℝ) = (99 / 200 : ℝ) := by norm_num
        rw [hcast, h99]
        exact mul_le_mul_of_nonneg_left h (by norm_num)

/-! ## d：α 上界 box ⇒ `hdiag` -/

/-- **d 证书**：`α_e` 上界 box + ℚ 行和界 ⇒ `anchorWeight α j ≤ 2/25`。 -/
theorem hdiag_of_boxes (α : Edge → ℝ) (AB : Edge → RatInterval)
    (hAB : ∀ e, RatInterval.Mem (AB e) (α e))
    (hcert : ∀ j : Fin 9, (∑ i : Fin 9, ∑ side : Fin 2,
        if anchorIndex i side = j then (AB (.inl (i, side))).hi else 0) ≤ (2 / 25 : ℚ)) :
    ∀ j, anchorWeight α j ≤ 2 / 25 := by
  intro j
  have hle : ∀ i side, (if anchorIndex i side = j then α (.inl (i, side)) else 0)
      ≤ (if anchorIndex i side = j then ((AB (.inl (i, side))).hi : ℝ) else 0) := by
    intro i side
    by_cases h : anchorIndex i side = j
    · rw [if_pos h, if_pos h]
      exact RatInterval.mem_le_hi (hAB (.inl (i, side)))
    · rw [if_neg h, if_neg h]
  calc anchorWeight α j
      ≤ ((∑ i : Fin 9, ∑ side : Fin 2,
          if anchorIndex i side = j then (AB (.inl (i, side))).hi else 0 : ℚ) : ℝ) := by
        unfold anchorWeight
        calc ∑ i, ∑ side, (if anchorIndex i side = j then α (.inl (i, side)) else 0)
            ≤ ∑ i, ∑ side,
                (if anchorIndex i side = j then ((AB (.inl (i, side))).hi : ℝ) else 0) :=
              Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun side _ => hle i side))
          _ = ((∑ i : Fin 9, ∑ side : Fin 2,
                if anchorIndex i side = j then (AB (.inl (i, side))).hi else 0 : ℚ) : ℝ) := by
              simp only [Rat.cast_sum, apply_ite, Rat.cast_zero]
    _ ≤ (2 / 25 : ℝ) := by
        have h2 : ((2 / 25 : ℚ) : ℝ) = (2 / 25 : ℝ) := by norm_num
        have hcast : ((∑ i : Fin 9, ∑ side : Fin 2,
            if anchorIndex i side = j then (AB (.inl (i, side))).hi else 0 : ℚ) : ℝ)
            ≤ ((2 / 25 : ℚ) : ℝ) := by exact_mod_cast hcert j
        rw [h2] at hcast
        exact hcast

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.sum_sq_le_of_boxes
#print axioms N11Formalization.FlashLocal.matrix_frob_sq_le_of_boxes
#print axioms N11Formalization.FlashLocal.sum_ite_pin_sq_eq
#print axioms N11Formalization.FlashLocal.hFsq_of_boxes
#print axioms N11Formalization.FlashLocal.hCfrob_of_boxes
#print axioms N11Formalization.FlashLocal.hrow_of_boxes
#print axioms N11Formalization.FlashLocal.hdiag_of_boxes
