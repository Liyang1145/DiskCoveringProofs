/-
  **FlashCosineCore — the leaf-INDEPENDENT semantic core of the C911 cosine-energy leaves.**

  WHAT THIS IS.  The cone's C921 chain carries "GAP CARRIED (gap (3)): the semantic identity of
  the recorded source quantities" -- layer (b)/(c) of `C921Sem.LeafSemBound`: whole-cell affine
  cos-minorants `1 - cos z >= s*z + c` plus their rational mixture.  This file supplies the
  MINORANT MACHINERY in a form that is checked by the kernel on RATIONAL data only:

    * `cos_sub_cos_le_of_sin_le` / `le_cos_sub_cos_of_le_sin`
        the mean-value inequalities behind every tangent/chord minorant;
    * `minorant_of_sin_le` / `minorant_of_le_sin`
        the two certificate shapes: if `sin <= s` on the cell then `z |-> 1 - cos z - s z` is
        antitone, so `c = g(B)` (shape (a)); if `s <= sin` on the cell then `g` is monotone
        increasing, so `c = g(A)` (shape (b)).  NO critical-point (Fermat / asin-candidate)
        enumeration is used and no numerical minimisation is assumed;
    * `sin_le_sin_of_mem_arc_inc` / `arc_inc_le_sin` / `sin_le_sin_of_mem_arc_dec` /
        `arc_dec_le_sin` -- sin is monotone on ONE arc, so the cell inequalities
        `sin <= s` / `s <= sin` reduce to the two rational endpoint brackets of the arc;
        the `arc_*_of_nonneg/nonpos` helpers turn those into closed RATIONAL comparisons
        against the 20-digit π brackets `RatInterval.piLo/piHi`;
    * `lp_step9` -- LP weak duality over the Fin-9 chart (closed 9-simplex + DBM rows),
        dual `lam >= 0` supplied as data;
    * `partial_energy_le` -- a leaf-indexed partial sum extends to the full 36-pair cosine
        energy using `w >= 0` and `1 - cos >= 0` ONLY (no numerical assumption).

  CALIBER.  object: one energy leaf's cell (z = angular differences of the 9-point chart);
  units: length^2 (unit-disk radius 1); normalization: `y >= 0`, `sum y = 1` (Fin 9, the
  SOURCE domain; the Fin-8 `sum <= 1` form is a separate bridge and is NOT used here);
  threshold-free (the numbers `T`/`thresh` live in the leaf file).

  DISCIPLINE.  no `sorry`, no custom `axiom`, no `native_decide`, no `#eval`.
-/
import Mathlib
import N11Formalization.IntervalsHighLag
import N11Formalization.Interval.Phase

namespace N11Formalization.FlashCosine

open Finset

/-! ## 0. 2π-移位（把任意弧拉回主值窗口） -/

theorem sin_sub_two_pi_shift (x : ℝ) (m : ℤ) :
    Real.sin (x - (m : ℝ) * (2 * Real.pi)) = Real.sin x := by
  have h := N11Formalization.RatInterval.sin_add_two_pi_shift (x - (m : ℝ) * (2 * Real.pi)) m
  have harg : x - (m : ℝ) * (2 * Real.pi) + (m : ℝ) * (2 * Real.pi) = x := by ring
  rw [harg] at h
  exact h.symm

/-! ## 1. 中值不等式（切线/弦型 minorant 的解析核） -/

/-- **`cos` 的差商界（上）**：`sin <= s` 于 `[x,y]` ⟹ `cos x - cos y <= s(y-x)`。 -/
theorem cos_sub_cos_le_of_sin_le {x y s : ℝ} (hxy : x ≤ y)
    (h : ∀ t ∈ Set.Icc x y, Real.sin t ≤ s) :
    Real.cos x - Real.cos y ≤ s * (y - x) := by
  rcases lt_or_eq_of_le hxy with hlt | heq
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope Real.cos hlt Real.continuousOn_cos
      (fun t _ => Real.differentiableAt_cos.differentiableWithinAt)
    rw [Real.deriv_cos] at hcd
    have hsc : Real.sin c ≤ s := h c ⟨hc.1.le, hc.2.le⟩
    have hba : 0 < y - x := by linarith
    have h1 : Real.cos y - Real.cos x = -Real.sin c * (y - x) := by
      rw [hcd]
      field_simp
    linarith [mul_le_mul_of_nonneg_right hsc hba.le]
  · rw [heq]; ring_nf; positivity

/-- **`cos` 的差商界（下）**：`s <= sin` 于 `[x,y]` ⟹ `s(y-x) <= cos x - cos y`。 -/
theorem le_cos_sub_cos_of_le_sin {x y s : ℝ} (hxy : x ≤ y)
    (h : ∀ t ∈ Set.Icc x y, s ≤ Real.sin t) :
    s * (y - x) ≤ Real.cos x - Real.cos y := by
  rcases lt_or_eq_of_le hxy with hlt | heq
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope Real.cos hlt Real.continuousOn_cos
      (fun t _ => Real.differentiableAt_cos.differentiableWithinAt)
    rw [Real.deriv_cos] at hcd
    have hsc : s ≤ Real.sin c := h c ⟨hc.1.le, hc.2.le⟩
    have hba : 0 < y - x := by linarith
    have h1 : Real.cos y - Real.cos x = -Real.sin c * (y - x) := by
      rw [hcd]
      field_simp
    linarith [mul_le_mul_of_nonneg_right hsc hba.le]
  · rw [heq]; ring_nf; positivity

/-! ## 2. 两种证书形状（无 Fermat、无 asin 候选枚举） -/

/-- **形状 (a)**：`sin <= s` 于全胞 ⟹ `g = 1 - cos - s·id` 递减 ⟹ 下确界在右端点。 -/
theorem minorant_of_sin_le {a b s c : ℝ}
    (hsin : ∀ t ∈ Set.Icc a b, Real.sin t ≤ s) (hc : c ≤ 1 - Real.cos b - s * b) :
    ∀ z ∈ Set.Icc a b, s * z + c ≤ 1 - Real.cos z := by
  intro z hz
  have h1 : Real.cos z - Real.cos b ≤ s * (b - z) :=
    cos_sub_cos_le_of_sin_le hz.2 (fun t ht => hsin t ⟨le_trans hz.1 ht.1, ht.2⟩)
  linarith

/-- **形状 (b)**：`s <= sin` 于全胞 ⟹ `g` 递增 ⟹ 下确界在左端点。 -/
theorem minorant_of_le_sin {a b s c : ℝ}
    (hsin : ∀ t ∈ Set.Icc a b, s ≤ Real.sin t) (hc : c ≤ 1 - Real.cos a - s * a) :
    ∀ z ∈ Set.Icc a b, s * z + c ≤ 1 - Real.cos z := by
  intro z hz
  have h1 : s * (z - a) ≤ Real.cos a - Real.cos z :=
    le_cos_sub_cos_of_le_sin hz.1 (fun t ht => hsin t ⟨ht.1, le_trans ht.2 hz.2⟩)
  linarith

/-- **仿射函数在全胞非负**：只需两端点非负（无 MVT、无单调性）。 -/
theorem affine_nonneg_of_endpoints {a b s c z : ℝ} (hz : z ∈ Set.Icc a b)
    (ha : 0 ≤ s * a + c) (hb : 0 ≤ s * b + c) : 0 ≤ s * z + c := by
  rcases le_total 0 s with hs | hs
  · nlinarith [hs, hz.1, ha]
  · nlinarith [hs, hz.2, hb]
/-! ## 3. 单一单调弧上的四个 sin 夹逼 -/

/-- 上升弧：`sin` 在 `[a,b]` 上递增 ⟹ `sin z <= sin b`。 -/
theorem sin_le_sin_of_mem_arc_inc {a b : ℝ} {m : ℤ} {z : ℝ}
    (ha : -(Real.pi / 2) ≤ a - (m : ℝ) * (2 * Real.pi))
    (hb : b - (m : ℝ) * (2 * Real.pi) ≤ Real.pi / 2)
    (hz : z ∈ Set.Icc a b) : Real.sin z ≤ Real.sin b := by
  have hz1 : z - (m : ℝ) * (2 * Real.pi) ≤ b - (m : ℝ) * (2 * Real.pi) := by linarith [hz.2]
  have hz2 : -(Real.pi / 2) ≤ z - (m : ℝ) * (2 * Real.pi) := by linarith [hz.1, ha]
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two hz2 hb hz1
  rwa [sin_sub_two_pi_shift z m, sin_sub_two_pi_shift b m] at h

/-- 上升弧：`sin` 在 `[a,b]` 上递增 ⟹ `sin a <= sin z`。 -/
theorem arc_inc_le_sin {a b : ℝ} {m : ℤ} {z : ℝ}
    (ha : -(Real.pi / 2) ≤ a - (m : ℝ) * (2 * Real.pi))
    (hb : b - (m : ℝ) * (2 * Real.pi) ≤ Real.pi / 2)
    (hz : z ∈ Set.Icc a b) : Real.sin a ≤ Real.sin z := by
  have hz1 : a - (m : ℝ) * (2 * Real.pi) ≤ z - (m : ℝ) * (2 * Real.pi) := by linarith [hz.1]
  have hz2 : z - (m : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := by linarith [hz.2, hb]
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two ha hz2 hz1
  rwa [sin_sub_two_pi_shift a m, sin_sub_two_pi_shift z m] at h

/-- 下降弧：`sin` 在 `[a,b]` 上递减 ⟹ `sin z <= sin a`。 -/
theorem sin_le_sin_of_mem_arc_dec {a b : ℝ} {m : ℤ} {z : ℝ}
    (ha : Real.pi / 2 ≤ a - (m : ℝ) * (2 * Real.pi))
    (hb : b - (m : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2)
    (hz : z ∈ Set.Icc a b) : Real.sin z ≤ Real.sin a := by
  have hz1 : a - (m : ℝ) * (2 * Real.pi) ≤ z - (m : ℝ) * (2 * Real.pi) := by linarith [hz.1]
  have hz2 : z - (m : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := by linarith [hz.2, hb]
  have hzw : Real.sin z = Real.sin (Real.pi - (z - (m : ℝ) * (2 * Real.pi))) := by
    rw [← sin_sub_two_pi_shift z m]
    exact (Real.sin_pi_sub _).symm
  have haw : Real.sin a = Real.sin (Real.pi - (a - (m : ℝ) * (2 * Real.pi))) := by
    rw [← sin_sub_two_pi_shift a m]
    exact (Real.sin_pi_sub _).symm
  rw [hzw, haw]
  refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ ?_
  · linarith [hz2]
  · linarith [ha]
  · linarith [hz1]

/-- 下降弧：`sin` 在 `[a,b]` 上递减 ⟹ `sin b <= sin z`。 -/
theorem arc_dec_le_sin {a b : ℝ} {m : ℤ} {z : ℝ}
    (ha : Real.pi / 2 ≤ a - (m : ℝ) * (2 * Real.pi))
    (hb : b - (m : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2)
    (hz : z ∈ Set.Icc a b) : Real.sin b ≤ Real.sin z := by
  have hz1 : z - (m : ℝ) * (2 * Real.pi) ≤ b - (m : ℝ) * (2 * Real.pi) := by linarith [hz.2]
  have hz2 : Real.pi / 2 ≤ z - (m : ℝ) * (2 * Real.pi) := by linarith [hz.1, ha]
  have hzw : Real.sin z = Real.sin (Real.pi - (z - (m : ℝ) * (2 * Real.pi))) := by
    rw [← sin_sub_two_pi_shift z m]
    exact (Real.sin_pi_sub _).symm
  have hbw : Real.sin b = Real.sin (Real.pi - (b - (m : ℝ) * (2 * Real.pi))) := by
    rw [← sin_sub_two_pi_shift b m]
    exact (Real.sin_pi_sub _).symm
  rw [hzw, hbw]
  refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ ?_
  · linarith [hb]
  · linarith [hz2]
  · linarith [hz1]

/-! ## 5. LP 弱对偶步（Fin 9 chart，行 `A y <= b`，`y` 闭 9-单纯形） -/

/-- **LP 步（Fin 9）**：`lam >= 0`、逐行 `A y <= b`、`y >= 0`、`sum y = 1`、且
`rmin <= c q + (Aᵀlam) q` 对每个 `q` ⟹ `sum q c q * y q >= rmin - lam ⬝ b`。
纯代数：`c·y = (c + Aᵀlam)·y - lam·(Ay)`。 -/
theorem lp_step9 {m : ℕ} (A : Fin m → Fin 9 → ℚ) (bV : Fin m → ℚ) (lam : Fin m → ℚ)
    (c : Fin 9 → ℝ) (rmin : ℝ) (y : Fin 9 → ℝ)
    (hlam : ∀ j, 0 ≤ (lam j : ℝ))
    (hdom : ∀ j, (∑ q, (A j q : ℝ) * y q) ≤ (bV j : ℝ))
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hr : ∀ q, rmin ≤ c q + ∑ j, (lam j : ℝ) * (A j q : ℝ)) :
    rmin - ∑ j, (lam j : ℝ) * (bV j : ℝ) ≤ ∑ q, c q * y q := by
  have h1 : rmin ≤ ∑ q, (c q + ∑ j, (lam j : ℝ) * (A j q : ℝ)) * y q := by
    calc rmin = ∑ q, rmin * y q := by rw [← Finset.mul_sum, hy1, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hr q) (hy0 q)
  have h2 : ∑ q, (∑ j, (lam j : ℝ) * (A j q : ℝ)) * y q ≤
      ∑ j, (lam j : ℝ) * (bV j : ℝ) := by
    have hswap : ∑ q, (∑ j, (lam j : ℝ) * (A j q : ℝ)) * y q
        = ∑ j, (lam j : ℝ) * (∑ q, (A j q : ℝ) * y q) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring
    rw [hswap]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hdom j) (hlam j)
  have h3 : ∑ q, (c q + ∑ j, (lam j : ℝ) * (A j q : ℝ)) * y q
      = ∑ q, c q * y q + ∑ q, (∑ j, (lam j : ℝ) * (A j q : ℝ)) * y q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  linarith

/-! ## 6. 部分叶和 ⇒ 全 36 对能量（只用 `w >= 0`、`1 - cos >= 0`） -/

/-- 把 15 对（或任意子集 `S`）的加权余弦和扩到全部 36 对。**不需要任何数值假设**。 -/
theorem partial_energy_le {w : Fin 9 → Fin 9 → ℝ} (hw : ∀ i j, 0 ≤ w i j)
    (z : Fin 9 → Fin 9 → ℝ) (S : Finset (Fin 9 × Fin 9)) (hS : ∀ p ∈ S, p.1 < p.2) :
    (∑ p ∈ S, w p.1 p.2 * (1 - Real.cos (z p.1 p.2)))
      ≤ ∑ i, ∑ j, if i < j then w i j * (1 - Real.cos (z i j)) else 0 := by
  set f : Fin 9 × Fin 9 → ℝ := fun p => w p.1 p.2 * (1 - Real.cos (z p.1 p.2)) with hf
  have hprod : (∑ i : Fin 9, ∑ j : Fin 9, if i < j then f (i, j) else 0)
      = ∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin 9 × Fin 9)),
          if p.1 < p.2 then f p else 0 := by
    rw [Finset.sum_product]
  have hfilt : (∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin 9 × Fin 9)),
        if p.1 < p.2 then f p else 0)
      = ∑ p ∈ ((Finset.univ ×ˢ Finset.univ : Finset (Fin 9 × Fin 9)).filter
          (fun p => p.1 < p.2)), f p := by
    rw [Finset.sum_filter]
  have hsub : S ⊆ ((Finset.univ ×ˢ Finset.univ : Finset (Fin 9 × Fin 9)).filter
      (fun p => p.1 < p.2)) := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hS p hp⟩
  have hnonneg : ∀ p ∈ ((Finset.univ ×ˢ Finset.univ : Finset (Fin 9 × Fin 9)).filter
      (fun p => p.1 < p.2)), p ∉ S → 0 ≤ f p := by
    intro p _ _
    simp only [hf]
    exact mul_nonneg (hw p.1 p.2) (by linarith [Real.cos_le_one (z p.1 p.2)])
  have hmain : (∑ p ∈ S, f p) ≤
      ∑ p ∈ ((Finset.univ ×ˢ Finset.univ : Finset (Fin 9 × Fin 9)).filter
        (fun p => p.1 < p.2)), f p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  calc (∑ p ∈ S, f p)
      ≤ ∑ p ∈ ((Finset.univ ×ˢ Finset.univ : Finset (Fin 9 × Fin 9)).filter
          (fun p => p.1 < p.2)), f p := hmain
    _ = ∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin 9 × Fin 9)),
          if p.1 < p.2 then f p else 0 := hfilt.symm
    _ = ∑ i : Fin 9, ∑ j : Fin 9, if i < j then f (i, j) else 0 := hprod.symm

end N11Formalization.FlashCosine

#print axioms N11Formalization.FlashCosine.cos_sub_cos_le_of_sin_le
#print axioms N11Formalization.FlashCosine.minorant_of_sin_le
#print axioms N11Formalization.FlashCosine.sin_le_sin_of_mem_arc_inc
#print axioms N11Formalization.FlashCosine.sin_le_sin_of_mem_arc_dec
#print axioms N11Formalization.FlashCosine.lp_step9
#print axioms N11Formalization.FlashCosine.partial_energy_le







