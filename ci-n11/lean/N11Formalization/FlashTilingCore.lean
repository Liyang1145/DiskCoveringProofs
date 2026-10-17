import Mathlib
import N11Formalization.Definitions

/-!
# FlashTilingCore —— orientation algebra for the 11-face hull cover (flash-tiling 写域)

只含可核验的初等代数：`det2`/`orient`（2×2 定向）与凸半平面引理。
不含任何"铺满"假设，不含 sorry/axiom/native_decide。
-/

namespace N11Formalization.FlashTiling

open N11Formalization

/-- 平面坐标下的 2×2 行列式。 -/
noncomputable def det2 (u v : Point) : ℝ :=
  u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0

/-- 三点定向（带号面积的两倍）。 -/
noncomputable def orient (a b c : Point) : ℝ := det2 (b - a) (c - a)

/-! ## det2 的双线性与 orient 的代数恒等式 -/

theorem det2_add (u v w : Point) : det2 u (v + w) = det2 u v + det2 u w := by
  simp only [det2]; simp; ring

theorem det2_add_left (u v w : Point) : det2 (u + v) w = det2 u w + det2 v w := by
  simp only [det2]; simp; ring

theorem det2_smul (u : Point) (t : ℝ) (v : Point) : det2 u (t • v) = t * det2 u v := by
  simp only [det2]; simp; ring

theorem det2_smul_left (t : ℝ) (u v : Point) : det2 (t • u) v = t * det2 u v := by
  simp only [det2]; simp; ring

theorem det2_sub (u v w : Point) : det2 u (v - w) = det2 u v - det2 u w := by
  simp only [det2]; simp; ring

theorem det2_antisymm (u v : Point) : det2 v u = -det2 u v := by
  simp only [det2]; ring

theorem det2_self (u : Point) : det2 u u = 0 := by
  simp only [det2]; ring

theorem det2_zero_left (v : Point) : det2 0 v = 0 := by
  simp only [det2]; simp

/-- `z ↦ det2 d z` 是线性的：`det2 d (u - w) = 0` 型关系的桥梁。 -/
theorem det2_eq_zero_of_det2_eq_zero {d u w : Point} (hd : d ≠ 0)
    (hu : det2 d u = 0) (hw : det2 d w = 0) : det2 u w = 0 := by
  rcases eq_or_ne (d.ofLp 0) 0 with h0 | h0
  · have h1 : d.ofLp 1 ≠ 0 := by
      intro h
      exact hd (by ext i; fin_cases i <;> simp [h0, h])
    have hu0 : u.ofLp 0 = 0 := by
      simp only [det2] at hu; simp [h0] at hu; exact mul_eq_zero.mp hu |>.resolve_left h1
    have hw0 : w.ofLp 0 = 0 := by
      simp only [det2] at hw; simp [h0] at hw; exact mul_eq_zero.mp hw |>.resolve_left h1
    simp only [det2]; rw [hu0, hw0]; ring
  · have hu' : u.ofLp 1 = d.ofLp 1 * u.ofLp 0 / d.ofLp 0 := by
      simp only [det2] at hu
      rw [eq_div_iff h0]; linarith
    have hw' : w.ofLp 1 = d.ofLp 1 * w.ofLp 0 / d.ofLp 0 := by
      simp only [det2] at hw
      rw [eq_div_iff h0]; linarith
    simp only [det2]; rw [hu', hw']; ring

/-- 与 `d ≠ 0` 行列式为零的向量必与 `d` 平行。 -/
theorem exists_smul_of_det2_eq_zero {u w : Point} (hu : u ≠ 0) (h : det2 u w = 0) :
    ∃ s : ℝ, w = s • u := by
  rcases eq_or_ne (u.ofLp 0) 0 with h0 | h0
  · have h1 : u.ofLp 1 ≠ 0 := by
      intro hh; exact hu (by ext i; fin_cases i <;> simp [h0, hh])
    refine ⟨w.ofLp 1 / u.ofLp 1, ?_⟩
    ext i
    fin_cases i <;> simp
    · simp only [det2] at h; simp [h0] at h
      field_simp at h ⊢
      linarith
    · field_simp
  · refine ⟨w.ofLp 0 / u.ofLp 0, ?_⟩
    ext i
    fin_cases i <;> simp
    · field_simp
    · simp only [det2] at h
      have hh : u.ofLp 0 * w.ofLp 1 = u.ofLp 1 * w.ofLp 0 := by linarith
      field_simp
      linarith

/-! ## orient 的恒等式 -/

theorem orient_swap23 (a b c : Point) : orient a b c = -orient a c b := by
  simp only [orient, det2]; simp; ring

theorem orient_cyclic (a b c : Point) : orient a b c = orient b c a := by
  simp only [orient, det2]; simp; ring

theorem orient_sub_eq_det2 (a b c : Point) :
    orient a b c = det2 (b - a) (c - a) := rfl

/-- `orient a b c - orient a b d = det2 (b - a) (c - d)`（仿射差）。 -/
theorem orient_sub_orient (a b c d : Point) :
    orient a b c - orient a b d = det2 (b - a) (c - d) := by
  simp only [orient, det2]; simp; ring

/-- 第三变元沿射线的仿射性。 -/
theorem orient_affine_ray (a b u v : Point) (t : ℝ) :
    orient a b (u + t • (v - u)) = orient a b u + t * (orient a b v - orient a b u) := by
  simp only [orient, det2]; simp; ring

/-- 半平面 `{x | 0 ≤ orient a b x}` 是凸集。 -/
theorem convex_orient_nonneg (a b : Point) : Convex ℝ {x : Point | 0 ≤ orient a b x} := by
  intro x hx y hy s t hs ht hst
  have hsplit : s • x + t • y = x + t • (y - x) := by
    ext i
    fin_cases i <;> simp <;> linarith [hst]
  show 0 ≤ orient a b (s • x + t • y)
  rw [hsplit, orient_affine_ray]
  nlinarith [hx, hy, hs, ht, hst]

/-- 顶点集落在半平面里 ⇒ 凸包落在半平面里。 -/
theorem convexHull_subset_orient_nonneg {ι : Type*} (v : ι → Point) (a b : Point)
    (hv : ∀ j, 0 ≤ orient a b (v j)) :
    convexHull ℝ (Set.range v) ⊆ {x : Point | 0 ≤ orient a b x} :=
  convexHull_min (by rintro x ⟨j, rfl⟩; exact hv j) (convex_orient_nonneg a b)

/-! ## API 探针：Fin n 循环下标（fan 引理需要"后继是双射"与"闭合和为零"） -/

#check @Fin.induction
#check @Fin.succ
#check @Fin.castSucc
#check @Fin.last
#check @Fin.val_add
#check @Fin.add_def
#check @Fin.val_one
#check @Finset.sum_bij
#check @Fintype.sum_equiv
#check @Finset.sum_eq_zero_iff_of_nonneg
#check @Finset.sum_ite_eq'
#check @finRotate
#check @Equiv.Perm
#check @IsCompact.of_isClosed_subset
#check @isClosed_le
#check @Continuous.add
#check @Continuous.mul
#check @continuous_iff_continuousAt
#check @IsCompact.exists_isMaxOn
#check @Set.Nonempty
#check @Convex.combo_mem

example (n : ℕ) (i : Fin n) : ((i + 1 : Fin n)).val = (i.val + 1) % n := by
  rw [Fin.val_add]; simp

example (n : ℕ) (i : Fin n) : (i + 1 : Fin n) = i + 1 := rfl

end N11Formalization.FlashTiling
