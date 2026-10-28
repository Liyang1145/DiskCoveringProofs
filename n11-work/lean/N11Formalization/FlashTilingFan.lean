import Mathlib
import N11Formalization.Definitions

/-!
# FlashTilingFan —— 通用 fan/dart 覆盖引理（flash-tiling 写域）

框架：`q : Fin (n+1) → Point` 配一对互逆映射 `s`（环后继）与 `s'`（环前驱），假设
`RingConvex`（每条有向边 `(q i, q (s i))` 的左侧含所有其他顶点）、环路闭合、`s` 无不动点 /
无 2-环 / 无 3-环（具体 `Fin 9` 上由 `decide` 付）。结论：对**任意** `x`（不必在凸包内）与任意满足
全部边半平面条件的 `p`，`∃ i, p ∈ convexHull ℝ {x, q i, q (s i)}`。

数学内容（全初等；无分离定理 / Jordan / 测度）：
1. `exists_phi_lt_of_ne`：若 `φ_i(p) ≥ φ_i(x)` 全成立，由闭合性 `Σφ_i ≡ const` 得全部 `φ_i(p) = φ_i(x)`，
   于是相邻两条边都 ⊥ `p−x`，与 `RingConvex` 正定性矛盾（三元组 `s' m, m, s m`）。
2. 射线 `r(t) = x + t(p−x)`：可行集闭、含 `1`、有显式上界 ⇒ 取到最大点 `T ≥ 1`；若所有 `φ_i(r T) > 0`
   则用显式 `ε > 0` 构造 `T+ε` 仍可行，与极大性矛盾 ⇒ `∃ j, φ_j(r T) = 0`。
3. `z := r T` 在直线 `(q j, q(s j))` 上；前驱边泛函给参数 `≥ 0`，后继边泛函给 `≤ 1`。

无 sorry / 自定义 axiom / native_decide。
-/

namespace N11Formalization.FlashTiling

open N11Formalization

/-- 平面坐标下的 2×2 行列式。 -/
noncomputable def det2 (u v : Point) : ℝ :=
  u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0

/-- 三点定向（带号面积的两倍）。 -/
noncomputable def orient (a b c : Point) : ℝ := det2 (b - a) (c - a)

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

/-- 第一变元线性映射。 -/
noncomputable def det2Fst (u : Point) : Point →ₗ[ℝ] ℝ where
  toFun v := det2 u v
  map_add' v w := det2_add u v w
  map_smul' t v := det2_smul u t v

/-- 第二变元线性映射。 -/
noncomputable def det2Snd (w : Point) : Point →ₗ[ℝ] ℝ where
  toFun u := det2 u w
  map_add' u v := det2_add_left u v w
  map_smul' t u := det2_smul_left t u w

/-- 与 `u ≠ 0` 行列式为零的向量必与 `u` 平行。 -/
theorem exists_smul_of_det2_eq_zero {u w : Point} (hu : u ≠ 0) (h : det2 u w = 0) :
    ∃ c : ℝ, w = c • u := by
  have hcu : u.ofLp 0 ≠ 0 ∨ u.ofLp 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  have key : u.ofLp 0 * w.ofLp 1 = u.ofLp 1 * w.ofLp 0 := by
    have hh : u.ofLp 0 * w.ofLp 1 - u.ofLp 1 * w.ofLp 0 = 0 := h
    linarith
  rcases hcu with h0 | h1
  · refine ⟨w.ofLp 0 / u.ofLp 0, ?_⟩
    ext i
    fin_cases i <;> simp
    · field_simp
    · field_simp
      linarith [key]
  · refine ⟨w.ofLp 1 / u.ofLp 1, ?_⟩
    ext i
    fin_cases i <;> simp
    · field_simp
      linarith [key]
    · field_simp

/-- 与 `d ≠ 0` 行列式皆零的两向量行列式为零。 -/
theorem det2_eq_zero_of_det2_eq_zero {d u w : Point} (hd : d ≠ 0)
    (hu : det2 d u = 0) (hw : det2 d w = 0) : det2 u w = 0 := by
  obtain ⟨a, ha⟩ := exists_smul_of_det2_eq_zero hd hu
  obtain ⟨b, hb⟩ := exists_smul_of_det2_eq_zero hd hw
  rw [ha, hb, det2_smul_left, det2_smul, det2_self, mul_zero, mul_zero]

/-- 第三变元沿射线的仿射性。 -/
theorem orient_affine_ray (a b u v : Point) (t : ℝ) :
    orient a b (u + t • (v - u)) = orient a b u + t * (orient a b v - orient a b u) := by
  simp only [orient, det2]; simp; ring

/-- 半平面 `{x | 0 ≤ orient a b x}` 是凸集。 -/
theorem convex_orient_nonneg (a b : Point) : Convex ℝ {x : Point | 0 ≤ orient a b x} := by
  intro x hx y hy s t hs ht hst
  have hsplit : s • x + t • y = x + t • (y - x) := by
    have hs' : s = 1 - t := by linarith
    ext i
    fin_cases i <;> simp [hs'] <;> ring
  show 0 ≤ orient a b (s • x + t • y)
  rw [hsplit, orient_affine_ray]
  have ht1 : t ≤ 1 := by linarith
  have hA : 0 ≤ orient a b x := hx
  have hB : 0 ≤ orient a b y := hy
  have h1 : 0 ≤ t * orient a b y := mul_nonneg ht hB
  have h2 : t * orient a b x ≤ orient a b x := by
    calc t * orient a b x ≤ 1 * orient a b x := mul_le_mul_of_nonneg_right ht1 hA
      _ = orient a b x := one_mul _
  linarith

/-- 顶点集落在半平面里 ⇒ 凸包落在半平面里。 -/
theorem convexHull_subset_orient_nonneg {ι : Type*} (v : ι → Point) (a b : Point)
    (hv : ∀ j, 0 ≤ orient a b (v j)) :
    convexHull ℝ (Set.range v) ⊆ {x : Point | 0 ≤ orient a b x} :=
  convexHull_min (by rintro x ⟨j, rfl⟩; exact hv j) (convex_orient_nonneg a b)

/-! ## 环结构 -/

/-- 环（`s` 为后继）严格凸 CCW。 -/
def RingConvex {n : ℕ} (q : Fin (n+1) → Point) (s : Fin (n+1) → Fin (n+1)) : Prop :=
  ∀ i j : Fin (n+1), j ≠ i → j ≠ s i → 0 < orient (q i) (q (s i)) (q j)

/-- 环路闭合：`Σ_i (q (s i) − q i) = 0`。 -/
def SumClosed {n : ℕ} (q : Fin (n+1) → Point) (s : Fin (n+1) → Fin (n+1)) : Prop :=
  (∑ i, (q (s i) - q i)) = 0

/-- 边 `i` 的半平面泛函。 -/
noncomputable def phi {n : ℕ} (q : Fin (n+1) → Point) (s : Fin (n+1) → Fin (n+1))
    (i : Fin (n+1)) (x : Point) : ℝ := orient (q i) (q (s i)) x

theorem phi_sub {n : ℕ} (q : Fin (n+1) → Point) (s : Fin (n+1) → Fin (n+1))
    (i : Fin (n+1)) (p x : Point) :
    phi q s i p - phi q s i x = det2 (q (s i) - q i) (p - x) := by
  simp only [phi, orient, det2]
  simp
  ring

/-- **无退化方向**。 -/
theorem exists_phi_lt_of_ne {n : ℕ} {q : Fin (n+1) → Point} {s s' : Fin (n+1) → Fin (n+1)}
    (hss' : ∀ i, s (s' i) = i) (hne1 : ∀ i, s i ≠ i) (hne2 : ∀ i, s i ≠ s' i)
    (hcv : RingConvex q s) (hcl : SumClosed q s) {x p : Point} (hne : p ≠ x) :
    ∃ i : Fin (n+1), phi q s i p < phi q s i x := by
  by_contra hcon
  push Not at hcon
  have hd : p - x ≠ 0 := sub_ne_zero.mpr hne
  have hsum : (∑ i, (phi q s i p - phi q s i x)) = 0 := by
    have h1 : ∀ i : Fin (n+1),
        phi q s i p - phi q s i x = (det2Snd (p - x)) (q (s i) - q i) :=
      fun i => phi_sub q s i p x
    simp only [h1]
    rw [← map_sum (det2Snd (p - x)), hcl]
    simp
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin (n+1))), 0 ≤ phi q s i p - phi q s i x :=
    fun i _ => by have := hcon i; linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  have e1 : det2 (q 0 - q (s' 0)) (p - x) = 0 := by
    have h := hzero (s' 0) (Finset.mem_univ _)
    have h2 := phi_sub q s (s' 0) p x
    rw [hss' 0] at h2
    linarith [h2]
  have e2 : det2 (q (s 0) - q 0) (p - x) = 0 := by
    have h := hzero 0 (Finset.mem_univ _)
    have h2 := phi_sub q s 0 p x
    linarith [h2]
  have f1 : det2 (p - x) (q 0 - q (s' 0)) = 0 := by
    have h := det2_antisymm (q 0 - q (s' 0)) (p - x)
    rw [h, e1, neg_zero]
  have f2 : det2 (p - x) (q (s 0) - q 0) = 0 := by
    have h := det2_antisymm (q (s 0) - q 0) (p - x)
    rw [h, e2, neg_zero]
  have hpar := det2_eq_zero_of_det2_eq_zero hd f1 f2
  have hzero_orient : orient (q (s' 0)) (q 0) (q (s 0)) = 0 := by
    have hsplit : q (s 0) - q (s' 0) = (q (s 0) - q 0) + (q 0 - q (s' 0)) := by abel
    change det2 (q 0 - q (s' 0)) (q (s 0) - q (s' 0)) = 0
    rw [hsplit, det2_add, hpar, det2_self, add_zero]
  have hpos : 0 < orient (q (s' 0)) (q 0) (q (s 0)) := by
    have hh := hcv (s' 0) (s 0) (hne2 0) (by rw [hss' 0]; exact hne1 0)
    rwa [hss' 0] at hh
  linarith

/-- 沿射线的仿射表示。 -/
theorem phi_affine {n : ℕ} (q : Fin (n+1) → Point) (s : Fin (n+1) → Fin (n+1))
    (i : Fin (n+1)) (u v : Point) (t : ℝ) :
    phi q s i (u + t • (v - u)) = phi q s i u + t * (phi q s i v - phi q s i u) :=
  orient_affine_ray (q i) (q (s i)) u v t

/-- **fan/dart 覆盖引理**。 -/
theorem fan_dart {n : ℕ} {q : Fin (n+1) → Point} {s s' : Fin (n+1) → Fin (n+1)}
    (hss' : ∀ i, s (s' i) = i) (hne1 : ∀ i, s i ≠ i) (hne2 : ∀ i, s i ≠ s' i)
    (hne3 : ∀ i, s (s i) ≠ i)
    (hcv : RingConvex q s) (hcl : SumClosed q s) {x p : Point}
    (hp : ∀ i : Fin (n+1), 0 ≤ phi q s i p) :
    ∃ i : Fin (n+1), p ∈ convexHull ℝ ({x, q i, q (s i)} : Set Point) := by
  by_cases hpx : p = x
  · refine ⟨0, ?_⟩
    exact subset_convexHull ℝ _ (by simp [hpx])
  · obtain ⟨i₀, hi₀⟩ := exists_phi_lt_of_ne hss' hne1 hne2 hcv hcl hpx
    have hxpos : 0 < phi q s i₀ x := lt_of_le_of_lt (hp i₀) hi₀
    set d : Point := p - x with hd
    set F : Set ℝ := {t : ℝ | 0 ≤ t ∧ ∀ i : Fin (n+1), 0 ≤ phi q s i (x + t • d)} with hF
    have haff : ∀ (i : Fin (n+1)) (t : ℝ),
        phi q s i (x + t • d) = phi q s i x + t * (phi q s i p - phi q s i x) := by
      intro i t
      rw [hd, phi_affine]
    have hFclosed : IsClosed F := by
      have hset : F = Set.Ici (0:ℝ) ∩ ⋂ i, {t : ℝ | 0 ≤ phi q s i (x + t • d)} := by
        ext t; simp [hF]
      rw [hset]
      refine IsClosed.inter isClosed_Ici (isClosed_iInter fun i => ?_)
      have hcont : Continuous fun t : ℝ => phi q s i (x + t • d) := by
        have : (fun t : ℝ => phi q s i (x + t • d))
            = fun t => phi q s i x + t * (phi q s i p - phi q s i x) := by
          funext t; exact haff i t
        rw [this]
        fun_prop
      exact isClosed_le continuous_const hcont
    have h1F : (1:ℝ) ∈ F := by
      refine ⟨zero_le_one, ?_⟩
      intro i
      have : x + (1:ℝ) • d = p := by rw [hd]; simp
      rw [this]; exact hp i
    have hFne : F.Nonempty := ⟨1, h1F⟩
    have hdpos : 0 < phi q s i₀ x - phi q s i₀ p := by linarith
    have hbound : ∀ t ∈ F, t ≤ phi q s i₀ x / (phi q s i₀ x - phi q s i₀ p) := by
      rintro t ⟨-, ht⟩
      have hc := ht i₀
      rw [haff i₀ t] at hc
      rw [le_div_iff₀ hdpos]
      linarith
    have hFsub : F ⊆ Set.Icc (0:ℝ) (phi q s i₀ x / (phi q s i₀ x - phi q s i₀ p)) :=
      fun t ht => ⟨ht.1, hbound t ht⟩
    have hFcompact : IsCompact F := IsCompact.of_isClosed_subset isCompact_Icc hFclosed hFsub
    obtain ⟨T, hTF, hTmax⟩ := hFcompact.exists_isMaxOn hFne continuousOn_id
    have hT1 : 1 ≤ T := by
      have := hTmax h1F
      simpa using this
    have hexit : ∃ j : Fin (n+1), phi q s j (x + T • d) = 0 := by
      by_contra hcon
      have hcon' : ∀ j : Fin (n+1), 0 < phi q s j (x + T • d) := fun j =>
        lt_of_le_of_ne (hTF.2 j) (Ne.symm (fun h0 => hcon ⟨j, h0⟩))
      obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (n+1)))
        (fun i => phi q s i (x + T • d)) ⟨0, Finset.mem_univ 0⟩
      set K : ℝ := ∑ i, |phi q s i p - phi q s i x| with hK
      have hKnn : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
      have hδ : ∀ i : Fin (n+1), |phi q s i p - phi q s i x| ≤ K := fun i =>
        Finset.single_le_sum (fun j _ => abs_nonneg (phi q s j p - phi q s j x))
          (Finset.mem_univ i)
      set ε : ℝ := phi q s j₀ (x + T • d) / (K + 1) with hε
      have hεpos : 0 < ε := by
        rw [hε]; exact div_pos (hcon' j₀) (by linarith)
      have hεK : ε * K < phi q s j₀ (x + T • d) := by
        have hφ : 0 < phi q s j₀ (x + T • d) := hcon' j₀
        have hK1 : 0 < K + 1 := by linarith
        rw [hε, div_mul_eq_mul_div, div_lt_iff₀ hK1]
        nlinarith [hKnn, hφ]
      have hmem : T + ε ∈ F := by
        refine ⟨by linarith, ?_⟩
        intro i
        have haff2 : phi q s i (x + (T + ε) • d)
            = phi q s i (x + T • d) + ε * (phi q s i p - phi q s i x) := by
          rw [haff i (T + ε), haff i T]
          ring
        rw [haff2]
        have hle := hj₀ i (Finset.mem_univ i)
        have hb := abs_le.mp (hδ i)
        have hmul : -ε * K ≤ ε * (phi q s i p - phi q s i x) := by nlinarith [hb.1, hεpos.le]
        nlinarith [hle, hεK, hmul]
      have hmax : T + ε ≤ T := hTmax hmem
      linarith
    obtain ⟨j, hj⟩ := hexit
    set z : Point := x + T • d with hz
    have hedge_ne : q (s j) - q j ≠ 0 := by
      intro hzero
      have hq : q (s j) = q j := sub_eq_zero.mp hzero
      have hpos := hcv (s' j) (s j) (hne2 j) (by rw [hss' j]; exact hne1 j)
      rw [hss' j, hq] at hpos
      have hz0 : orient (q (s' j)) (q j) (q j) = 0 := by
        change det2 (q j - q (s' j)) (q j - q (s' j)) = 0
        exact det2_self _
      rw [hz0] at hpos
      exact absurd hpos (lt_irrefl 0)
    have hdet : det2 (q (s j) - q j) (z - q j) = 0 := hj
    obtain ⟨c, hc⟩ := exists_smul_of_det2_eq_zero hedge_ne hdet
    have hprev : 0 ≤ phi q s (s' j) z := hTF.2 (s' j)
    have hprev_form : phi q s (s' j) z = c * orient (q (s' j)) (q j) (q (s j)) := by
      have h2 : phi q s (s' j) z = det2 (q j - q (s' j)) (z - q (s' j)) := by
        simp only [phi, orient, hss' j]
      have h1 : z - q (s' j) = (q j - q (s' j)) + c • (q (s j) - q j) := by
        have h4 : z - q (s' j) = (z - q j) + (q j - q (s' j)) := by abel
        rw [h4, hc]
        rw [add_comm]
      rw [h2, h1, det2_add, det2_smul, det2_self, zero_add]
      have h5 : det2 (q j - q (s' j)) (q (s j) - q j)
          = orient (q (s' j)) (q j) (q (s j)) := by
        have hsplit : q (s j) - q j = (q (s j) - q (s' j)) - (q j - q (s' j)) := by abel
        rw [hsplit, det2_sub, det2_self, sub_zero]
        rfl
      rw [h5]
    have hprev_pos : 0 < orient (q (s' j)) (q j) (q (s j)) := by
      have hh := hcv (s' j) (s j) (hne2 j) (by rw [hss' j]; exact hne1 j)
      rwa [hss' j] at hh
    have hc0 : 0 ≤ c := by
      rw [hprev_form] at hprev
      exact nonneg_of_mul_nonneg_left hprev hprev_pos
    have hnext : 0 ≤ phi q s (s j) z := hTF.2 (s j)
    have hnext_form : phi q s (s j) z = (1 - c) * orient (q (s j)) (q (s (s j))) (q j) := by
      have h2 : phi q s (s j) z = det2 (q (s (s j)) - q (s j)) (z - q (s j)) := rfl
      have h1 : z - q (s j) = (1 - c) • (q j - q (s j)) := by
        have h4 : z - q (s j) = (z - q j) + (q j - q (s j)) := by abel
        rw [h4, hc]
        module
      rw [h2, h1, det2_smul]
      rw [show det2 (q (s (s j)) - q (s j)) (q j - q (s j))
          = orient (q (s j)) (q (s (s j))) (q j) from rfl]
    have hnext_pos : 0 < orient (q (s j)) (q (s (s j))) (q j) :=
      hcv (s j) j (Ne.symm (hne1 j)) (Ne.symm (hne3 j))
    have hc1 : c ≤ 1 := by
      rw [hnext_form] at hnext
      by_contra hlt
      push Not at hlt
      nlinarith [hnext_pos]
    refine ⟨j, ?_⟩
    have hzmem : z ∈ convexHull ℝ ({x, q j, q (s j)} : Set Point) := by
      have hcombo : z = (1 - c) • q j + c • q (s j) := by
        have h4 : z = (z - q j) + q j := by abel
        rw [h4, hc]
        module
      have h2 : q j ∈ convexHull ℝ ({x, q j, q (s j)} : Set Point) :=
        subset_convexHull ℝ _ (by simp)
      have h3 : q (s j) ∈ convexHull ℝ ({x, q j, q (s j)} : Set Point) :=
        subset_convexHull ℝ _ (by simp)
      rw [hcombo]
      exact (convex_convexHull ℝ _) h2 h3 (by linarith) hc0 (by linarith)
    have hxmem : x ∈ convexHull ℝ ({x, q j, q (s j)} : Set Point) :=
      subset_convexHull ℝ _ (by simp)
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have h5 : (1/T) • (z - x) = p - x := by
      have hz' : z - x = T • (p - x) := by rw [hz, hd, add_sub_cancel_left]
      rw [hz', smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hTpos), one_smul]
    have hcombo : p = (1 - 1/T) • x + (1/T) • z := by
      have h6 : p = x + (1/T) • (z - x) := by
        rw [h5]
        abel
      rw [h6, smul_sub, sub_smul, one_smul]
      abel
    rw [hcombo]
    refine (convex_convexHull ℝ _) hxmem hzmem ?_ ?_ ?_
    · have h1T : 1/T ≤ 1 := (div_le_one hTpos).mpr hT1
      linarith
    · exact div_nonneg zero_le_one hTpos.le
    · ring

end N11Formalization.FlashTiling

/-! ## 公理画像（本文件两枚承重定理） -/
#print axioms N11Formalization.FlashTiling.fan_dart
#print axioms N11Formalization.FlashTiling.exists_phi_lt_of_ne
#print axioms N11Formalization.FlashTiling.convexHull_subset_orient_nonneg
#print axioms N11Formalization.FlashTiling.exists_smul_of_det2_eq_zero
