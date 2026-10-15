import N11Formalization.KrawczykMatrix
import N11Formalization.PrecondRight

/-!
# `HsumCert`: `hsum` 的整数化证书（数据 → checker → soundness → 具体通过 / 具体被拒）

**靶子形状**（源：`N11Formalization/KrawczykMatrix.lean:124`、`Precond.lean:119`、
`NondegProof.lean:591/622/656/679`）：

```
hsum : ∀ i : Fin 12, ∑ j : Fin 12,
         max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K
```

**为什么必须整数化**（本文件作者实测，`evidence/root-audit/ProbeRA1`）：`decide` 在 ℚ 上**不归约**
（`Rat.add`/`Rat.mul` 不可约，连 `(1:ℚ)+1 = 2` 都失败），而 ℤ 的算术/比较/`Fin` 求和全部可 `decide`。
所以：**数据全部是 ℤ**（共同分母 `D` 下的分子），checker 只做 ℤ 运算；ℤ→ℚ 的语义由一个**定理**给出。

**结构**（GUIDE §5：不可信生成器 + 已证正确 checker）：
1. `HsumCert`：不受信数据（`D`、`Y` 分子、`J` 两端分子、`K` 分子/分母）；
2. `check : HsumCert → Bool`：纯 ℤ 判据（6 条）；
3. `check_sound`：`check = true → hsum ∧ 0 ≤ K ∧ K < 1`（一次给出 `hsum`/`hK0`/`hK1`）；
4. `certOK_check`：具体数据**通过**（`decide`）；
5. `certLIE_rejected`：把行和界压小 1 的**说谎见证被拒**（`decide`）。

**真实等级**：kernel-proved，零 `sorry`、零自定义 `axiom`、零 `native_decide`。
**口径**：固定 `n = 12`；共同分母模型 `Y i k = numY i k / D`，`J k j = [loNum/D, hiNum/D]`（`D > 0`）；
`K = numK / denK`（`denK > 0`）；`J` 的合法性 `loNum ≤ hiNum` 由 checker 的整数不等式验证。
**不覆盖**：`Y`/`Jt` 本身的来源（那是 `hJ` 与生成器的义务）；本文件不产生 `Jt`。
-/

namespace N11Formalization

/-! ## 0. 整数/有理 cast 的 `max`/`abs` 桥（自证，不依赖引理名） -/

theorem int_cast_maxQ (a b : ℤ) : ((max a b : ℤ) : ℚ) = max (a : ℚ) (b : ℚ) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]

theorem int_cast_absQ (a : ℤ) : ((|a| : ℤ) : ℚ) = |(a : ℚ)| := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by exact_mod_cast h)]
  · rw [abs_of_nonpos h, abs_of_nonpos (by exact_mod_cast h)]
    push_cast
    ring

theorem rat_cast_maxR (a b : ℚ) : ((max a b : ℚ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]

theorem rat_cast_absR (a : ℚ) : ((|a| : ℚ) : ℝ) = |(a : ℝ)| := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by exact_mod_cast h)]
  · rw [abs_of_nonpos h, abs_of_nonpos (by exact_mod_cast h)]
    push_cast
    ring

/-- `max a b / E = max (a/E) (b/E)`（`0 ≤ E`）。 -/
theorem max_div_right {E : ℚ} (hE : 0 ≤ E) (a b : ℚ) : max a b / E = max (a / E) (b / E) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h hE)]
  · rw [max_eq_left h, max_eq_left (div_le_div_of_nonneg_right h hE)]

/-- **绝对值与缩放交换**：`max |a/E| |b/E| = max |a| |b| / E`（`E > 0`）。 -/
theorem max_abs_div {E : ℚ} (hE : 0 < E) (a b : ℚ) :
    max |a / E| |b / E| = max |a| |b| / E := by
  rw [abs_div, abs_div, abs_of_pos hE]
  exact (max_div_right hE.le |a| |b|).symm

/-- ℚ 层的 `max`/`abs`/求和 一次性转移到 ℝ。 -/
theorem rat_cast_max_abs_sum {n : ℕ} (f g : Fin n → ℚ) (E : ℚ) :
    (((∑ j : Fin n, max |f j / E| |g j / E| : ℚ)) : ℝ)
      = ∑ j : Fin n, max |(f j : ℝ) / (E : ℝ)| |(g j : ℝ) / (E : ℝ)| := by
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rat_cast_maxR, rat_cast_absR, rat_cast_absR]
  push_cast
  ring

/-! ## 1. `krawczykMat` 端点的显式 ℚ 公式（soundness 的数学内核） -/

namespace RatInterval

/-- 点积 `lo` 的逐项：按 `c i` 的符号取向。 -/
def loTerm {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval) (i : Fin n) : ℚ :=
  if 0 ≤ c i then c i * (A i).lo else c i * (A i).hi

/-- 点积 `hi` 的逐项。 -/
def hiTerm {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval) (i : Fin n) : ℚ :=
  if 0 ≤ c i then c i * (A i).hi else c i * (A i).lo

theorem ofRat_mul_endpoints (c : ℚ) (A : RatInterval) (hA : A.lo ≤ A.hi) :
    ((ofRat c).mul A).lo = (if 0 ≤ c then c * A.lo else c * A.hi) ∧
      ((ofRat c).mul A).hi = (if 0 ≤ c then c * A.hi else c * A.lo) := by
  constructor
  · show min (min (c * A.lo) (c * A.hi)) (min (c * A.lo) (c * A.hi)) = _
    rw [min_self]
    by_cases hc : 0 ≤ c
    · rw [if_pos hc, min_eq_left (mul_le_mul_of_nonneg_left hA hc)]
    · rw [if_neg hc, min_eq_right (mul_le_mul_of_nonpos_left hA (not_le.mp hc).le)]
  · show max (max (c * A.lo) (c * A.hi)) (max (c * A.lo) (c * A.hi)) = _
    rw [max_self]
    by_cases hc : 0 ≤ c
    · rw [if_pos hc, max_eq_right (mul_le_mul_of_nonneg_left hA hc)]
    · rw [if_neg hc, max_eq_left (mul_le_mul_of_nonpos_left hA (not_le.mp hc).le)]

theorem foldl_dotFold_lo {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval)
    (hA : ∀ i, (A i).lo ≤ (A i).hi) (l : List (Fin n)) (acc : RatInterval) :
    (l.foldl (dotFold c A) acc).lo = acc.lo + (l.map (loTerm c A)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons i t ih =>
    have hstep : (dotFold c A acc i).lo = acc.lo + loTerm c A i := by
      rw [show (dotFold c A acc i).lo = acc.lo + ((ofRat (c i)).mul (A i)).lo from rfl,
        (ofRat_mul_endpoints (c i) (A i) (hA i)).1]
      rfl
    rw [List.foldl_cons, ih (dotFold c A acc i), List.map_cons, List.sum_cons, hstep]
    ring

theorem foldl_dotFold_hi {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval)
    (hA : ∀ i, (A i).lo ≤ (A i).hi) (l : List (Fin n)) (acc : RatInterval) :
    (l.foldl (dotFold c A) acc).hi = acc.hi + (l.map (hiTerm c A)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons i t ih =>
    have hstep : (dotFold c A acc i).hi = acc.hi + hiTerm c A i := by
      rw [show (dotFold c A acc i).hi = acc.hi + ((ofRat (c i)).mul (A i)).hi from rfl,
        (ofRat_mul_endpoints (c i) (A i) (hA i)).2]
      rfl
    rw [List.foldl_cons, ih (dotFold c A acc i), List.map_cons, List.sum_cons, hstep]
    ring

theorem dot_lo_eq {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval)
    (hA : ∀ i, (A i).lo ≤ (A i).hi) :
    (dot c A).lo = ((List.finRange n).map (loTerm c A)).sum := by
  have h : dot c A = (List.finRange n).foldl (dotFold c A) (ofRat 0) := rfl
  rw [h, foldl_dotFold_lo c A hA (List.finRange n) (ofRat 0)]
  show (0 : ℚ) + _ = _
  rw [zero_add]

theorem dot_hi_eq {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval)
    (hA : ∀ i, (A i).lo ≤ (A i).hi) :
    (dot c A).hi = ((List.finRange n).map (hiTerm c A)).sum := by
  have h : dot c A = (List.finRange n).foldl (dotFold c A) (ofRat 0) := rfl
  rw [h, foldl_dotFold_hi c A hA (List.finRange n) (ofRat 0)]
  show (0 : ℚ) + _ = _
  rw [zero_add]

theorem finRange_map_sum {n : ℕ} (f : Fin n → ℚ) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  rw [← List.sum_toFinset f (List.nodup_finRange n), List.toFinset_finRange]

end RatInterval

/-- **`krawczykMat` 端点公式**：`lo = δ − Σ_k hiTerm`，`hi = δ − Σ_k loTerm`。 -/
theorem krawczykMat_lo_hi_eq {n : ℕ} (Y : Fin n → Fin n → ℚ)
    (J : Fin n → Fin n → RatInterval) (hJ : ∀ k j, (J k j).lo ≤ (J k j).hi) (i j : Fin n) :
    ((krawczykMat Y J i j).lo
        = (if i = j then (1 : ℚ) else 0)
          - ∑ k : Fin n, RatInterval.hiTerm (Y i) (fun k => J k j) k)
      ∧ ((krawczykMat Y J i j).hi
        = (if i = j then (1 : ℚ) else 0)
          - ∑ k : Fin n, RatInterval.loTerm (Y i) (fun k => J k j) k) := by
  have hhi := RatInterval.dot_hi_eq (n := n) (Y i) (fun k => J k j) (fun k => hJ k j)
  have hlo := RatInterval.dot_lo_eq (n := n) (Y i) (fun k => J k j) (fun k => hJ k j)
  rw [RatInterval.finRange_map_sum] at hhi hlo
  constructor
  · show (if i = j then (1 : ℚ) else 0) - (incrMat Y J i j).hi = _
    rw [show (incrMat Y J i j).hi = (RatInterval.dot (Y i) fun k => J k j).hi from rfl, hhi]
  · show (if i = j then (1 : ℚ) else 0) - (incrMat Y J i j).lo = _
    rw [show (incrMat Y J i j).lo = (RatInterval.dot (Y i) fun k => J k j).lo from rfl, hlo]

/-! ## 2. 证书数据结构与派生量 -/

/-- `hsum` 行的整数化证书数据（**全部不受信**）。 -/
structure HsumCert where
  /-- 共同分母（正）。 -/
  D : ℤ
  /-- 预条件子 `Y` 的分子（`Y i k = numY i k / D`）。 -/
  numY : Fin 12 → Fin 12 → ℤ
  /-- `J` 区间下端分子。 -/
  loNum : Fin 12 → Fin 12 → ℤ
  /-- `J` 区间上端分子。 -/
  hiNum : Fin 12 → Fin 12 → ℤ
  /-- 行和界 `K = numK / denK` 的分子。 -/
  numK : ℤ
  /-- `K` 的分母（正）。 -/
  denK : ℤ

namespace HsumCert

/-- 共同分母的平方（点积端点落在 `D²` 格上）。 -/
def E (c : HsumCert) : ℤ := c.D * c.D

/-- `Y` 的 ℚ 语义。 -/
def Yof (c : HsumCert) : Fin 12 → Fin 12 → ℚ := fun i k => (c.numY i k : ℚ) / (c.D : ℚ)

/-- `J` 的 ℚ 语义。 -/
def Jof (c : HsumCert) : Fin 12 → Fin 12 → RatInterval :=
  fun k j => ⟨(c.loNum k j : ℚ) / (c.D : ℚ), (c.hiNum k j : ℚ) / (c.D : ℚ)⟩

/-- `(Σ_k Y_ik·J_kj).lo` 的分子（`D²` 格）。 -/
def loNumD (c : HsumCert) (i j : Fin 12) : ℤ :=
  ∑ k : Fin 12, if 0 ≤ c.numY i k then c.numY i k * c.loNum k j else c.numY i k * c.hiNum k j

/-- `(Σ_k Y_ik·J_kj).hi` 的分子（`D²` 格）。 -/
def hiNumD (c : HsumCert) (i j : Fin 12) : ℤ :=
  ∑ k : Fin 12, if 0 ≤ c.numY i k then c.numY i k * c.hiNum k j else c.numY i k * c.loNum k j

/-- `(I − Y·J)_{ij}.lo = LN / D²` 的分子。 -/
def LN (c : HsumCert) (i j : Fin 12) : ℤ := (if i = j then 1 else 0) * c.E - c.hiNumD i j

/-- `(I − Y·J)_{ij}.hi = HN / D²` 的分子。 -/
def HN (c : HsumCert) (i j : Fin 12) : ℤ := (if i = j then 1 else 0) * c.E - c.loNumD i j

/-- 第 `i` 行的整数行和（`D²` 格分子）。 -/
def rowZ (c : HsumCert) (i : Fin 12) : ℤ := ∑ j : Fin 12, max |c.LN i j| |c.HN i j|

/-! ## 3. ℤ 数据 → ℚ 语义（逐项 / 求和 / 端点） -/

theorem nonneg_Yof (c : HsumCert) (hD : 0 < c.D) {i k : Fin 12} (h : 0 ≤ c.numY i k) :
    0 ≤ c.Yof i k := by
  simp only [Yof]
  exact div_nonneg (by exact_mod_cast h) (by exact_mod_cast hD.le)

theorem not_nonneg_Yof (c : HsumCert) (hD : 0 < c.D) {i k : Fin 12}
    (h : ¬ 0 ≤ c.numY i k) : ¬ 0 ≤ c.Yof i k := by
  intro hq
  simp only [Yof] at hq
  have hDQ : (0 : ℚ) < (c.D : ℚ) := by exact_mod_cast hD
  have hDne : ((c.D : ℤ) : ℚ) ≠ 0 := ne_of_gt hDQ
  have h2 : (0 : ℚ) * (c.D : ℚ) ≤ (c.numY i k : ℚ) := by
    have h3 := mul_le_mul_of_nonneg_right hq hDQ.le
    rw [div_mul_cancel₀ _ hDne] at h3
    simpa using h3
  exact h (by simpa using h2)

theorem loTerm_eq (c : HsumCert) (hD : 0 < c.D) {i k j : Fin 12} :
    RatInterval.loTerm (c.Yof i) (fun k => c.Jof k j) k
      = ((if 0 ≤ c.numY i k then c.numY i k * c.loNum k j
            else c.numY i k * c.hiNum k j : ℤ) : ℚ) / (c.E : ℚ) := by
  simp only [RatInterval.loTerm, Jof, E]
  by_cases h : 0 ≤ c.numY i k
  · rw [if_pos h, if_pos (nonneg_Yof c hD h)]
    rw [show c.Yof i k = (c.numY i k : ℚ) / (c.D : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]
  · rw [if_neg h, if_neg (not_nonneg_Yof c hD h)]
    rw [show c.Yof i k = (c.numY i k : ℚ) / (c.D : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]

theorem hiTerm_eq (c : HsumCert) (hD : 0 < c.D) {i k j : Fin 12} :
    RatInterval.hiTerm (c.Yof i) (fun k => c.Jof k j) k
      = ((if 0 ≤ c.numY i k then c.numY i k * c.hiNum k j
            else c.numY i k * c.loNum k j : ℤ) : ℚ) / (c.E : ℚ) := by
  simp only [RatInterval.hiTerm, Jof, E]
  by_cases h : 0 ≤ c.numY i k
  · rw [if_pos h, if_pos (nonneg_Yof c hD h)]
    rw [show c.Yof i k = (c.numY i k : ℚ) / (c.D : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]
  · rw [if_neg h, if_neg (not_nonneg_Yof c hD h)]
    rw [show c.Yof i k = (c.numY i k : ℚ) / (c.D : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]

theorem sum_loTerm_eq (c : HsumCert) (hD : 0 < c.D) (i j : Fin 12) :
    (∑ k : Fin 12, RatInterval.loTerm (c.Yof i) (fun k => c.Jof k j) k)
      = (c.loNumD i j : ℚ) / (c.E : ℚ) := by
  rw [Finset.sum_congr rfl (fun k _ => loTerm_eq c hD (i := i) (k := k) (j := j)), ← Finset.sum_div]
  congr 1
  simp only [loNumD, Int.cast_sum]

theorem sum_hiTerm_eq (c : HsumCert) (hD : 0 < c.D) (i j : Fin 12) :
    (∑ k : Fin 12, RatInterval.hiTerm (c.Yof i) (fun k => c.Jof k j) k)
      = (c.hiNumD i j : ℚ) / (c.E : ℚ) := by
  rw [Finset.sum_congr rfl (fun k _ => hiTerm_eq c hD (i := i) (k := k) (j := j)), ← Finset.sum_div]
  congr 1
  simp only [hiNumD, Int.cast_sum]

theorem Jof_valid (c : HsumCert) (hD : 0 < c.D)
    (hvalid : ∀ k j : Fin 12, c.loNum k j ≤ c.hiNum k j) (k j : Fin 12) :
    (c.Jof k j).lo ≤ (c.Jof k j).hi := by
  simp only [Jof]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hvalid k j) (by exact_mod_cast hD.le)

theorem Epos (c : HsumCert) (hD : 0 < c.D) : (0 : ℚ) < (c.E : ℚ) := by
  have hDQ : (0 : ℚ) < (c.D : ℚ) := by exact_mod_cast hD
  rw [E]
  push_cast
  nlinarith [hDQ]

/-- **端点恒等式（`lo` 侧）**：`(I − Y·J)_{ij}.lo = LN / E`。 -/
theorem krawczykMat_lo_eq (c : HsumCert) (hD : 0 < c.D)
    (hvalid : ∀ k j : Fin 12, c.loNum k j ≤ c.hiNum k j) (i j : Fin 12) :
    (krawczykMat c.Yof c.Jof i j).lo = (c.LN i j : ℚ) / (c.E : ℚ) := by
  rw [(krawczykMat_lo_hi_eq c.Yof c.Jof (fun k j => Jof_valid c hD hvalid k j) i j).1,
    sum_hiTerm_eq c hD i j]
  have hEne : (c.E : ℚ) ≠ 0 := ne_of_gt (Epos c hD)
  by_cases hij : i = j
  · simp only [hij, LN]
    push_cast
    field_simp
  · simp only [if_neg hij, LN]
    push_cast
    field_simp

/-- **端点恒等式（`hi` 侧）**：`(I − Y·J)_{ij}.hi = HN / E`。 -/
theorem krawczykMat_hi_eq (c : HsumCert) (hD : 0 < c.D)
    (hvalid : ∀ k j : Fin 12, c.loNum k j ≤ c.hiNum k j) (i j : Fin 12) :
    (krawczykMat c.Yof c.Jof i j).hi = (c.HN i j : ℚ) / (c.E : ℚ) := by
  rw [(krawczykMat_lo_hi_eq c.Yof c.Jof (fun k j => Jof_valid c hD hvalid k j) i j).2,
    sum_loTerm_eq c hD i j]
  have hEne : (c.E : ℚ) ≠ 0 := ne_of_gt (Epos c hD)
  by_cases hij : i = j
  · simp only [hij, HN]
    push_cast
    field_simp
  · simp only [if_neg hij, HN]
    push_cast
    field_simp

/-! ## 4. checker（纯 ℤ，六条判据） -/

/-- **纯函数 checker**：只用 `ℤ` 判据，故 `decide` 是真正的内核求值。
六条：`D > 0`；`denK > 0`；`numK ≥ 0`；`J` 区间合法；逐行整数行和界；`K < 1`。 -/
def check (c : HsumCert) : Bool :=
  decide (0 < c.D) && decide (0 < c.denK) && decide (0 ≤ c.numK)
    && decide (∀ k j : Fin 12, c.loNum k j ≤ c.hiNum k j)
    && decide (∀ i : Fin 12, c.rowZ i * c.denK ≤ c.numK * c.E)
    && decide (c.numK < c.denK)

/-! ## 5. soundness：`check = true → hsum ∧ 0 ≤ K ∧ K < 1` -/

theorem check_sound {c : HsumCert} (h : c.check = true) :
    (∀ i : Fin 12, ∑ j : Fin 12,
        max |((krawczykMat c.Yof c.Jof i j).lo : ℝ)| |((krawczykMat c.Yof c.Jof i j).hi : ℝ)|
        ≤ (c.numK : ℝ) / (c.denK : ℝ))
      ∧ (0 ≤ (c.numK : ℝ) / (c.denK : ℝ))
      ∧ ((c.numK : ℝ) / (c.denK : ℝ) < 1) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hD, hdenK⟩, hnumK⟩, hvalid⟩, hrow⟩, hK1⟩ := h
  have hKQ : (0 : ℚ) < (c.denK : ℚ) := by exact_mod_cast hdenK
  have hEpos := Epos c hD
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hrowQ : (∑ j : Fin 12,
          max |(c.LN i j : ℚ) / (c.E : ℚ)| |(c.HN i j : ℚ) / (c.E : ℚ)|)
        ≤ (c.numK : ℚ) / (c.denK : ℚ) := by
      have hZ : ((∑ j : Fin 12, max |c.LN i j| |c.HN i j| : ℤ) : ℚ)
          = ∑ j : Fin 12, max |(c.LN i j : ℚ)| |(c.HN i j : ℚ)| := by
        rw [Int.cast_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [int_cast_maxQ, int_cast_absQ, int_cast_absQ]
      have hcross : ((∑ j : Fin 12, max |(c.LN i j : ℚ)| |(c.HN i j : ℚ)|)) * (c.denK : ℚ)
          ≤ (c.numK : ℚ) * (c.E : ℚ) := by
        rw [← hZ, ← Int.cast_mul, ← Int.cast_mul]
        exact_mod_cast hrow i
      rw [Finset.sum_congr rfl (fun j _ => max_abs_div hEpos (c.LN i j) (c.HN i j)),
        ← Finset.sum_div]
      exact (div_le_div_iff₀ hEpos hKQ).mpr hcross
    have hcast := rat_cast_max_abs_sum (fun j => (c.LN i j : ℚ)) (fun j => (c.HN i j : ℚ))
      (c.E : ℚ)
    simp only [krawczykMat_lo_eq c hD hvalid i, krawczykMat_hi_eq c hD hvalid i, Rat.cast_div]
    rw [← hcast]
    exact_mod_cast hrowQ
  · have h0 : (0 : ℚ) ≤ (c.numK : ℚ) / (c.denK : ℚ) :=
      div_nonneg (by exact_mod_cast hnumK) hKQ.le
    exact_mod_cast h0
  · have h1 : (c.numK : ℚ) / (c.denK : ℚ) < 1 := by
      rw [div_lt_one hKQ]
      exact_mod_cast hK1
    exact_mod_cast h1

/-! ## 6. 具体实例：通过 / 被拒 -/

/-- 实例数据：`D = 10`，`Y = I`（`numY = 10·δ`），`J_kk = [9/10, 9/10]`。 -/
def numY1 : Fin 12 → Fin 12 → ℤ := fun i k => if i = k then 10 else 0

def loNum1 : Fin 12 → Fin 12 → ℤ := fun k j => if k = j then 9 else 0

def hiNum1 : Fin 12 → Fin 12 → ℤ := fun k j => if k = j then 9 else 0

/-- 诚实实例：真实的 `Σ_j max` = `1/10`，声称 `K = 10/100 = 1/10`。 -/
def certOK : HsumCert :=
  { D := 10, numY := numY1, loNum := loNum1, hiNum := hiNum1, numK := 10, denK := 100 }

/-- 说谎实例：把行和界**压小 1**（`numK = 9`，真实需要 `≥ 10`）。 -/
def certLIE : HsumCert :=
  { D := 10, numY := numY1, loNum := loNum1, hiNum := hiNum1, numK := 9, denK := 100 }

/-- 整数行和的独立读数（内核）：诚实实例每行都是 `10`。 -/
theorem certOK_rowZ (i : Fin 12) : certOK.rowZ i = 10 := by
  fin_cases i <;> decide

/-- 整数行和的独立读数：说谎实例与诚实实例的**数据完全相同**，只有 `numK` 不同。 -/
theorem certLIE_rowZ (i : Fin 12) : certLIE.rowZ i = 10 := by
  fin_cases i <;> decide

/-- **诚实实例通过内核检查**（`decide` = 内核求值这个 `Bool`，不是外部 exit 0）。 -/
theorem certOK_check : certOK.check = true := by decide

/-- **说谎实例被内核拒绝**：同一份 `Y`/`J` 数据，行和界从 `10/100` 压到 `9/100`。 -/
theorem certLIE_rejected : certLIE.check = false := by decide

/-- 诚实实例的 `hsum`（由声明的 soundness 直接得到）。 -/
theorem certOK_hsum :
    ∀ i : Fin 12, ∑ j : Fin 12,
        max |((krawczykMat certOK.Yof certOK.Jof i j).lo : ℝ)|
          |((krawczykMat certOK.Yof certOK.Jof i j).hi : ℝ)|
        ≤ (certOK.numK : ℝ) / (certOK.denK : ℝ) :=
  (check_sound certOK_check).1

/-- 诚实实例的 `K`：`= 1/10 < 1`（`hK1` 由 checker 一次给出）。 -/
theorem certOK_K_lt_one : (certOK.numK : ℝ) / (certOK.denK : ℝ) < 1 :=
  (check_sound certOK_check).2.2

/-- 诚实实例的 `hK0`：`0 ≤ K`。 -/
theorem certOK_K_nonneg : 0 ≤ (certOK.numK : ℝ) / (certOK.denK : ℝ) :=
  (check_sound certOK_check).2.1

/-! ## 7. **右侧收缩形式** `I − A·Y`（`krawczykMatR J Y`）——路线裁决要求的那一侧

`TRUST §4bis`：源预条件子是 binary64 近似逆 ⇒ 精确有理**左逆**取不到 ⇒ 走**右侧收缩**
（`nd_end_to_end_right` / `nd_plug_right_data` / `PrecondRight.lean`），需要的是

```
hsumR : ∀ i : Fin n, ∑ j : Fin n, max |((krawczykMatR Jt Y i j).lo : ℝ)| |((krawczykMatR Jt Y i j).hi : ℝ)| ≤ K'
```

**形状来源（本文件作者读声明得到）**：`PrecondRight.lean:84`
`krawczykMatR J Y i j = ofRat δ_ij − dot (fun k => Y k j) (fun k => J i k)`
⇒ 与左侧 `krawczykMat Y J i j = ofRat δ_ij − dot (Y i) (fun k => J k j)` **是同一种折叠**，
只是**系数取 `Y` 的第 j 列、区间取 `J` 的第 i 行** ⇒ **同一套 checker 架构逐字迁移**（不是转置恒等式：
`I − Y·A` 与 `I − A·Y` 是两个不同矩阵，行和一般不等）。

**共同分母模型完全复用**：`Y i k = numY i k / D`，`J k j = [loNum/D, hiNum/D]`，同一 `D`。
⇒ **同一份 `HsumCert` 数据同时产出左、右两条**（数据项 `Y` 只写一次 ✓）。 -/

/-- `(Σ_k Y_kj·J_ik).lo` 的分子（`D²` 格）。 -/
def loNumDR (c : HsumCert) (i j : Fin 12) : ℤ :=
  ∑ k : Fin 12, if 0 ≤ c.numY k j then c.numY k j * c.loNum i k else c.numY k j * c.hiNum i k

/-- `(Σ_k Y_kj·J_ik).hi` 的分子。 -/
def hiNumDR (c : HsumCert) (i j : Fin 12) : ℤ :=
  ∑ k : Fin 12, if 0 ≤ c.numY k j then c.numY k j * c.hiNum i k else c.numY k j * c.loNum i k

/-- `(I − A·Y)_{ij}.lo = LNR / D²` 的分子。 -/
def LNR (c : HsumCert) (i j : Fin 12) : ℤ := (if i = j then 1 else 0) * c.E - c.hiNumDR i j

/-- `(I − A·Y)_{ij}.hi = HNR / D²` 的分子。 -/
def HNR (c : HsumCert) (i j : Fin 12) : ℤ := (if i = j then 1 else 0) * c.E - c.loNumDR i j

/-- 右侧第 `i` 行的整数行和。 -/
def rowZR (c : HsumCert) (i : Fin 12) : ℤ := ∑ j : Fin 12, max |c.LNR i j| |c.HNR i j|

theorem nonneg_Yof_col (c : HsumCert) (hD : 0 < c.D) {k j : Fin 12}
    (h : 0 ≤ c.numY k j) : 0 ≤ c.Yof k j :=
  nonneg_Yof c hD (i := k) (k := j) h

theorem not_nonneg_Yof_col (c : HsumCert) (hD : 0 < c.D) {k j : Fin 12}
    (h : ¬ 0 ≤ c.numY k j) : ¬ 0 ≤ c.Yof k j :=
  not_nonneg_Yof c hD (i := k) (k := j) h

theorem loTerm_eqR (c : HsumCert) (hD : 0 < c.D) {i k j : Fin 12} :
    RatInterval.loTerm (fun k => c.Yof k j) (fun k => c.Jof i k) k
      = ((if 0 ≤ c.numY k j then c.numY k j * c.loNum i k
            else c.numY k j * c.hiNum i k : ℤ) : ℚ) / (c.E : ℚ) := by
  simp only [RatInterval.loTerm, Jof, E]
  by_cases h : 0 ≤ c.numY k j
  · rw [if_pos h, if_pos (nonneg_Yof_col c hD h)]
    rw [show c.Yof k j = (c.numY k j : ℚ) / (c.D : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]
  · rw [if_neg h, if_neg (not_nonneg_Yof_col c hD h)]
    rw [show c.Yof k j = (c.numY k j : ℚ) / (c.D : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]

theorem hiTerm_eqR (c : HsumCert) (hD : 0 < c.D) {i k j : Fin 12} :
    RatInterval.hiTerm (fun k => c.Yof k j) (fun k => c.Jof i k) k
      = ((if 0 ≤ c.numY k j then c.numY k j * c.hiNum i k
            else c.numY k j * c.loNum i k : ℤ) : ℚ) / (c.E : ℚ) := by
  simp only [RatInterval.hiTerm, Jof, E]
  by_cases h : 0 ≤ c.numY k j
  · rw [if_pos h, if_pos (nonneg_Yof_col c hD h)]
    rw [show c.Yof k j = (c.numY k j : ℚ) / (c.D : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]
  · rw [if_neg h, if_neg (not_nonneg_Yof_col c hD h)]
    rw [show c.Yof k j = (c.numY k j : ℚ) / (c.D : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]

theorem sum_loTermR_eq (c : HsumCert) (hD : 0 < c.D) (i j : Fin 12) :
    (∑ k : Fin 12, RatInterval.loTerm (fun k => c.Yof k j) (fun k => c.Jof i k) k)
      = (c.loNumDR i j : ℚ) / (c.E : ℚ) := by
  rw [Finset.sum_congr rfl (fun k _ => loTerm_eqR c hD (i := i) (k := k) (j := j)),
    ← Finset.sum_div]
  congr 1
  simp only [loNumDR, Int.cast_sum]

theorem sum_hiTermR_eq (c : HsumCert) (hD : 0 < c.D) (i j : Fin 12) :
    (∑ k : Fin 12, RatInterval.hiTerm (fun k => c.Yof k j) (fun k => c.Jof i k) k)
      = (c.hiNumDR i j : ℚ) / (c.E : ℚ) := by
  rw [Finset.sum_congr rfl (fun k _ => hiTerm_eqR c hD (i := i) (k := k) (j := j)),
    ← Finset.sum_div]
  congr 1
  simp only [hiNumDR, Int.cast_sum]

/-- **右形式端点恒等式（`lo`）**：`(I − A·Y)_{ij}.lo = LNR / E`。 -/
theorem krawczykMatR_lo_eq (c : HsumCert) (hD : 0 < c.D)
    (hvalid : ∀ k j : Fin 12, c.loNum k j ≤ c.hiNum k j) (i j : Fin 12) :
    (krawczykMatR c.Jof c.Yof i j).lo = (c.LNR i j : ℚ) / (c.E : ℚ) := by
  have h := RatInterval.dot_hi_eq (c := fun k => c.Yof k j) (A := fun k => c.Jof i k)
    (fun k => Jof_valid c hD hvalid i k)
  rw [RatInterval.finRange_map_sum] at h
  show (if i = j then (1 : ℚ) else 0)
      - (RatInterval.dot (fun k => c.Yof k j) (fun k => c.Jof i k)).hi = _
  rw [h, sum_hiTermR_eq c hD i j]
  have hEne : (c.E : ℚ) ≠ 0 := ne_of_gt (Epos c hD)
  by_cases hij : i = j
  · simp only [hij, LNR]
    push_cast
    field_simp
  · simp only [if_neg hij, LNR]
    push_cast
    field_simp

/-- **右形式端点恒等式（`hi`）**：`(I − A·Y)_{ij}.hi = HNR / E`。 -/
theorem krawczykMatR_hi_eq (c : HsumCert) (hD : 0 < c.D)
    (hvalid : ∀ k j : Fin 12, c.loNum k j ≤ c.hiNum k j) (i j : Fin 12) :
    (krawczykMatR c.Jof c.Yof i j).hi = (c.HNR i j : ℚ) / (c.E : ℚ) := by
  have h := RatInterval.dot_lo_eq (c := fun k => c.Yof k j) (A := fun k => c.Jof i k)
    (fun k => Jof_valid c hD hvalid i k)
  rw [RatInterval.finRange_map_sum] at h
  show (if i = j then (1 : ℚ) else 0)
      - (RatInterval.dot (fun k => c.Yof k j) (fun k => c.Jof i k)).lo = _
  rw [h, sum_loTermR_eq c hD i j]
  have hEne : (c.E : ℚ) ≠ 0 := ne_of_gt (Epos c hD)
  by_cases hij : i = j
  · simp only [hij, HNR]
    push_cast
    field_simp
  · simp only [if_neg hij, HNR]
    push_cast
    field_simp

/-- **右侧 checker**（同样六条，改用 `rowZR`）。 -/
def checkR (c : HsumCert) : Bool :=
  decide (0 < c.D) && decide (0 < c.denK) && decide (0 ≤ c.numK)
    && decide (∀ k j : Fin 12, c.loNum k j ≤ c.hiNum k j)
    && decide (∀ i : Fin 12, c.rowZR i * c.denK ≤ c.numK * c.E)
    && decide (c.numK < c.denK)

/-- **右侧 soundness**：`checkR = true → hsumR ∧ 0 ≤ K' ∧ K' < 1`（`K' = numK/denK`）。 -/
theorem checkR_sound {c : HsumCert} (h : c.checkR = true) :
    (∀ i : Fin 12, ∑ j : Fin 12,
        max |((krawczykMatR c.Jof c.Yof i j).lo : ℝ)|
          |((krawczykMatR c.Jof c.Yof i j).hi : ℝ)|
        ≤ (c.numK : ℝ) / (c.denK : ℝ))
      ∧ (0 ≤ (c.numK : ℝ) / (c.denK : ℝ))
      ∧ ((c.numK : ℝ) / (c.denK : ℝ) < 1) := by
  simp only [checkR, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hD, hdenK⟩, hnumK⟩, hvalid⟩, hrow⟩, hK1⟩ := h
  have hKQ : (0 : ℚ) < (c.denK : ℚ) := by exact_mod_cast hdenK
  have hEpos := Epos c hD
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hrowQ : (∑ j : Fin 12,
          max |(c.LNR i j : ℚ) / (c.E : ℚ)| |(c.HNR i j : ℚ) / (c.E : ℚ)|)
        ≤ (c.numK : ℚ) / (c.denK : ℚ) := by
      have hZ : ((∑ j : Fin 12, max |c.LNR i j| |c.HNR i j| : ℤ) : ℚ)
          = ∑ j : Fin 12, max |(c.LNR i j : ℚ)| |(c.HNR i j : ℚ)| := by
        rw [Int.cast_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [int_cast_maxQ, int_cast_absQ, int_cast_absQ]
      have hcross : ((∑ j : Fin 12, max |(c.LNR i j : ℚ)| |(c.HNR i j : ℚ)|)) * (c.denK : ℚ)
          ≤ (c.numK : ℚ) * (c.E : ℚ) := by
        rw [← hZ, ← Int.cast_mul, ← Int.cast_mul]
        exact_mod_cast hrow i
      rw [Finset.sum_congr rfl (fun j _ => max_abs_div hEpos (c.LNR i j) (c.HNR i j)),
        ← Finset.sum_div]
      exact (div_le_div_iff₀ hEpos hKQ).mpr hcross
    have hcast := rat_cast_max_abs_sum (fun j => (c.LNR i j : ℚ)) (fun j => (c.HNR i j : ℚ))
      (c.E : ℚ)
    simp only [krawczykMatR_lo_eq c hD hvalid i, krawczykMatR_hi_eq c hD hvalid i, Rat.cast_div]
    rw [← hcast]
    exact_mod_cast hrowQ
  · have h0 : (0 : ℚ) ≤ (c.numK : ℚ) / (c.denK : ℚ) :=
      div_nonneg (by exact_mod_cast hnumK) hKQ.le
    exact_mod_cast h0
  · have h1 : (c.numK : ℚ) / (c.denK : ℚ) < 1 := by
      rw [div_lt_one hKQ]
      exact_mod_cast hK1
    exact_mod_cast h1

theorem certOK_rowZR (i : Fin 12) : certOK.rowZR i = 10 := by
  fin_cases i <;> decide

/-- **诚实实例（右形式）通过内核检查**：同一份 `Y`/`J` 数据产出 `hsumR`。 -/
theorem certOK_checkR : certOK.checkR = true := by decide

/-- **右形式的说谎见证被拒**：同一份数据、行和界压小 1（`numK = 9`）。 -/
theorem certLIE_checkR_rejected : certLIE.checkR = false := by decide

/-- 诚实实例的 `hsumR`（右侧收缩所需的形状）。 -/
theorem certOK_hsumR :
    ∀ i : Fin 12, ∑ j : Fin 12,
        max |((krawczykMatR certOK.Jof certOK.Yof i j).lo : ℝ)|
          |((krawczykMatR certOK.Jof certOK.Yof i j).hi : ℝ)|
        ≤ (certOK.numK : ℝ) / (certOK.denK : ℝ) :=
  (checkR_sound certOK_checkR).1

end HsumCert

end N11Formalization
