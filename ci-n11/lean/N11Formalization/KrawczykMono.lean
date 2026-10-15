import N11Formalization.Interval.Core
import N11Formalization.Interval.Vector
import N11Formalization.KrawczykMatrix
import N11Formalization.PrecondRight

/-!
# `KrawczykMono` — T8 关键证明件:`krawczykMat`/`krawczykMatR` 的 `Jt`-单调性 + B′ 网格外包 + 行和迁移

**只 import 具体模块**(不 import 伞件 `N11Formalization`)。命名一律 `km_` 前缀(与根内 0 撞名)。

## 单调性方向(全件口径)

`RatInterval.Contains I J`(Interval/Core.lean L118)= `I.lo ≤ J.lo ∧ J.hi ≤ I.hi`,即 **`I` 宽 `J` 窄**;
主定理:**更宽的 `Jt` ⇒ 更宽的 Krawczyk 逐格区间**:
`km_krawczykMat_mono : (∀ r c, Contains (JtW r c) (JtE r c)) → ∀ i j, Contains (krawczykMat Y JtW i j) (krawczykMat Y JtE i j)`。

## 沿 `krawczykMat` 计算树的逐层单调性审计(⚠ 必读)

`krawczykMat Y J i j = (ofRat δ_ij).sub (incrMat Y J i j)`,其中
`incrMat Y J i j = RatInterval.dot (Y i) (fun k => J k j)`,`dot c A = (List.finRange n).foldl (dotFold c A) (ofRat 0)`,
`dotFold c A acc k = acc.add ((ofRat (c k)).mul (A k))`(根内原文,#print 存证见同目录 `probe_check.out.txt`)。

| 层 | 运算 | 引理 | 条件 |
|---|---|---|---|
| 0 | `ofRat δ_ij`(常值) | `contains_refl` | 无 |
| 1 | `mul`(dotFold 内,第二槽 = `J` 格) | `km_mul_contains` | ⚠ **需紧侧 `Valid`**(见下反例) |
| 2 | `add`(foldl 步进) | `km_add_contains` | 无条件(端点独立相加) |
| 3 | `dot` = `finRange` 折叠 | `km_foldl_dot_contains` 归纳 | ⚠ 需**被折叠的每个 `J` 格 `Valid`** |
| 4 | `sub`(对第二槽反序) | `km_sub_contains` | 无条件 |

**不单调点精确报告**:
1. **`inv`/`div` 不在本计算树内**(`krawczykMat`/`krawczykMatR` 只用 `ofRat`/`mul`/`add`/`sub`)。
   零穿越敏感的除法只出现在 **`Jt''` 的数据构造侧**(`hessIvBox` 的 `invPos`/`invPos_mem_div`,
   `ResidualDerivD.lean` L35/L44)——属上游(T7 数据工程),**不在本引理的声明范围**。
2. **`mul` 的单调性需要紧侧 `Valid`**(`km_mul_contains` 显式前提)。无 `Valid` 反例:
   `A' = [0,1] ⊇ A = [5,1]`(A 非法)、`B = [2,3]` 时 `mul A B = [2,15] ⊄ [0,3] = mul A' B`。
   故主定理带显式假设 `hV : ∀ r c, Valid (JtE r c)`(**紧侧**合法;宽侧不需要)。
   **供给路线**(装配时):`hJ_box`(HJBoxInstant)在任一 `x ∈ closedBall certCR rhoCertR`(如球心)
   给出每格 `Mem`,经 `valid_of_mem`(Core.lean L109)得 `hV`;`km_valid_of_mem_all` 打包此路线。
3. `abs`(区间绝对值)不在树内,只出现在行和后处理;其迁移在 `km_rowTerm_mono` 用
   **`mem_of_contains`(Core.lean L121:方向 `Contains I J → Mem J x → Mem I x`,宽前窄后)** 处理,
   同样需窄侧 `Valid`(成员关系本身蕴含非空)。

## B′ 网格(Lead 已裁:D = 2^320)

`Jt_B := ⟨⌊lo·D⌋/D, ⌈hi·D⌉/D⟩`(逐格)= `km_gridTable D Jt`;`km_gridTable_contains` 给**全部 144 格**
`Contains Jt_B r c (Jt'' r c)`(无条件,只需 `0 < D`;端点不等式 = `Int.floor_le`/`Int.le_ceil` 的纯序事实,
ℚ 层内核证明;T7 字面量代入后的**已解析格**走 `km_contains_of_gridLiterals` + 逐格 `norm_num`,
校准读数见 §4 尾 example)。

## 行和迁移(hsum/hsumR 在 `Jt_B` 版与 `Jt''` 版之间)

方向(`mem_of_contains`,宽前窄后):`Contains (Jt_B 格) (Jt'' 格)` + `Valid (Jt'' 格)` ⇒
窄格端点成员搬到宽格 ⇒ `max |lo| |hi|` 逐项不增 ⇒ `Finset.sum_le_sum` ⇒
`hsum_B`(对 `Jt_B`)**迁移为** `hsum''`(对 `Jt''`);`hsumR` 同构(`km_hsumR_transfer*`)。
装配即:`nd_via_hyp` 的 `hsum`/`hsumR` 槽(对全称 `Jt`)实例化 `Jt := Jt''` 后,由
`km_hsum_transfer_grid`/`km_hsumR_transfer_grid` 从 B′ 版行和直接喂入。

判据口径:本件不打印(门 = exit 0 / stdout 0 B / stderr 0 B / 0 warning);
公理画像另置副本 `axioprint.lean`(含 `#print axioms`)。
-/

namespace N11Formalization

open RatInterval (Contains Mem Valid ofRat)

/-! ## 1. 原子单调性(ℚ 端点层) -/

/-- `add` 对两槽同时单调(无条件)。 -/
theorem km_add_contains {A' A B' B : RatInterval}
    (hA : Contains A' A) (hB : Contains B' B) : Contains (A'.add B') (A.add B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩
  · show A'.lo + B'.lo ≤ A.lo + B.lo
    linarith
  · show A.hi + B.hi ≤ A'.hi + B'.hi
    linarith

/-- `sub` 对第一槽保序、对第二槽反序(无条件;`B` 侧即"更宽的 `J` ⇒ 更宽的差")。 -/
theorem km_sub_contains {A' A B' B : RatInterval}
    (hA : Contains A' A) (hB : Contains B' B) : Contains (A'.sub B') (A.sub B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩
  · show A'.lo - B'.hi ≤ A.lo - B.hi
    linarith
  · show A.hi - B.lo ≤ A'.hi - B'.lo
    linarith

/-- **`mul` 对第二槽单调 —— ⚠ 需紧侧 `Valid`**(反例见件头;`mul` 的四角 min/max 定义要求
紧侧端点落进宽侧盒内,非法区间端点可越出 ⇒ 结论不真)。第一槽(`ofRat c`)在 `dotFold`
中恒为退化合法区间,故只需此单槽版本。 -/
theorem km_mul_contains {B' B : RatInterval} (A : RatInterval)
    (h : Contains B' B) (hV : Valid B) : Contains (A.mul B') (A.mul B) := by
  obtain ⟨h1, h2⟩ := h
  have hVq : B.lo ≤ B.hi := hV
  -- 紧侧两端点都落进宽侧盒内
  have hmid : ∀ t : ℚ, t = B.lo ∨ t = B.hi → B'.lo ≤ t ∧ t ≤ B'.hi := by
    intro t ht
    rcases ht with ht | ht
    · subst ht
      exact ⟨h1, le_trans hVq h2⟩
    · subst ht
      exact ⟨le_trans h1 hVq, h2⟩
  -- 固定外槽 a:内槽两端点的乘积被宽侧端点乘积夹住(按 a 的符号分派;ℚ 序域,无 cast)
  have hlo : ∀ a t : ℚ, (t = B.lo ∨ t = B.hi) → min (a * B'.lo) (a * B'.hi) ≤ a * t := by
    intro a t ht
    obtain ⟨ht1, ht2⟩ := hmid t ht
    rcases le_or_gt 0 a with ha | ha
    · have e : B'.lo * a ≤ t * a := mul_le_mul_of_nonneg_right ht1 ha
      rw [mul_comm B'.lo a, mul_comm t a] at e
      exact le_trans (min_le_left _ _) e
    · have e : B'.hi * a ≤ t * a := mul_le_mul_of_nonpos_right ht2 (le_of_lt ha)
      rw [mul_comm B'.hi a, mul_comm t a] at e
      exact le_trans (min_le_right _ _) e
  have hhi : ∀ a t : ℚ, (t = B.lo ∨ t = B.hi) → a * t ≤ max (a * B'.lo) (a * B'.hi) := by
    intro a t ht
    obtain ⟨ht1, ht2⟩ := hmid t ht
    rcases le_or_gt 0 a with ha | ha
    · have e : t * a ≤ B'.hi * a := mul_le_mul_of_nonneg_right ht2 ha
      rw [mul_comm t a, mul_comm B'.hi a] at e
      exact le_trans e (le_max_right _ _)
    · have e : t * a ≤ B'.lo * a := mul_le_mul_of_nonpos_right ht1 (le_of_lt ha)
      rw [mul_comm t a, mul_comm B'.lo a] at e
      exact le_trans e (le_max_left _ _)
  refine ⟨?_, ?_⟩
  · show min (min (A.lo * B'.lo) (A.lo * B'.hi)) (min (A.hi * B'.lo) (A.hi * B'.hi))
        ≤ min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi))
    refine min_le_min
      (le_min (hlo A.lo B.lo (Or.inl (rfl : B.lo = B.lo))) (hlo A.lo B.hi (Or.inr (rfl : B.hi = B.hi))))
      (le_min (hlo A.hi B.lo (Or.inl (rfl : B.lo = B.lo))) (hlo A.hi B.hi (Or.inr (rfl : B.hi = B.hi))))
  · show max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi))
        ≤ max (max (A.lo * B'.lo) (A.lo * B'.hi)) (max (A.hi * B'.lo) (A.hi * B'.hi))
    refine max_le_max
      (max_le (hhi A.lo B.lo (Or.inl (rfl : B.lo = B.lo))) (hhi A.lo B.hi (Or.inr (rfl : B.hi = B.hi))))
      (max_le (hhi A.hi B.lo (Or.inl (rfl : B.lo = B.lo))) (hhi A.hi B.hi (Or.inr (rfl : B.hi = B.hi))))

/-! ## 2. `dot` 折叠的单调性与合法性(归纳;累加器一般形) -/

/-- 折叠单调(累加器一般形):逐格 `Contains` + 逐格 `Valid`(紧侧)⇒ 折叠区间单调。 -/
theorem km_foldl_dot_contains {n : ℕ} (c : Fin n → ℚ) {A' A : Fin n → RatInterval}
    (hC : ∀ k : Fin n, Contains (A' k) (A k)) (hV : ∀ k : Fin n, Valid (A k)) :
    ∀ (l : List (Fin n)) (acc' acc : RatInterval), Contains acc' acc → Valid acc →
      Contains (l.foldl (RatInterval.dotFold c A') acc') (l.foldl (RatInterval.dotFold c A) acc) := by
  intro l
  induction l with
  | nil => intro acc' acc hacc _; exact hacc
  | cons i t ih =>
    intro acc' acc hacc haccV
    simp only [List.foldl_cons]
    refine ih (acc'.add ((ofRat (c i)).mul (A' i))) (acc.add ((ofRat (c i)).mul (A i)))
      (km_add_contains hacc (km_mul_contains (ofRat (c i)) (hC i) (hV i)))
      (RatInterval.add_valid haccV (RatInterval.mul_valid _ _))

/-- 折叠合法性(累加器一般形):逐格 `Valid` ⇒ 折叠区间合法。 -/
theorem km_foldl_dot_valid {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval)
    (_hV : ∀ k : Fin n, Valid (A k)) :
    ∀ (l : List (Fin n)) (acc : RatInterval), Valid acc →
      Valid (l.foldl (RatInterval.dotFold c A) acc) := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons i t ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    exact ih _ (RatInterval.add_valid hacc (RatInterval.mul_valid _ _))

/-- 层 3:`dot` 的单调性。 -/
theorem km_dot_contains {n : ℕ} (c : Fin n → ℚ) {A' A : Fin n → RatInterval}
    (hC : ∀ k : Fin n, Contains (A' k) (A k)) (hV : ∀ k : Fin n, Valid (A k)) :
    Contains (RatInterval.dot c A') (RatInterval.dot c A) :=
  km_foldl_dot_contains c hC hV (List.finRange n) (ofRat 0) (ofRat 0)
    (RatInterval.contains_refl _) (le_refl _)

/-- 层 3:`dot` 的合法性。 -/
theorem km_dot_valid {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval)
    (hV : ∀ k : Fin n, Valid (A k)) : Valid (RatInterval.dot c A) :=
  km_foldl_dot_valid c A hV (List.finRange n) (ofRat 0) (le_refl _)

/-! ## 3. 主单调性定理(层 4 收口) -/

/-- 层 4 前半:`incrMat`(=`dot` 沿 `Jt` 第 `j` 列)单调。 -/
theorem km_incrMat_mono {n : ℕ} (Y : Fin n → Fin n → ℚ)
    {JtW JtE : Fin n → Fin n → RatInterval}
    (hC : ∀ r c : Fin n, Contains (JtW r c) (JtE r c))
    (hV : ∀ r c : Fin n, Valid (JtE r c))
    (i j : Fin n) : Contains (incrMat Y JtW i j) (incrMat Y JtE i j) :=
  km_dot_contains (Y i) (fun k => hC k j) (fun k => hV k j)

/-- ★ **主单调性定理(`krawczykMat` 版)**:更宽的 `Jt` ⇒ 更宽的 Krawczyk 逐格区间。
条件全列:`hC` 逐格 `Contains`(宽⊇紧)+ `hV` 紧侧逐格 `Valid`(层 1 `mul` 所必需;反例见件头)。 -/
theorem km_krawczykMat_mono {n : ℕ} (Y : Fin n → Fin n → ℚ)
    {JtW JtE : Fin n → Fin n → RatInterval}
    (hC : ∀ r c : Fin n, Contains (JtW r c) (JtE r c))
    (hV : ∀ r c : Fin n, Valid (JtE r c))
    (i j : Fin n) : Contains (krawczykMat Y JtW i j) (krawczykMat Y JtE i j) := by
  simp only [krawczykMat]
  exact km_sub_contains (RatInterval.contains_refl _) (km_incrMat_mono Y hC hV i j)

/-- ★ **主单调性定理(右形 `krawczykMatR` 版)**:同构,折叠 `Jt` 第 `i` 行。 -/
theorem km_krawczykMatR_mono {n : ℕ} (Y : Fin n → Fin n → ℚ)
    {JtW JtE : Fin n → Fin n → RatInterval}
    (hC : ∀ r c : Fin n, Contains (JtW r c) (JtE r c))
    (hV : ∀ r c : Fin n, Valid (JtE r c))
    (i j : Fin n) : Contains (krawczykMatR JtW Y i j) (krawczykMatR JtE Y i j) := by
  simp only [krawczykMatR]
  exact km_sub_contains (RatInterval.contains_refl _)
    (km_dot_contains (fun k => Y k j) (fun k => hC i k) (fun k => hV i k))

/-! ## 3b. 逐格合法性(行和迁移的次前提) -/

theorem km_incrMat_valid {n : ℕ} (Y : Fin n → Fin n → ℚ)
    (JtE : Fin n → Fin n → RatInterval) (hV : ∀ r c : Fin n, Valid (JtE r c)) (i j : Fin n) :
    Valid (incrMat Y JtE i j) :=
  km_dot_valid (Y i) (fun k => JtE k j) (fun k => hV k j)

theorem km_krawczykMat_valid {n : ℕ} (Y : Fin n → Fin n → ℚ)
    (JtE : Fin n → Fin n → RatInterval) (hV : ∀ r c : Fin n, Valid (JtE r c)) (i j : Fin n) :
    Valid (krawczykMat Y JtE i j) := by
  simp only [krawczykMat]
  exact RatInterval.sub_valid (le_refl _) (km_incrMat_valid Y JtE hV i j)

theorem km_krawczykMatR_valid {n : ℕ} (Y : Fin n → Fin n → ℚ)
    (JtE : Fin n → Fin n → RatInterval) (hV : ∀ r c : Fin n, Valid (JtE r c)) (i j : Fin n) :
    Valid (krawczykMatR JtE Y i j) := by
  simp only [krawczykMatR]
  exact RatInterval.sub_valid (le_refl _)
    (km_dot_valid (fun k => Y k j) (fun k => JtE i k) (fun k => hV i k))

/-- `hV` 供给路线打包:每格 `Mem` 某实数 ⇒ 每格 `Valid`
(装配时对 `Jt''` 用 `HJBoxInstant.hJ_box` 在球心处实例化)。 -/
theorem km_valid_of_mem_all {n : ℕ} {Jt : Fin n → Fin n → RatInterval}
    {v : Fin n → Fin n → ℝ} (h : ∀ r c : Fin n, (Jt r c).Mem (v r c)) :
    ∀ r c : Fin n, Valid (Jt r c) :=
  fun r c => RatInterval.valid_of_mem (h r c)

/-! ## 4. B′ 网格(格 `2^-320`,`D = 2^320`) -/

/-- B′ 网格参数(Lead 已裁):`D = 2^320`,格点 = `m / D`(精确 dyadic)。 -/
def km_gridD : ℤ := ((2 ^ 320 : ℕ) : ℤ)

theorem km_gridD_pos : 0 < km_gridD := by
  show (0 : ℤ) < ((2 ^ 320 : ℕ) : ℤ)
  have h : (0 : ℕ) < 2 ^ 320 := by norm_num
  omega

/-- 格点向下取格:`km_gridDown D q = ⌊q·D⌋ / D ≤ q`(需 `0 < D`)。 -/
def km_gridDown (D : ℤ) (q : ℚ) : ℚ := ((Int.floor (q * (D : ℚ)) : ℚ)) / (D : ℚ)

/-- 格点向上取格:`q ≤ ⌈q·D⌉ / D = km_gridUp D q`(需 `0 < D`)。 -/
def km_gridUp (D : ℤ) (q : ℚ) : ℚ := ((Int.ceil (q * (D : ℚ)) : ℚ)) / (D : ℚ)

theorem km_gridDown_le (D : ℤ) (hD : 0 < D) (q : ℚ) : km_gridDown D q ≤ q := by
  have hDq : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hf := Int.floor_le (q * (D : ℚ))
  show ((Int.floor (q * (D : ℚ)) : ℚ)) / (D : ℚ) ≤ q
  rw [div_le_iff₀ hDq]
  exact hf

theorem km_le_gridUp (D : ℤ) (hD : 0 < D) (q : ℚ) : q ≤ km_gridUp D q := by
  have hDq : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hc := Int.le_ceil (q * (D : ℚ))
  show q ≤ ((Int.ceil (q * (D : ℚ)) : ℚ)) / (D : ℚ)
  rw [le_div_iff₀ hDq]
  exact hc

/-- **B′ 网格引理**:`⟨⌊lo⌋_g, ⌈hi⌉_g⟩ ⊇ ⟨lo, hi⟩`(ℚ 层,无条件,只需 `0 < D`)。 -/
theorem km_contains_grid (D : ℤ) (hD : 0 < D) (lo hi : ℚ) :
    Contains ⟨km_gridDown D lo, km_gridUp D hi⟩ ⟨lo, hi⟩ :=
  ⟨km_gridDown_le D hD lo, km_le_gridUp D hD hi⟩

/-- **B′ 外包表**(逐格;消费点 12×12 = 144 格)。 -/
def km_gridTable {n : ℕ} (D : ℤ) (Jt : Fin n → Fin n → RatInterval) :
    Fin n → Fin n → RatInterval :=
  fun r c => ⟨km_gridDown D (Jt r c).lo, km_gridUp D (Jt r c).hi⟩

/-- ★ **144 格通用引理**:每格 `Contains (Jt_B r c) (Jt r c)`(无条件,只需 `0 < D`)。
T7 字面量代入后的已解析格:同一形状经 `km_contains_of_gridLiterals` + 逐格 `norm_num`。 -/
theorem km_gridTable_contains {n : ℕ} (D : ℤ) (hD : 0 < D)
    (Jt : Fin n → Fin n → RatInterval) (r c : Fin n) :
    Contains (km_gridTable D Jt r c) (Jt r c) :=
  km_contains_grid D hD (Jt r c).lo (Jt r c).hi

/-- **T7 已解析格插口**:端点字面量代入后,`Contains ⟨m/D, n/D⟩ ⟨lo, hi⟩` 就是两条 ℚ 不等式。 -/
theorem km_contains_of_gridLiterals {lo hi : ℚ} {m n D : ℤ}
    (hm : ((m : ℚ) / (D : ℚ)) ≤ lo) (hn : hi ≤ ((n : ℚ) / (D : ℚ))) :
    Contains ⟨((m : ℚ) / (D : ℚ)), ((n : ℚ) / (D : ℚ))⟩ ⟨lo, hi⟩ :=
  ⟨hm, hn⟩

/-- 校准读数(D = 8 的真实取格:`⌊(2/5)·8⌋/8 = 3/8`,`⌈(11/10)·8⌉/8 = 9/8`;
同一 `norm_num` 路径在 `D = 2^320` 与 T7 的 98 个端点上逐格同样适用)。 -/
example : Contains ⟨(3 : ℚ) / 8, (9 : ℚ) / 8⟩ ⟨(2 : ℚ) / 5, (11 : ℚ) / 10⟩ := by
  norm_num [Contains]

/-- 校准读数(取格算子本身接入:`km_gridDown 8 (2/5) = 3/8`、`km_gridUp 8 (11/10) = 9/8`)。 -/
example : Contains ⟨km_gridDown 8 (2 / 5), km_gridUp 8 (11 / 10)⟩
    ⟨(2 : ℚ) / 5, (11 : ℚ) / 10⟩ := by
  simp only [km_gridDown, km_gridUp]
  norm_num [Contains]

/-! ## 5. 行和迁移(hsum / hsumR) -/

/-- `Mem I x ⇒ |x| ≤ max |I.lo| |I.hi|`(ℝ 层)。 -/
theorem km_abs_le_maxAbs_of_mem {I : RatInterval} {x : ℝ} (h : I.Mem x) :
    |x| ≤ max |(I.lo : ℝ)| |(I.hi : ℝ)| := by
  have hlo := RatInterval.mem_lo_le h
  have hhi := RatInterval.mem_le_hi h
  have b1 := neg_abs_le (I.lo : ℝ)
  have b2 := le_abs_self (I.lo : ℝ)
  have b3 := neg_abs_le (I.hi : ℝ)
  have b4 := le_abs_self (I.hi : ℝ)
  have b5 := le_max_left (abs (I.lo : ℝ)) (abs (I.hi : ℝ))
  have b6 := le_max_right (abs (I.lo : ℝ)) (abs (I.hi : ℝ))
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

/-- **行和单项迁移**(`mem_of_contains` 方向:宽前窄后,Core.lean L121)。
`Contains W E`(W 宽 E 窄)+ `Valid E` ⇒ `max |lo_E| |hi_E| ≤ max |lo_W| |hi_W|`:
E 的两端点是 E 的成员(`mem_iff` + `Valid`),经 `mem_of_contains` 搬进 W,再收 |·| 界。 -/
theorem km_rowTerm_mono {W E : RatInterval} (h : Contains W E) (hV : Valid E) :
    max |(E.lo : ℝ)| |(E.hi : ℝ)| ≤ max |(W.lo : ℝ)| |(W.hi : ℝ)| := by
  have hloE : E.Mem ((E.lo : ℝ)) := RatInterval.mem_iff.mpr ⟨le_refl _, by exact_mod_cast hV⟩
  have hhiE : E.Mem ((E.hi : ℝ)) := RatInterval.mem_iff.mpr ⟨by exact_mod_cast hV, le_refl _⟩
  exact max_le (km_abs_le_maxAbs_of_mem (RatInterval.mem_of_contains h hloE))
    (km_abs_le_maxAbs_of_mem (RatInterval.mem_of_contains h hhiE))

/-- ★ **hsum 迁移**(`krawczykMat` 版):逐格 `Contains` + 紧侧逐格 `Valid` ⇒
`hsum`(宽表)⇒ `hsum`(紧表)。消费点 `nd_via_hyp` 的 `hsum` 槽即此形状(`Jt` 全称)。 -/
theorem km_hsum_transfer {n : ℕ} (Y : Fin n → Fin n → ℚ) {K : ℝ}
    {JtW JtE : Fin n → Fin n → RatInterval}
    (hC : ∀ r c : Fin n, Contains (JtW r c) (JtE r c))
    (hV : ∀ r c : Fin n, Valid (JtE r c))
    (hsumW : ∀ i : Fin n, ∑ j : Fin n,
      max |((krawczykMat Y JtW i j).lo : ℝ)| |((krawczykMat Y JtW i j).hi : ℝ)| ≤ K) :
    ∀ i : Fin n, ∑ j : Fin n,
      max |((krawczykMat Y JtE i j).lo : ℝ)| |((krawczykMat Y JtE i j).hi : ℝ)| ≤ K :=
  fun i =>
  le_trans (Finset.sum_le_sum fun j _ =>
    km_rowTerm_mono (km_krawczykMat_mono Y hC hV i j) (km_krawczykMat_valid Y JtE hV i j))
    (hsumW i)

/-- ★ **hsumR 迁移**(`krawczykMatR` 版,同构)。 -/
theorem km_hsumR_transfer {n : ℕ} (Y : Fin n → Fin n → ℚ) {K : ℝ}
    {JtW JtE : Fin n → Fin n → RatInterval}
    (hC : ∀ r c : Fin n, Contains (JtW r c) (JtE r c))
    (hV : ∀ r c : Fin n, Valid (JtE r c))
    (hsumRW : ∀ i : Fin n, ∑ j : Fin n,
      max |((krawczykMatR JtW Y i j).lo : ℝ)| |((krawczykMatR JtW Y i j).hi : ℝ)| ≤ K) :
    ∀ i : Fin n, ∑ j : Fin n,
      max |((krawczykMatR JtE Y i j).lo : ℝ)| |((krawczykMatR JtE Y i j).hi : ℝ)| ≤ K :=
  fun i =>
  le_trans (Finset.sum_le_sum fun j _ =>
    km_rowTerm_mono (km_krawczykMatR_mono Y hC hV i j) (km_krawczykMatR_valid Y JtE hV i j))
    (hsumRW i)

/-- ★ **B′ 消费形(hsum)**:行和在 `Jt_B = km_gridTable km_gridD Jt` 上 ≤ K ⇒
`Jt` 版 `hsum` 成立(单调性 + 迁移一次完成;`hV` 由 `km_valid_of_mem_all` ∘ `hJ_box` 供给)。 -/
theorem km_hsum_transfer_grid {n : ℕ} (Y : Fin n → Fin n → ℚ) {K : ℝ}
    (Jt : Fin n → Fin n → RatInterval) (hV : ∀ r c : Fin n, Valid (Jt r c))
    (hsumB : ∀ i : Fin n, ∑ j : Fin n,
      max |((krawczykMat Y (km_gridTable km_gridD Jt) i j).lo : ℝ)|
        |((krawczykMat Y (km_gridTable km_gridD Jt) i j).hi : ℝ)| ≤ K) :
    ∀ i : Fin n, ∑ j : Fin n,
      max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K :=
  km_hsum_transfer Y (fun r c => km_gridTable_contains km_gridD km_gridD_pos Jt r c) hV hsumB

/-- ★ **B′ 消费形(hsumR)**。 -/
theorem km_hsumR_transfer_grid {n : ℕ} (Y : Fin n → Fin n → ℚ) {K : ℝ}
    (Jt : Fin n → Fin n → RatInterval) (hV : ∀ r c : Fin n, Valid (Jt r c))
    (hsumRB : ∀ i : Fin n, ∑ j : Fin n,
      max |((krawczykMatR (km_gridTable km_gridD Jt) Y i j).lo : ℝ)|
        |((krawczykMatR (km_gridTable km_gridD Jt) Y i j).hi : ℝ)| ≤ K) :
    ∀ i : Fin n, ∑ j : Fin n,
      max |((krawczykMatR Jt Y i j).lo : ℝ)| |((krawczykMatR Jt Y i j).hi : ℝ)| ≤ K :=
  km_hsumR_transfer Y (fun r c => km_gridTable_contains km_gridD km_gridD_pos Jt r c) hV hsumRB

end N11Formalization
