/-
  N11Formalization.Interval.Vector
  ================================

  M1–M4（root-audit 第 1 步 `K(B) ⊆ B` 的骨架）：
  * M1 `abs`：区间绝对值（含端点公式与 `Valid` 保持）；
  * M2 `dot`：**有限点积**（`Fin n` 上的有理系数线性组合）的包含性。用 `List.finRange`
    折叠实现，避免引入 `Finset`/`AddCommMonoid RatInterval` 实例；折叠引理对任意
    `List (Fin n)` 陈述，故也覆盖子列表/重排的用法；
  * M3 `supNorm`：上确界范数（`hull` 折叠 `abs`），含包含性；
  * M4 `BoxIncl`：盒包含封装（`K(B) ⊆ B` 化成逐分量有理不等式）；
  * 附 `krawczykAffine` / `krawczykAffineR`：Krawczyk 算子的**仿射骨架**
    `K_i = m_i − Σ_j Y_ij·Fm_j + Σ_j M_ij·(x_j − m_j)`。

  口径说明（关键，勿误读）：`Fm`（`F(m)` 的区间包）与 `M = I − Y·J(B)`（有理系数矩阵）
  是**输入数据**。`Fm` 之所以是区间而不是有理点值，是因为真正的 `F` 含 `sin/cos`，
  其点值不是有理数（那一块是 M5，缺口见 `INTERVAL-GAPS.md`）；矩阵 `M` 之所以作为
  有理系数传入，是因为 `J(B)` 的区间求值属 M5 之后的义务。本节**不**假装已能评估 `F` 或 `J`。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval`。
-/
import Mathlib
import N11Formalization.Interval.Core
import N11Formalization.Interval.Sqrt

namespace N11Formalization

namespace RatInterval

variable {A B : RatInterval} {x : ℝ}

/-! ## M1 区间绝对值 -/

/-- 区间绝对值（外向）：包住 `{|x| : x ∈ A}` 的区间。 -/
def abs (A : RatInterval) : RatInterval :=
  ⟨if 0 ≤ A.lo then A.lo else if A.hi ≤ 0 then -A.hi else 0, max (-A.lo) A.hi⟩

theorem abs_mem (hA : Mem A x) : Mem A.abs |x| := by
  have hlo := mem_lo_le hA
  have hhi := mem_le_hi hA
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show ((if 0 ≤ A.lo then A.lo else if A.hi ≤ 0 then -A.hi else 0 : ℚ) : ℝ) ≤ |x|
    by_cases h1 : 0 ≤ A.lo
    · rw [if_pos h1]
      have h1' : (0 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h1
      rw [abs_of_nonneg (le_trans h1' hlo)]
      exact hlo
    · rw [if_neg h1]
      by_cases h2 : A.hi ≤ 0
      · rw [if_pos h2]
        have h2' : (A.hi : ℝ) ≤ 0 := by exact_mod_cast h2
        rw [abs_of_nonpos (le_trans hhi h2')]
        push_cast
        linarith
      · rw [if_neg h2]
        push_cast
        exact abs_nonneg x
  · show |x| ≤ ((max (-A.lo) A.hi : ℚ) : ℝ)
    rw [Rat.cast_max]
    push_cast
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hm : -(max (-(A.lo : ℝ)) (A.hi : ℝ)) ≤ (A.lo : ℝ) := by
        linarith [le_max_left (-(A.lo : ℝ)) (A.hi : ℝ)]
      linarith
    · exact le_trans hhi (le_max_right _ _)

theorem abs_valid (hA : Valid A) : Valid A.abs := by
  have hA' : A.lo ≤ A.hi := hA
  show (if 0 ≤ A.lo then A.lo else if A.hi ≤ 0 then -A.hi else 0) ≤ max (-A.lo) A.hi
  by_cases h1 : 0 ≤ A.lo
  · rw [if_pos h1]
    linarith [hA', le_max_right (-A.lo) A.hi]
  · rw [if_neg h1]
    by_cases h2 : A.hi ≤ 0
    · rw [if_pos h2]
      linarith [hA', le_max_left (-A.lo) A.hi]
    · rw [if_neg h2]
      have hpos : (0 : ℚ) < -A.lo := neg_pos.mpr (not_le.mp h1)
      linarith [le_max_left (-A.lo) A.hi]

/-! ## M1' 区间凸包 `hull`（上确界范数折叠用） -/

/-- 两区间的凸包（并集的区间闭包）。 -/
def hull (A B : RatInterval) : RatInterval := ⟨min A.lo B.lo, max A.hi B.hi⟩

theorem contains_hull_left (A B : RatInterval) : Contains (hull A B) A := by
  refine ⟨?_, ?_⟩
  · show min A.lo B.lo ≤ A.lo
    exact min_le_left _ _
  · show A.hi ≤ max A.hi B.hi
    exact le_max_left _ _

theorem contains_hull_right (A B : RatInterval) : Contains (hull A B) B := by
  refine ⟨?_, ?_⟩
  · show min A.lo B.lo ≤ B.lo
    exact min_le_right _ _
  · show B.hi ≤ max A.hi B.hi
    exact le_max_right _ _

theorem hull_mem_left {x : ℝ} (h : Mem A x) : Mem (hull A B) x :=
  mem_of_contains (contains_hull_left A B) h

theorem hull_mem_right {x : ℝ} (h : Mem B x) : Mem (hull A B) x :=
  mem_of_contains (contains_hull_right A B) h

theorem hull_valid (hA : Valid A) (hB : Valid B) : Valid (hull A B) := by
  have hA' : A.lo ≤ A.hi := hA
  have hB' : B.lo ≤ B.hi := hB
  show min A.lo B.lo ≤ max A.hi B.hi
  linarith [min_le_left A.lo B.lo, min_le_right A.lo B.lo, le_max_left A.hi B.hi,
    le_max_right A.hi B.hi, hA', hB']

/-- 上确界范数的单步引理：`y ∈ acc`、`z ∈ A` ⟹ `max y |z| ∈ hull acc A.abs`。
（`supNorm` 的区间侧与实数侧端点形状不同，故需要这条专门的单步引理。） -/
theorem hull_abs_mem {acc : RatInterval} {y z : ℝ} (hacc : Mem acc y) (hA : Mem A z) :
    Mem (hull acc A.abs) (max y |z|) := by
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show ((min acc.lo A.abs.lo : ℚ) : ℝ) ≤ max y |z|
    push_cast
    linarith [mem_lo_le hacc, min_le_left (acc.lo : ℝ) (A.abs.lo : ℝ), le_max_left y |z|]
  · show max y |z| ≤ ((max acc.hi A.abs.hi : ℚ) : ℝ)
    rw [Rat.cast_max]
    exact max_le (le_trans (mem_le_hi hacc) (le_max_left (acc.hi : ℝ) (A.abs.hi : ℝ)))
      (le_trans (mem_le_hi (abs_mem hA)) (le_max_right (acc.hi : ℝ) (A.abs.hi : ℝ)))

/-! ## M2 有限点积 -/

/-- 点积的区间侧折叠函数：`acc + c_i · A_i`。 -/
def dotFold {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval) : RatInterval → Fin n → RatInterval :=
  fun acc i => acc.add ((ofRat (c i)).mul (A i))

/-- 点积的实数侧折叠函数：`acc + c_i · x_i`。 -/
def dotFoldR {n : ℕ} (c : Fin n → ℚ) (x : Fin n → ℝ) : ℝ → Fin n → ℝ :=
  fun acc i => acc + (c i : ℝ) * x i

/-- 列表版点积（对任意 `List (Fin n)`；`dot` 取 `List.finRange n`）。 -/
def dotL {n : ℕ} (l : List (Fin n)) (c : Fin n → ℚ) (A : Fin n → RatInterval) : RatInterval :=
  l.foldl (dotFold c A) (ofRat 0)

/-- 列表版点积的实数语义。 -/
def dotLR {n : ℕ} (l : List (Fin n)) (c : Fin n → ℚ) (x : Fin n → ℝ) : ℝ :=
  l.foldl (dotFoldR c x) 0

/-- **有限点积**（`Fin n` 上的有理系数线性组合）。 -/
def dot {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval) : RatInterval :=
  dotL (List.finRange n) c A

/-- 点积的实数语义。 -/
def dotR {n : ℕ} (c : Fin n → ℚ) (x : Fin n → ℝ) : ℝ :=
  dotLR (List.finRange n) c x

theorem dot_eq_dotL {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval) :
    dot c A = dotL (List.finRange n) c A := rfl

theorem dotR_eq_dotLR {n : ℕ} (c : Fin n → ℚ) (x : Fin n → ℝ) :
    dotR c x = dotLR (List.finRange n) c x := rfl

/-- 折叠引理（累加器一般化）：逐项用 `mul_mem` + `add_mem`。 -/
theorem foldl_dot_mem {n : ℕ} (c : Fin n → ℚ) (A : Fin n → RatInterval) (x : Fin n → ℝ)
    (hx : ∀ i, Mem (A i) (x i)) (l : List (Fin n)) (acc : RatInterval) (y : ℝ)
    (hy : Mem acc y) :
    Mem (l.foldl (dotFold c A) acc) (l.foldl (dotFoldR c x) y) := by
  induction l generalizing acc y with
  | nil => simpa using hy
  | cons i t ih =>
    simp only [List.foldl_cons]
    exact ih (dotFold c A acc i) (dotFoldR c x y i)
      (add_mem hy (mul_mem (ofRat_mem (c i)) (hx i)))

/-- **点积包含性**：`∀i, A_i ∋ x_i ⟹ dot c A ∋ Σ_i c_i x_i`（此处写成折叠形式）。 -/
theorem dot_mem {n : ℕ} {c : Fin n → ℚ} {A : Fin n → RatInterval} {x : Fin n → ℝ}
    (hx : ∀ i, Mem (A i) (x i)) : Mem (dot c A) (dotR c x) :=
  foldl_dot_mem c A x hx (List.finRange n) (ofRat 0) 0 (by simpa using ofRat_mem (0 : ℚ))

theorem dotL_mem {n : ℕ} {l : List (Fin n)} {c : Fin n → ℚ} {A : Fin n → RatInterval}
    {x : Fin n → ℝ} (hx : ∀ i, Mem (A i) (x i)) : Mem (dotL l c A) (dotLR l c x) :=
  foldl_dot_mem c A x hx l (ofRat 0) 0 (by simpa using ofRat_mem (0 : ℚ))

/-! ## M3 上确界范数 -/

/-- 上确界范数的区间侧折叠函数：`hull acc (|A_i|)`。 -/
def supFold {n : ℕ} (A : Fin n → RatInterval) : RatInterval → Fin n → RatInterval :=
  fun acc i => hull acc (A i).abs

/-- 上确界范数的实数侧折叠函数：`max acc |x_i|`。 -/
def supFoldR {n : ℕ} (x : Fin n → ℝ) : ℝ → Fin n → ℝ :=
  fun acc i => max acc |x i|

/-- 上确界范数（区间）。 -/
def supNorm {n : ℕ} (A : Fin n → RatInterval) : RatInterval :=
  (List.finRange n).foldl (supFold A) (ofRat 0)

/-- 上确界范数的实数语义 `max(0, max_i |x_i|)`（`max_i |x_i| ≥ 0`，故与 `max_i |x_i|` 一致）。 -/
def supNormR {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl (supFoldR x) 0

theorem foldl_sup_mem {n : ℕ} (A : Fin n → RatInterval) (x : Fin n → ℝ)
    (hx : ∀ i, Mem (A i) (x i)) (l : List (Fin n)) (acc : RatInterval) (y : ℝ)
    (hy : Mem acc y) :
    Mem (l.foldl (supFold A) acc) (l.foldl (supFoldR x) y) := by
  induction l generalizing acc y with
  | nil => simpa using hy
  | cons i t ih =>
    simp only [List.foldl_cons]
    exact ih (supFold A acc i) (supFoldR x y i) (hull_abs_mem hy (hx i))

/-- **上确界范数包含性**：`∀i, A_i ∋ x_i ⟹ supNorm A ∋ max_i |x_i|`（折叠形式）。 -/
theorem supNorm_mem {n : ℕ} {A : Fin n → RatInterval} {x : Fin n → ℝ}
    (hx : ∀ i, Mem (A i) (x i)) : Mem (supNorm A) (supNormR x) :=
  foldl_sup_mem A x hx (List.finRange n) (ofRat 0) 0 (by simpa using ofRat_mem (0 : ℚ))

theorem supNorm_valid {n : ℕ} {A : Fin n → RatInterval} (h : ∀ i, Valid (A i)) :
    Valid (supNorm A) := by
  have key : ∀ (l : List (Fin n)) (acc : RatInterval), Valid acc →
      Valid (l.foldl (supFold A) acc) := by
    intro l
    induction l with
    | nil => intro acc hacc; simpa using hacc
    | cons i t ih =>
      intro acc hacc
      simp only [List.foldl_cons, supFold]
      exact ih _ (hull_valid hacc (abs_valid (h i)))
  exact key (List.finRange n) (ofRat 0) (le_refl 0)

/-! ## M4 盒包含 -/

/-- 盒包含：`BoxIncl A B` = 「A 比 B 窄」（逐分量 A_i ⊆ B_i）。 -/
def BoxIncl {n : ℕ} (A B : Fin n → RatInterval) : Prop := ∀ i, Contains (B i) (A i)

theorem BoxIncl.mem {n : ℕ} {A B : Fin n → RatInterval} (h : BoxIncl A B) {x : Fin n → ℝ}
    (hx : ∀ i, Mem (A i) (x i)) : ∀ i, Mem (B i) (x i) :=
  fun i => mem_of_contains (h i) (hx i)

theorem BoxIncl.refl {n : ℕ} (A : Fin n → RatInterval) : BoxIncl A A :=
  fun i => contains_refl (A i)

theorem BoxIncl.trans {n : ℕ} {A B C : Fin n → RatInterval} (h₁ : BoxIncl A B) (h₂ : BoxIncl B C) :
    BoxIncl A C :=
  fun i => (h₂ i).trans (h₁ i)

/-- `K(B) ⊆ B` 的判定就是**逐分量有理不等式**（下游用精确有理算术收尾）。 -/
theorem boxIncl_iff {n : ℕ} {A B : Fin n → RatInterval} :
    BoxIncl A B ↔ ∀ i, (B i).lo ≤ (A i).lo ∧ (A i).hi ≤ (B i).hi :=
  Iff.rfl

/-! ## K(B) 的仿射骨架 -/

/-- Krawczyk 算子的**仿射骨架**（区间侧）：
`K_i = m_i − Σ_j Y_ij·Fm_j + Σ_j M_ij·(B_j − m_j)`。 -/
def krawczykAffine {n : ℕ} (Y : Fin n → Fin n → ℚ) (Fm : Fin n → RatInterval)
    (M : Fin n → Fin n → ℚ) (m : Fin n → ℚ) (B : Fin n → RatInterval) : Fin n → RatInterval :=
  fun i => ((ofRat (m i)).sub (dot (Y i) Fm)).add
    (dot (M i) (fun j => (B j).sub (ofRat (m j))))

/-- 仿射骨架的实数语义（同一表达式树，系数做强转）。 -/
def krawczykAffineR {n : ℕ} (Y : Fin n → Fin n → ℚ) (FmR : Fin n → ℝ)
    (M : Fin n → Fin n → ℚ) (m : Fin n → ℚ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ((m i : ℝ) - dotR (Y i) FmR) + dotR (M i) (fun j => x j - (m j : ℝ))

/-- **仿射骨架的包含性（端到端）**：
`Fm_j ∋ FmR_j` 且 `B_j ∋ x_j` ⇒ 逐分量 `K_i ∋ (m_i − Σ Y_ij FmR_j + Σ M_ij (x_j − m_j))`。 -/
theorem krawczykAffine_mem {n : ℕ} (Y : Fin n → Fin n → ℚ) (Fm : Fin n → RatInterval)
    (FmR : Fin n → ℝ) (M : Fin n → Fin n → ℚ) (m : Fin n → ℚ) (B : Fin n → RatInterval)
    (x : Fin n → ℝ) (hF : ∀ j, Mem (Fm j) (FmR j)) (hx : ∀ j, Mem (B j) (x j)) (i : Fin n) :
    Mem (krawczykAffine Y Fm M m B i) (krawczykAffineR Y FmR M m x i) :=
  add_mem (sub_mem (ofRat_mem (m i)) (dot_mem hF))
    (dot_mem (fun j => sub_mem (hx j) (ofRat_mem (m j))))

/-! ## 读数：2 变量仿射切片（收缩型样例）

数据：`m = 0`、`B = [-1,1]²`、`Fm = [1/2,1/2]²`、`Y = (1/2)·𝟙`、`M = (1/4)·𝟙`。
则 `K_i = (0 − (1/2)·(1/2)·2) + (1/4)·(B_0 − 0) + (1/4)·(B_1 − 0) = −1/2 + [−1/2, 1/2] = [−1, 0]`，
故 `K(B) ⊆ B`（贴着左端点相切）；这是「一步 Krawczyk 收缩」的 1 维等价物，
用来把「区间化 → 逐分量有理不等式」整条路走到底。 -/

def mZ : Fin 2 → ℚ := fun _ => 0

def boxUnit : Fin 2 → RatInterval := fun _ => intv (-1) 1

def fmHalf : Fin 2 → RatInterval := fun _ => intv (1 / 2) (1 / 2)

def YHalf : Fin 2 → Fin 2 → ℚ := fun _ _ => 1 / 2

def MQuarter : Fin 2 → Fin 2 → ℚ := fun _ _ => 1 / 4

/-- 读数：`dot` 在 2 维常数数据上算到底（`(1/2)·[1/2,1/2] + (1/2)·[1/2,1/2] = [1/2,1/2]`）。 -/
theorem read_dot_half : dot (YHalf 0) fmHalf = intv (1 / 2) (1 / 2) := by
  simp only [dot, dotL, YHalf, fmHalf, dotFold, List.finRange_succ, List.finRange_zero,
    List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, RatInterval.intv,
    RatInterval.add, RatInterval.mul, RatInterval.ofRat]
  norm_num

/-- 读数（切片第 0 分量）：`K_0 = [−1, 0]`。 -/
theorem read_krawczyk_K0 : krawczykAffine YHalf fmHalf MQuarter mZ boxUnit 0 = intv (-1) 0 := by
  simp only [krawczykAffine, dot, dotL, YHalf, MQuarter, mZ, fmHalf, boxUnit, dotFold,
    List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, RatInterval.intv, RatInterval.sub, RatInterval.add, RatInterval.mul,
    RatInterval.ofRat]
  norm_num

/-- 读数（切片第 1 分量）：同一数据的 `K_1 = [−1, 0]`。 -/
theorem read_krawczyk_K1 : krawczykAffine YHalf fmHalf MQuarter mZ boxUnit 1 = intv (-1) 0 := by
  simp only [krawczykAffine, dot, dotL, YHalf, MQuarter, mZ, fmHalf, boxUnit, dotFold,
    List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, RatInterval.intv, RatInterval.sub, RatInterval.add, RatInterval.mul,
    RatInterval.ofRat]
  norm_num

/-- 读数（切片端到端）：`K(B) ⊆ B` 在该 2 维切片上成立（`BoxIncl` = 逐分量有理不等式）。 -/
theorem read_krawczyk_incl : BoxIncl (krawczykAffine YHalf fmHalf MQuarter mZ boxUnit) boxUnit := by
  intro i
  fin_cases i <;>
    simp only [krawczykAffine, dot, dotL, YHalf, MQuarter, mZ, fmHalf, boxUnit,
      dotFold, List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, RatInterval.intv, RatInterval.sub, RatInterval.add,
      RatInterval.mul, RatInterval.ofRat, RatInterval.Contains] <;>
    norm_num

end RatInterval

end N11Formalization
