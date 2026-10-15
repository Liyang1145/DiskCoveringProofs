/-
  N11Formalization.IntervalAD
  ===========================

  **区间自动微分层（一元）**：在 `Interval/*` 的精确有理区间内核之上，把「值 + 导数」二重区间
  `AD := RatInterval × RatInterval` 与其**可靠性**（soundness）做成可证的层。

  口径（诚实标注，勿高估）
  ------------------------
  * **一元**：`AD` 描述 `ℝ → ℝ` 的一元函数 `f` 的 `f x` 与 `deriv f x`。**不含**
    多变量偏导矩阵（12 维 Jacobian 包络）——那是后续任务，本文件不声称完成。
  * 区间端点**精确有理** `ℚ`，语义在 **ℝ 侧**（`Mem`）。
  * **规则只有「值盒 → 值盒」与「值盒 → 导盒」两个算子**（`vf`、`dfv`），
    两者的可靠性都只以**值盒的成员**为前提：
      `vsound I y : Mem I y → Mem (vf I) (f y)`；
      `dfv_sound I y : Mem I y → Mem (dfv I) (fp y)`。
    这是本轮调试得到的关键设计（DEAD.md C⁵/R21）：区间 AD 的**斜率达**（slope form）
    只需值盒即可算导数包络。若像早先版本那样让导数算子同时吃「值盒 + 输入导盒 `D`」，
    则 `comp` 的组合步要求「`c.fp (s.f x)` 落在 `s` 的**输出导盒**里」——
    而手头只有「`s.fp x` 落在该盒里」，且 `Mem D (a*b)` 推不出 `Mem D a`
    （区间不可约去），组合子在**语义**上就不自洽（不只是类型形状问题）。
    改成 `dfv` 后，`comp` 的 `dfv` 为 `(c.dfv (s.vf V)) · (s.dfv V)`，
    分别由 `c.dfv_sound`（配 `s.vsound`）与 `s.dfv_sound` 供给，组合无障碍落地。
  * **递归可靠性用 `fp`（定点导数），不嵌 `deriv`**：否则 `comp` 处出现无法消解的 `Eq.rec`
    （`deriv (fun y => c.f (s.f y)) x` 与 `c.fp (s.f x) * s.fp x` 不是定义相等）。

  ## 缺口（如实登记，不冒充已证；均为**实现限制不是数学反例**）
  * `sqrt`：非退化前提需要 `0 < I.lo ⟹ 0 < I.sqrt.lo`（素材在 Core/Sqrt.lean 的
    `sqrtLo_sq_le`/`sqrtLo_nonneg`/`sqrtLo_le_sqrt`，卡在 `↑(I.sqrt.lo)` 的字段记法展开）。
    缺口精确陈述为 `sqrtGapStatement`。
  * `pow`：`dfv I = (ofRat n) · I.pow (n-1)` 需要 `0 ≤ I.lo` 才能用 Core 的 `pow_mem`，
    而 `dfv_sound` 对**任意**值盒成立，故未给。缺口陈述为 `powGapStatement`。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval` 当证明。
-/
import Mathlib
import N11Formalization.Interval

namespace N11Formalization

namespace RatInterval

/-! ## 1. 二重区间与语义 -/

/-- **值 + 导数二重区间**。 -/
structure AD where
  /-- 值区间（包 `f x`）。 -/
  v : RatInterval
  /-- 导数区间（包 `deriv f x`）。 -/
  d : RatInterval
  deriving DecidableEq, Repr

/-- **AD 侧语义**。 -/
def ADMem (A : AD) (x dx : ℝ) : Prop := Mem A.v x ∧ Mem A.d dx

theorem ADMem.v_mem (h : ADMem A x dx) : Mem A.v x := h.1

theorem ADMem.d_mem (h : ADMem A x dx) : Mem A.d dx := h.2

/-- 合法性。 -/
def AD.Valid (A : AD) : Prop := RatInterval.Valid A.v ∧ RatInterval.Valid A.d

theorem AD.valid_of_mem (h : ADMem A x dx) : A.Valid :=
  ⟨RatInterval.valid_of_mem (I := A.v) h.1, RatInterval.valid_of_mem (I := A.d) h.2⟩

/-- `Mem (ofRat q) (q : ℝ)`：本工程下直接把 `ofRat_mem` 用在 ℝ 目标上会卡在
`(ofRat q).Mem ↑q` vs `….Mem q`，故显式经 `mem_iff` 给出（`q` 的类型注记必须写全）。 -/
theorem ofRat_memR (q : ℚ) : Mem (ofRat q) (q : ℝ) :=
  mem_iff.mpr ⟨le_refl _, le_refl _⟩

/-! ## 2. 规则类型与链式法则（唯一组合子） -/
structure ADRule where
  /-- 实函数。 -/
  f : ℝ → ℝ
  /-- 定点导数。 -/
  fp : ℝ → ℝ
  /-- 值区间算子。 -/
  vf : RatInterval → RatInterval
  /-- 导函数在**值盒**上的包络（斜率达）。 -/
  dfv : RatInterval → RatInterval
  /-- `vf` 的可靠性。 -/
  vsound : ∀ (I : RatInterval) (y : ℝ), Mem I y → Mem (vf I) (f y)
  /-- `dfv` 的可靠性。 -/
  dfv_sound : ∀ (I : RatInterval) (y : ℝ), Mem I y → Mem (dfv I) (fp y)
  /-- `deriv` 的定值。 -/
  hderiv_spec : ∀ x : ℝ, HasDerivAt f (fp x) x
  /-- `deriv` 的定值（推论形式）。 -/
  hderiv : ∀ x : ℝ, deriv f x = fp x
  /-- 值区间合法。 -/
  vvalid : ∀ (I : RatInterval), Valid I → Valid (vf I)
  /-- `dfv` 合法。 -/
  dfv_valid : ∀ (I : RatInterval), Valid I → Valid (dfv I)

namespace ADRule

/-- 规则的「按点取值」：值盒 `Box.v` 同时决定值区间与导数区间。 -/
def move (s : ADRule) (Box : AD) (_y : ℝ) : AD :=
  ⟨s.vf Box.v, s.dfv Box.v⟩

/-- `move` 对点参数常值。 -/
theorem move_const (s : ADRule) (Box : AD) (x y : ℝ) : s.move Box x = s.move Box y := rfl

/-- 规则作用一次的可靠性（`fp` 版本）：只需值盒含点。 -/
theorem move_sound_fp (s : ADRule) {Box : AD} {x : ℝ} (h : Mem Box.v x) :
    ADMem (s.move Box x) (s.f x) (s.fp x) :=
  ⟨s.vsound Box.v x h, s.dfv_sound Box.v x h⟩

/-- 规则作用一次的可靠性（`deriv` 版本，终端形状）。 -/
theorem move_sound (s : ADRule) {Box : AD} {x : ℝ} (h : Mem Box.v x) :
    ADMem (s.move Box x) (s.f x) (deriv s.f x) :=
  s.hderiv x ▸ s.move_sound_fp h

theorem valid_move (s : ADRule) {Box : AD} {x : ℝ} (h : Mem Box.v x) :
    (s.move Box x).Valid :=
  ⟨s.vvalid Box.v (valid_of_mem h), s.dfv_valid Box.v (valid_of_mem h)⟩

/-- **链式法则**（唯一组合子）。
`dfv V = (c.dfv (s.vf V)) · (s.dfv V)`：内层导数 `s.fp x` 由 `s.dfv V` 包住，
外层 `c.fp` 在 `s` 的值像上由 `c.dfv (s.vf V)` 包住，相乘即链式导数
`c.fp (s.f x) * s.fp x`。**不需要**任何「输出导盒」参与，故组合无 defeq 障碍。 -/
def comp (c s : ADRule) : ADRule where
  f := fun x => c.f (s.f x)
  fp := fun x => c.fp (s.f x) * s.fp x
  vf := fun I => c.vf (s.vf I)
  dfv := fun I => (c.dfv (s.vf I)).mul (s.dfv I)
  vsound := fun I y h => c.vsound (s.vf I) (s.f y) (s.vsound I y h)
  dfv_sound := fun I y h =>
    mul_mem (c.dfv_sound (s.vf I) (s.f y) (s.vsound I y h)) (s.dfv_sound I y h)
  hderiv_spec := fun x =>
    HasDerivAt.comp x (c.hderiv_spec (s.f x)) (s.hderiv_spec x)
  hderiv := fun x => (HasDerivAt.comp x (c.hderiv_spec (s.f x)) (s.hderiv_spec x)).deriv
  vvalid := fun I h => c.vvalid (s.vf I) (s.vvalid I h)
  dfv_valid := fun I _ => mul_valid (c.dfv (s.vf I)) (s.dfv I)

/-- 在**规则**上左乘有理系数，用于 `(1/2)·f` 这类最外层变换。 -/
def scale (c : ℚ) (s : ADRule) : ADRule where
  f := fun x => (c : ℝ) * s.f x
  fp := fun x => (c : ℝ) * s.fp x
  vf := fun I => (ofRat c).mul (s.vf I)
  dfv := fun I => (ofRat c).mul (s.dfv I)
  vsound := fun I y h => mul_mem ((by simpa using ofRat_memR c)) (s.vsound I y h)
  dfv_sound := fun I y h => mul_mem ((by simpa using ofRat_memR c)) (s.dfv_sound I y h)
  hderiv_spec := fun x => (s.hderiv_spec x).const_mul (c : ℝ)
  hderiv := fun x => ((s.hderiv_spec x).const_mul (c : ℝ)).deriv
  vvalid := fun I _ => mul_valid (ofRat c) (s.vf I)
  dfv_valid := fun I _ => mul_valid (ofRat c) (s.dfv I)

end ADRule

/-! ## 3. 规则实例（`const` / `id` / `add` / `neg` / `sub` / `mul`(平方) / `sin` / `cos`） -/

/-- 恒等 `f(x) = x`，`deriv = 1`。 -/
def rule_id : ADRule where
  f := fun x => x
  fp := fun _ => 1
  vf := fun I => I
  dfv := fun _ => ofRat 1
  vsound := fun I y h => h
  dfv_sound := fun I y _ => (by simpa using ofRat_memR (1 : ℚ))
  hderiv_spec := fun x => hasDerivAt_id x
  hderiv := fun x => (hasDerivAt_id x).deriv
  vvalid := fun I h => h
  dfv_valid := fun _ _ => le_refl (1 : ℚ)

/-- 常数 `f(x) = q`，`deriv = 0`。 -/
def rule_const (q : ℚ) : ADRule where
  f := fun _ => (q : ℝ)
  fp := fun _ => 0
  vf := fun _ => ofRat q
  dfv := fun _ => ofRat 0
  vsound := fun _ _ _ => (by simpa using ofRat_memR q)
  dfv_sound := fun _ _ _ => (by simpa using ofRat_memR (0 : ℚ))
  hderiv_spec := fun x => hasDerivAt_const (x := x) (q : ℝ)
  hderiv := fun x => (hasDerivAt_const (x := x) (q : ℝ)).deriv
  vvalid := fun _ _ => le_refl q
  dfv_valid := fun _ _ => le_refl (0 : ℚ)

/-- 加法 `f(x) = x + x`，`deriv = 1 + 1`（= 2，写在有理层以免 `cast` 归约）。 -/
def rule_add : ADRule where
  f := fun x => x + x
  fp := fun _ => 1 + 1
  vf := fun I => I.add I
  dfv := fun _ => (ofRat 1).add (ofRat 1)
  vsound := fun I y h => add_mem h h
  dfv_sound := fun I y _ => add_mem ((by simpa using ofRat_memR (1 : ℚ))) ((by simpa using ofRat_memR (1 : ℚ)))
  hderiv_spec := fun x => (hasDerivAt_id x).add (hasDerivAt_id x)
  hderiv := fun x => (((hasDerivAt_id x).add (hasDerivAt_id x))).deriv
  vvalid := fun I h => add_valid h h
  dfv_valid := fun _ _ => le_refl (1 + 1 : ℚ)

/-- 取负 `f(x) = -x`，`deriv = -1`。 -/
def rule_neg : ADRule where
  f := fun x => -x
  fp := fun _ => -1
  vf := fun I => I.neg
  dfv := fun _ => (ofRat 1).neg
  vsound := fun I y h => neg_mem h
  dfv_sound := fun I y _ => neg_mem ((by simpa using ofRat_memR (1 : ℚ)))
  hderiv_spec := fun x => (hasDerivAt_id x).neg
  hderiv := fun x => ((hasDerivAt_id x).neg).deriv
  vvalid := fun I h => neg_valid h
  dfv_valid := fun _ _ => le_refl (-(1 : ℚ))

/-- 减法 `f(x) = x - x`，`deriv = 1 - 1`（= 0）。 -/
def rule_sub : ADRule where
  f := fun x => x - x
  fp := fun _ => 1 - 1
  vf := fun I => I.sub I
  dfv := fun _ => (ofRat 1).sub (ofRat 1)
  vsound := fun I y h => sub_mem h h
  dfv_sound := fun I y _ => sub_mem ((by simpa using ofRat_memR (1 : ℚ))) ((by simpa using ofRat_memR (1 : ℚ)))
  hderiv_spec := fun x => (hasDerivAt_id x).sub (hasDerivAt_id x)
  hderiv := fun x => (((hasDerivAt_id x).sub (hasDerivAt_id x))).deriv
  vvalid := fun I h => sub_valid h h
  dfv_valid := fun _ _ => le_refl (1 - 1 : ℚ)

/-- **乘积法则**的二重区间算子：值 `A.v·B.v`；导 `A.d·B.v + A.v·B.d`（`f'·g + f·g'`）。

这是**二元**算子（不是 `ADRule`），故导出侧直接吃两个二重区间；
其可靠性 `mulAD_mem` 用分离前提陈述，避开「`Box.d` 与派生盒定义相等」的坑。 -/
def mulAD (A B : AD) : AD :=
  ⟨A.v.mul B.v, (A.d.mul B.v).add (A.v.mul B.d)⟩

/-- **乘积法则可靠性**：`f x ∈ A.v`、`g x ∈ B.v`、`deriv f x ∈ A.d`、`deriv g x ∈ B.d`
⟹ `f x·g x ∈ (mulAD A B).v` 且 `deriv (f·g) x = f' x·g x + f x·g' x ∈ (mulAD A B).d`。 -/
theorem mulAD_mem {f g : ℝ → ℝ} {A B : AD} {x : ℝ}
    (hf : HasDerivAt f (deriv f x) x) (hg : HasDerivAt g (deriv g x) x)
    (hAv : Mem A.v (f x)) (hAd : Mem A.d (deriv f x))
    (hBv : Mem B.v (g x)) (hBd : Mem B.d (deriv g x)) :
    Mem (mulAD A B).v (f x * g x) ∧ Mem (mulAD A B).d (deriv (f * g) x) := by
  have hderiv : deriv (f * g) x = deriv f x * g x + f x * deriv g x := (hf.mul hg).deriv
  constructor
  · exact mul_mem hAv hBv
  · rw [hderiv]
    exact add_mem (mul_mem hAd hBv) (mul_mem hAv hBd)

/-- **平方规则** `f(x) = x²`（乘积法则在 `id·id` 上的实例）：`deriv = 1·x + x·1`。
`dfv I = 1·I + I·1`（把上式的 `x` 换成值盒 `I`）。 -/
def rule_sq : ADRule where
  f := fun x => (id * id : ℝ → ℝ) x
  fp := fun x => 1 * x + x * 1
  vf := fun I => I.mul I
  dfv := fun I => ((ofRat 1).mul I).add (I.mul (ofRat 1))
  vsound := fun I y h => mul_mem h h
  dfv_sound := fun I y h => add_mem (mul_mem ((by simpa using ofRat_memR (1 : ℚ))) h) (mul_mem h ((by simpa using ofRat_memR (1 : ℚ))))
  hderiv_spec := fun x => by
    have h : HasDerivAt (id * id) (1 * x + x * 1) x := by
      simpa using ((hasDerivAt_id x).mul (hasDerivAt_id x))
    exact h
  hderiv := fun x => (((hasDerivAt_id x).mul (hasDerivAt_id x))).deriv
  vvalid := fun I _ => mul_valid I I
  dfv_valid := fun I _ => add_valid (mul_valid (ofRat 1) I) (mul_valid I (ofRat 1))

/-! ### 3.1 sin / cos 规则（可计算窗口支：`sinI`/`cosI`） -/

theorem sinI_valid {I : RatInterval} (h : Valid I) : Valid (sinI I) :=
  valid_of_mem (sinI_mem (A := I) (x := (I.lo : ℝ))
    (mem_iff.mpr ⟨le_refl _, Rat.cast_le.mpr h⟩))

theorem cosI_valid {I : RatInterval} (h : Valid I) : Valid (cosI I) :=
  valid_of_mem (cosI_mem (A := I) (x := (I.lo : ℝ))
    (mem_iff.mpr ⟨le_refl _, Rat.cast_le.mpr h⟩))

/-- **`sin` 规则**：`D sin = cos`。值区间 `sinI I`，导数区间 `cosI I`。 -/
noncomputable def sinAD : ADRule where
  f := Real.sin
  fp := Real.cos
  vf := sinI
  dfv := cosI
  vsound := fun I y h => sinI_mem (A := I) (x := y) h
  dfv_sound := fun I y h => cosI_mem (A := I) (x := y) h
  hderiv_spec := fun x => Real.hasDerivAt_sin x
  hderiv := fun x => (Real.hasDerivAt_sin x).deriv
  vvalid := fun _ h => sinI_valid h
  dfv_valid := fun _ h => cosI_valid h

/-- **`cos` 规则**：`D cos = -sin`。值区间 `cosI I`，导数区间 `(sinI I).neg`。 -/
noncomputable def cosAD : ADRule where
  f := Real.cos
  fp := fun x => -Real.sin x
  vf := cosI
  dfv := fun I => (sinI I).neg
  vsound := fun I y h => cosI_mem (A := I) (x := y) h
  dfv_sound := fun I y h => neg_mem (sinI_mem (A := I) (x := y) h)
  hderiv_spec := fun x => Real.hasDerivAt_cos x
  hderiv := fun x => (Real.hasDerivAt_cos x).deriv
  vvalid := fun _ h => cosI_valid h
  dfv_valid := fun _ h => neg_valid (sinI_valid h)

/-! ## 4. 端到端切片：`f(x) = sin x` 在有理盒 `[1/8, 1/4]` 上

`boxA.v = [1/8, 1/4]`，点取 `x₀ = (1/4 : ℚ)`。用 `ADRule.move_sound` 一次给出
值区间与导数区间，并读出闭式端点。 -/
def x0 : ℝ := ((1 / 4 : ℚ) : ℝ)

def boxA : AD := ⟨intv (1 / 8) (1 / 4), intv (1 / 8) (1 / 4)⟩

theorem boxA_v : Mem boxA.v x0 := by
  norm_num [boxA, intv, Mem, toSet, x0]

/-- 端到端（值）：值区间含 `sin x₀`。 -/
theorem e2e_value : Mem (sinAD.move boxA x0).v (sinAD.f x0) :=
  (sinAD.move_sound boxA_v).1

/-- 端到端（导数）：导数区间含 `deriv sin x₀ = cos x₀`。 -/
theorem e2e_deriv : Mem (sinAD.move boxA x0).d (deriv sinAD.f x0) :=
  (sinAD.move_sound boxA_v).2

/-- 端到端（值闭式读数）：值区间 = `⟨sinLo (1/8), sinHi (1/4)⟩`。 -/
theorem e2e_value_closed : (sinAD.move boxA x0).v = ⟨sinLo (1/8), sinHi (1/4)⟩ := by
  norm_num [ADRule.move, sinAD, boxA, intv, sinI]

/-- 端到端（导闭式读数）：导数区间 = `⟨cosLo (1/4), cosHi 0⟩`。 -/
theorem e2e_deriv_closed : (sinAD.move boxA x0).d = ⟨cosLo (1/4), cosHi 0⟩ := by
  norm_num [ADRule.move, sinAD, boxA, intv, cosI]

/-- 与 Core 点级规格的交叉读数（值侧）：`sinLo (1/4) ≤ sin ↑(1/4) ≤ sinHi (1/4)`。 -/
theorem e2e_value_spec :
    ((sinLo (1/4) : ℚ) : ℝ) ≤ Real.sin ((1/4 : ℚ) : ℝ) ∧
      Real.sin ((1/4 : ℚ) : ℝ) ≤ ((sinHi (1/4) : ℚ) : ℝ) :=
  ⟨sinLo_le_sin (q := 1/4) (by norm_num [abs_of_nonneg]),
   sin_le_sinHi (q := 1/4) (by norm_num [abs_of_nonneg])⟩

/-- 与 Core 点级规格的交叉读数（导侧）：`cosLo (1/4) ≤ cos ↑(1/4) ≤ cosHi 0 = 1`。 -/
theorem e2e_deriv_spec :
    ((cosLo (1/4) : ℚ) : ℝ) ≤ Real.cos ((1/4 : ℚ) : ℝ) ∧
      Real.cos ((1/4 : ℚ) : ℝ) ≤ ((cosHi 0 : ℚ) : ℝ) :=
  ⟨cosLo_le_cos (q := 1/4) (by norm_num [abs_of_nonneg]),
   by
     have h : Real.cos ((1/4 : ℚ) : ℝ) ≤ (1 : ℝ) := Real.cos_le_one _
     simpa [cosHi_zero] using h⟩

/-! ## 5. 缺口（精确陈述；均为**实现限制不是数学反例**）

* `sqrt` 的导数规则需要 `0 < I.lo ⟹ 0 < I.sqrt.lo`（ℝ 级），素材在 Core/Sqrt.lean
  的 `sqrtLo_sq_le`/`sqrtLo_nonneg`/`sqrtLo_le_sqrt`，卡在 `↑(I.sqrt.lo)` 的字段记法展开。
* `pow` 的导数包络 `(ofRat n) · I.pow (n-1)` 需要 `0 ≤ I.lo` 才能用 Core 的 `pow_mem`
  （`pow_mem` 的前提正是 base `lo` 非负），而 `dfv_sound` 要对**任意**值盒成立。 -/
def sqrtGapStatement : Prop :=
  ∀ (I : RatInterval), 0 < I.lo → (0 : ℚ) < I.sqrt.lo

def powGapStatement : Prop :=
  ∀ (I : RatInterval) (n : ℕ), 1 ≤ n → 0 ≤ I.lo → (0 : ℚ) < (I.pow (n - 1)).lo

end RatInterval

end N11Formalization
