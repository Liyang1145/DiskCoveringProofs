import N11Formalization.BoxRstar
import N11Formalization.Interval.Vector
import N11Formalization.HessSeamMain

/-!
# Lead：**λ 盒 ＋ 区间系数点积**（KKT×z 块的正确口径 ✓）

**为什么需要它**（R177–R179 三处查证 ✓）：
* 球级**链式法则**（`KktZFderivAny.fderiv_TCSystem_kkt_z_any` ✓）：
  `(fderiv TCSystem x (Pi.single (up7 j) 1)) (kkt12 i) = -(Σ mm, (last5 x mm) * hessEntryAt (first7 x) i j mm)` ✓
  ⇒ 权重 `last5 x` **随 `x` 变** ✗（固定的 `lamRat` 只在**球心**成立 ✓）
* `RatInterval.dot` 的系数是**有理向量**（`Vector.lean` L145 ✓）✗ ⇒ 本件补**区间系数**版 ✓

**本件**：`lamBox`（λ 盒 ✓）／`lamBox_mem`（由球取逐坐标范围 ✓）／`dotIv`／`dotIvR`／`dotIv_mem`（逐字镜像 `dot`／`dotR`／`foldl_dot_mem`／`dot_mem` ✓）。

**写法口径**（本轮实测 ✓，两条都是本件编译错误的**真因**）：
1. **命名空间**：`Mem`／`ofRat`／`add_mem`／`mul_mem` 全在 `N11Formalization.RatInterval` 里 ⇒
   本件必须 `open RatInterval`（同 `NondegProof` L71／`HessSeamBall` L27 ✓）。只 `open N11Formalization` 时
   裸 `Mem` 是**未知标识符**，被 `autoImplicit`（默认开）当成隐式绑定的未知变量 ⇒ 报
   `Function expected at Mem`；`RatInterval.add`／`RatInterval.mul` 的**全名写法从来没错**（同族报错全落在 `Mem` 上）。
2. **端点比较**：`linarith` 的原子比较**不展开普通 `def`**（只在 reducible 层比），故
   `rhoCertR` 与 `((rhoCert:ℚ):ℝ)` 被判成**两个原子**（最小反例：`h : -rhoCertR ≤ x - c` ⊢ `c - ↑rhoCert ≤ x` 失败；
   同项目 `HessSeamBall` L37–38 已记过同一坑 ✓）⇒ 必须先把两侧 `rw` 成**同一符号**再 `linarith`。
   反之 `Fin` 字面量的**证明分量**不同**不**妨碍 `linarith`（proof irrelevance 抹平；实测 `last5 x mm` 与
   `x ⟨↑mm+7, by omega⟩` 可作同一原子）——本件仍把下标固定成局部变量 `idx` ＋ `Fin.ext` 显式索引桥，
   使 `linarith` 两侧原子**逐字相同**（不依赖任何 defeq 行为）。
判据：**exit=0 且输出 0 行**。
-/

namespace N11Formalization.Lead.LamBox

open N11Formalization

open RatInterval

/-! ## 1. λ 盒 -/

/-- **λ 盒**：第 `mm` 维 = 证书球内坐标 `7+mm` 的范围 ✓（两端皆有理 ✓）。 -/
noncomputable def lamBox (mm : Fin 5) : RatInterval :=
  RatInterval.mk (certC ⟨(mm : ℕ) + 7, by omega⟩ - rhoCert)
    (certC ⟨(mm : ℕ) + 7, by omega⟩ + rhoCert)

/-- `(lamBox mm).Mem (last5 x mm)`（只用 `x ∈ closedBall certCR rhoCertR` ✓）。

**写法**：把 `Fin` 下标固定成局部变量 `idx`（`hidx : ↑idx = ↑mm + 7`），再用 `Fin.ext` 桥
`last5 x mm = x idx` 与 `↑(certC ⟨↑mm+7, ⋯⟩) = certCR idx` ⇒ 端点不等式两侧的原子（`x idx`、
`certCR idx`、`rhoCertR`）由**同一批局部项**给出，`linarith` 不再面对"同值不同形"的 `Fin` 证明分量 ✓。 -/
theorem lamBox_mem (x : Fin 12 → ℝ) (hx : x ∈ Metric.closedBall certCR rhoCertR) (mm : Fin 5) :
    (lamBox mm).Mem (last5 x mm) := by
  have hdist : dist x certCR ≤ rhoCertR := Metric.mem_closedBall.mp hx
  have hcoord : ∀ i : Fin 12, |x i - certCR i| ≤ rhoCertR := by
    intro i
    have h := (dist_pi_le_iff rhoCertR_pos.le (f := x) (g := certCR)).mp hdist i
    simpa [Real.dist_eq] using h
  obtain ⟨idx, hidx⟩ : ∃ i : Fin 12, (i : ℕ) = (mm : ℕ) + 7 :=
    ⟨⟨(mm : ℕ) + 7, by omega⟩, rfl⟩
  have hmm := abs_le.mp (hcoord idx)
  have hlast : last5 x mm = x idx := by
    simp only [last5]
    exact congrArg x (Fin.ext (by simpa using hidx.symm))
  have hcert : ((certC ⟨(mm : ℕ) + 7, by omega⟩ : ℚ) : ℝ) = certCR idx :=
    congrArg (fun i : Fin 12 => ((certC i : ℚ) : ℝ)) (Fin.ext (by simpa using hidx.symm))
  have hlo : (((lamBox mm).lo : ℚ) : ℝ) = certCR idx - rhoCertR := by
    rw [lamBox, Rat.cast_sub, hcert]
    rfl
  have hhi : (((lamBox mm).hi : ℚ) : ℝ) = certCR idx + rhoCertR := by
    rw [lamBox, Rat.cast_add, hcert]
    rfl
  refine RatInterval.mem_iff.mpr ⟨?_, ?_⟩
  · rw [hlo, hlast]
    linarith [hmm.1]
  · rw [hhi, hlast]
    linarith [hmm.2]

/-! ## 2. 区间系数点积（镜像根内 `dot`／`dot_mem` ✓） -/

/-- 区间侧折叠（镜像 `dotFold` L130 ✓）：`acc + c_i · A_i` ✓（全名写法 ✓）。 -/
def dotIvFold {n : ℕ} (c : Fin n → RatInterval) (A : Fin n → RatInterval) :
    RatInterval → Fin n → RatInterval :=
  fun acc i => RatInterval.add acc (RatInterval.mul (c i) (A i))

/-- 实数侧折叠（镜像 `dotFoldR` L133 ✓）：`acc + λ_i · x_i` ✓。 -/
def dotIvFoldR {n : ℕ} (lam : Fin n → ℝ) (x : Fin n → ℝ) : ℝ → Fin n → ℝ :=
  fun acc i => acc + lam i * x i

/-- 区间系数点积 ✓。 -/
def dotIv {n : ℕ} (c : Fin n → RatInterval) (A : Fin n → RatInterval) : RatInterval :=
  (List.finRange n).foldl (dotIvFold c A) (RatInterval.ofRat 0)

/-- 区间系数点积的实数语义 ✓。 -/
def dotIvR {n : ℕ} (lam : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl (dotIvFoldR lam x) 0

/-- 折叠引理（镜像 `foldl_dot_mem` L159 ✓）。 -/
theorem foldl_dotIv_mem {n : ℕ} (c : Fin n → RatInterval) (A : Fin n → RatInterval)
    (lam : Fin n → ℝ) (x : Fin n → ℝ) (hc : ∀ i, Mem (c i) (lam i)) (hx : ∀ i, Mem (A i) (x i))
    (l : List (Fin n)) (acc : RatInterval) (y : ℝ) (hy : Mem acc y) :
    Mem (l.foldl (dotIvFold c A) acc) (l.foldl (dotIvFoldR lam x) y) := by
  induction l generalizing acc y with
  | nil => simpa using hy
  | cons i t ih =>
    simp only [List.foldl_cons]
    exact ih (dotIvFold c A acc i) (dotIvFoldR lam x y i)
      (RatInterval.add_mem hy (RatInterval.mul_mem (hc i) (hx i)))

/-- **区间系数点积包含性** ✓（镜像 `dot_mem` L171 ✓）。 -/
theorem dotIv_mem {n : ℕ} {c : Fin n → RatInterval} {A : Fin n → RatInterval}
    {lam : Fin n → ℝ} {x : Fin n → ℝ} (hc : ∀ i, Mem (c i) (lam i))
    (hx : ∀ i, Mem (A i) (x i)) : Mem (dotIv c A) (dotIvR lam x) :=
  foldl_dotIv_mem c A lam x hc hx (List.finRange n) (RatInterval.ofRat 0) 0
    (by simpa using RatInterval.ofRat_mem (0 : ℚ))

end N11Formalization.Lead.LamBox
