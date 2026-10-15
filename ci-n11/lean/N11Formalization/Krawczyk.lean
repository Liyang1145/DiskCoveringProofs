import Mathlib

-- 风格 linter：本文件在 Prop 目标下需要**实例**形式的 `Nonempty`/`CompleteSpace`（球子类型），
-- 故保留 `haveI`；这只影响 `have`/`haveI` 的书写偏好，不影响证明内容。
set_option linter.style.haveILetI false

/-!
# Krawczyk 的 Banach 收缩步（GUIDE §3 的 Root 模块内核；**不依赖区间库**）

root-audit 的结论（`evidence/root/ROOT-CERT-AUDIT.md`）：C891 的根存在唯一**不需要 Brouwer**——
只要 `g = id − Y·F` 在闭球 `B(c,ρ)` 上是 `K`-收缩、映球入球、且起点残差足够小，
Banach 直接给出**存在唯一**。本文件把这个"收缩步"做成**无条件、通用、内核检查**的定理，
从而把 G1 的剩余义务精确化为「证明三条区间不等式」（见 §末尾注释）。

**真实等级**：kernel-proved，无条件（除显式前提）；零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

/-- **Krawczyk 收缩步（Banach 形式）**。

设 `E` 是完备实赋范空间，`F : E → E`，`Y : E →L[ℝ] E` **单射**，`g x = x − Y (F x)`。
若在闭球 `B(c,ρ)` 上：
* `hlip` —— `g` 的 Lipschitz 界 `K < 1`（区间侧由 `‖I − Y·J(X)‖ ≤ K` 给出）；
* `hres` —— **Krawczyk 残差条件** `η + K·ρ < ρ`，其中 `η = dist c (g c) = ‖Y (F c)‖`；

则 `F` 在 `B(c,ρ)` 内有**唯一**零点。

包含性 `g(B) ⊆ B`（"Krawczyk 包含"）**在本定理内部由 `hlip + hres` 推出**：
`dist (g x) c ≤ dist (g x) (g c) + dist (g c) c ≤ K·dist x c + η ≤ K·ρ + η < ρ`。
不需要 Brouwer：`Y` 单射把 `g` 的不动点变成 `F` 的零点，唯一性来自 `g` 在球上的收缩不动点唯一性。 -/
theorem krawczyk_banach {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : E → E) (Y : E →L[ℝ] E) (hY : Function.Injective Y)
    (c : E) (ρ K : ℝ) (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hlip : ∀ x ∈ closedBall c ρ, ∀ y ∈ closedBall c ρ,
      dist (x - Y (F x)) (y - Y (F y)) ≤ K * dist x y)
    (hres : dist c (c - Y (F c)) + K * ρ < ρ) :
    ∃! x : E, x ∈ closedBall c ρ ∧ F x = 0 := by
  classical
  have hcs : c ∈ closedBall c ρ := by
    rw [mem_closedBall]; simpa using hρ.le
  -- 由 `hlip + hres` 推出 Krawczyk 包含 `g(B) ⊆ B`
  have hmap : ∀ x ∈ closedBall c ρ, x - Y (F x) ∈ closedBall c ρ := by
    intro x hx
    rw [mem_closedBall]
    have h3 : dist x c ≤ ρ := by rwa [mem_closedBall] at hx
    have h2 : dist (x - Y (F x)) (c - Y (F c)) ≤ K * dist x c := hlip x hx c hcs
    have h4 : K * dist x c ≤ K * ρ := mul_le_mul_of_nonneg_left h3 hK0
    have h5 : dist (x - Y (F x)) c ≤ dist (x - Y (F x)) (c - Y (F c)) + dist (c - Y (F c)) c :=
      dist_triangle _ _ _
    have h6 : dist (c - Y (F c)) c = dist c (c - Y (F c)) := dist_comm _ _
    linarith
  haveI : Nonempty ↥(closedBall c ρ) := ⟨⟨c, hcs⟩⟩
  haveI : CompleteSpace ↥(closedBall c ρ) := by
    rw [completeSpace_coe_iff_isComplete]
    exact isClosed_closedBall.isComplete
  set g : ↥(closedBall c ρ) → ↥(closedBall c ρ) :=
    fun x => ⟨x.1 - Y (F x.1), hmap x.1 x.2⟩ with hgdef
  have hglip : LipschitzWith (⟨K, hK0⟩ : NNReal) g := by
    refine lipschitzWith_iff_dist_le_mul.mpr ?_
    intro x y
    rw [Subtype.dist_eq, Subtype.dist_eq]
    exact hlip x.1 x.2 y.1 y.2
  have hg : ContractingWith (⟨K, hK0⟩ : NNReal) g :=
    ⟨by exact_mod_cast hK1, hglip⟩
  refine ⟨(ContractingWith.fixedPoint g hg).1, ?_, ?_⟩
  · have hfix : g (ContractingWith.fixedPoint g hg) = ContractingWith.fixedPoint g hg :=
      ContractingWith.fixedPoint_isFixedPt hg
    have hval : (ContractingWith.fixedPoint g hg).1 - Y (F (ContractingWith.fixedPoint g hg).1)
        = (ContractingWith.fixedPoint g hg).1 := congrArg Subtype.val hfix
    have hzero : Y (F (ContractingWith.fixedPoint g hg).1) = 0 := sub_eq_self.mp hval
    exact ⟨(ContractingWith.fixedPoint g hg).2, hY (by simpa using hzero)⟩
  · intro y hy
    have hyfix : g ⟨y, hy.1⟩ = ⟨y, hy.1⟩ := by
      ext
      simp only [hgdef]
      rw [hy.2]
      simp
    exact congrArg Subtype.val (ContractingWith.fixedPoint_unique hg hyfix)

/-!
## G1 的剩余义务（精确化）

本定理把根的存在唯一完全归约到**三条区间不等式**，与 root-audit 的结论一致：

1. `hmap`：`K(B) ⊆ B`（"Krawczyk 包含"）——由 `‖I − Y·J‖ ≤ Q` 与 `‖Y·F(m)‖ ≤ η` 给出，
   两者都是**纯有理不等式**（`Q ≤ 0.0043719716348663187201 < 1`，`η` 与 `ρ` 的显式有理界）；
2. `hlip`：`g` 在 `B` 上的 Lipschitz 常数 `≤ Q`——由 `hmap` 的算子界 + 中值不等式给出
   （区间侧需要 `fderiv` 的盒包含性；`K` 取 `Q`）；
3. `hres`：`dist c (g c) ≤ (1−Q)·ρ`——由 `η` 的有理上界直接得到。

即：**Banach 步已无条件付清**；剩下的只是把 `Q`、`η` 与 `ρ` 的**精确有理界**算出来并接进
`evidence/interval/` 的区间内核（M1–M5）。
-/

end N11Formalization
