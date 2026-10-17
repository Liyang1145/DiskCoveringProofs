import N11Formalization.OpNorm
import N11Formalization.Interval.Vector
import N11Formalization.Transport
import N11Formalization.Assembly.G1Interval
import N11Formalization.Assembly.G1Final

/-!
# Jacobian 逐元素包络 + 有理预条件子 ⇒ G1 义务 (1) 的收口形式

G1 的义务 (1) 是**数值**的：给 `I − Y·(∂F/∂x)` 一个算子范数界。本文件把它落成**可算的形状**：

* `ratMatCLM`：有理矩阵视为 `(Fin n → ℝ) →L[ℝ] (Fin n → ℝ)`，并有 `ratMatCLM_apply`/`_single`；
* `dotR_eq_sum`：把 interval-core 的**列表折叠** `dotR` 与 `Finset.sum` 接通（用其 `dot_mem` 的必要桥梁）；
* `incrMat` / `krawczykMat`：`Y·A` 与 `I − Y·A` 的**逐元素区间包络**；
* `mem_krawczykMat`：若 `J` 逐元素包络 `A` 的矩阵表示，则 `krawczykMat Y J` 逐元素包络 `I − Y·A`；
* `opNorm_le_of_jacobian_enclosure`：逐元素包络 + 行和界 ⇒ `‖I − Y·A‖ ≤ K`；
* **`TCSystem_unique_root_of_jacobian_enclosure`**：接到 `Assembly/G1Final`，给出 G1 的
  **最终可算形式**（唯一剩下要外部产出的东西就是 `hJ`：Jacobian 的逐元素区间包络）。

**真实等级**：kernel-proved，无条件（除显式前提），零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

/-! ## 1. `dotR` ↔ `Finset.sum` -/

theorem foldl_dotFoldR_eq {n : ℕ} (l : List (Fin n)) (c : Fin n → ℚ) (x : Fin n → ℝ) (acc : ℝ) :
    l.foldl (RatInterval.dotFoldR c x) acc = acc + (l.map (fun i => (c i : ℝ) * x i)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    simp only [RatInterval.dotFoldR]
    ring

/-- `dotR` 就是 `Finset.sum`（`dot` 的实数语义）。 -/
theorem dotR_eq_sum {n : ℕ} (c : Fin n → ℚ) (x : Fin n → ℝ) :
    RatInterval.dotR c x = ∑ i : Fin n, (c i : ℝ) * x i := by
  rw [RatInterval.dotR_eq_dotLR, RatInterval.dotLR, foldl_dotFoldR_eq, zero_add,
    ← List.sum_toFinset (fun i : Fin n => (c i : ℝ) * x i) (List.nodup_finRange n),
    List.toFinset_finRange]

/-! ## 2. 有理矩阵作为 CLM -/

/-- 有理矩阵视为 `(Fin n → ℝ)` 上的连续线性映射。 -/
noncomputable def ratMatCLM {n : ℕ} (Y : Fin n → Fin n → ℚ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin n =>
    ∑ k : Fin n, ((Y i k : ℚ) : ℝ) •
      (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ))

theorem ratMatCLM_apply {n : ℕ} (Y : Fin n → Fin n → ℚ) (v : Fin n → ℝ) (i : Fin n) :
    ratMatCLM Y v i = ∑ k : Fin n, (Y i k : ℝ) * v k := by
  simp only [ratMatCLM, ContinuousLinearMap.pi_apply, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem ratMatCLM_single {n : ℕ} (Y : Fin n → Fin n → ℚ) (j : Fin n) (i : Fin n) :
    ratMatCLM Y (Pi.single j 1) i = (Y i j : ℝ) := by
  rw [ratMatCLM_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]; ring
  · intro k _ hk; rw [Pi.single_eq_of_ne hk, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-! ## 3. `I − Y·A` 的逐元素区间包络 -/

/-- `(Y·A)_{ij}` 的区间包络（`Y` 有理、`A` 的逐元素包络为 `J`）。 -/
def incrMat {n : ℕ} (Y : Fin n → Fin n → ℚ) (J : Fin n → Fin n → RatInterval)
    (i j : Fin n) : RatInterval :=
  RatInterval.dot (Y i) (fun k => J k j)

/-- `(I − Y·A)_{ij}` 的区间包络。 -/
def krawczykMat {n : ℕ} (Y : Fin n → Fin n → ℚ) (J : Fin n → Fin n → RatInterval)
    (i j : Fin n) : RatInterval :=
  (RatInterval.ofRat (if i = j then (1 : ℚ) else 0)).sub (incrMat Y J i j)

theorem mem_incrMat {n : ℕ} {Y : Fin n → Fin n → ℚ} {J : Fin n → Fin n → RatInterval}
    {A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hJ : ∀ k j : Fin n, (J k j).Mem (A (Pi.single j 1) k)) (i j : Fin n) :
    (incrMat Y J i j).Mem (ratMatCLM Y (A (Pi.single j 1)) i) := by
  have hd := RatInterval.dot_mem (c := Y i) (A := fun k => J k j)
    (x := fun k => A (Pi.single j 1) k) (fun k => hJ k j)
  rw [dotR_eq_sum] at hd
  simp only [incrMat]
  rw [ratMatCLM_apply]
  exact hd

theorem mem_krawczykMat {n : ℕ} {Y : Fin n → Fin n → ℚ} {J : Fin n → Fin n → RatInterval}
    {A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hJ : ∀ k j : Fin n, (J k j).Mem (A (Pi.single j 1) k)) (i j : Fin n) :
    (krawczykMat Y J i j).Mem
      ((ContinuousLinearMap.id ℝ (Fin n → ℝ) - (ratMatCLM Y).comp A) (Pi.single j 1) i) := by
  have hinc := mem_incrMat (Y := Y) (J := J) (A := A) hJ i j
  have hgoal : (ContinuousLinearMap.id ℝ (Fin n → ℝ) - (ratMatCLM Y).comp A)
        (Pi.single j 1) i
      = (if i = j then (1 : ℝ) else 0) - ratMatCLM Y (A (Pi.single j 1)) i := by
    rw [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, Pi.sub_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij]
      have hs' : Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ) i = 0 :=
        @Pi.single_eq_of_ne (Fin n) (fun _ : Fin n => ℝ) _ _ j i hij (1 : ℝ)
      rw [hs']
  rw [hgoal]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hk : krawczykMat Y J i i = (RatInterval.ofRat 1).sub (incrMat Y J i i) := by
      simp [krawczykMat]
    rw [hk]
    simpa using RatInterval.sub_mem (RatInterval.ofRat_mem (1 : ℚ)) hinc
  · rw [if_neg hij]
    have hk : krawczykMat Y J i j = (RatInterval.ofRat 0).sub (incrMat Y J i j) := by
      simp [krawczykMat, if_neg hij]
    rw [hk]
    simpa using RatInterval.sub_mem (RatInterval.ofRat_mem (0 : ℚ)) hinc

/-- **Jacobian 逐元素包络 + 行和界 ⇒ `‖I − Y·A‖ ≤ K`**（义务 (1) 的算子范数一步）。 -/
theorem opNorm_le_of_jacobian_enclosure {n : ℕ} (Y : Fin n → Fin n → ℚ)
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {K : ℝ} (hK0 : 0 ≤ K)
    (J : Fin n → Fin n → RatInterval)
    (hJ : ∀ k j : Fin n, (J k j).Mem (A (Pi.single j 1) k))
    (hsum : ∀ i : Fin n, ∑ j : Fin n,
      max |((krawczykMat Y J i j).lo : ℝ)| |((krawczykMat Y J i j).hi : ℝ)| ≤ K) :
    ‖ContinuousLinearMap.id ℝ (Fin n → ℝ) - (ratMatCLM Y).comp A‖ ≤ K :=
  opNorm_le_of_entry_bounds _ hK0 _ _
    (fun i j => ⟨RatInterval.mem_lo_le (mem_krawczykMat (Y := Y) (J := J) (A := A) hJ i j),
      RatInterval.mem_le_hi (mem_krawczykMat (Y := Y) (J := J) (A := A) hJ i j)⟩) hsum

/-- **G1 义务 (1) 的最终可算形式**：Jacobian 的**逐元素区间包络** `hJ` + 有理预条件子 `Y`
+ 行和界 `K < 1` + 残差界 ⇒ 源系统的唯一根。

这是本项目对 G1 的**最紧陈述**：唯一需要外部产出的是 `hJ`（Jacobian 的逐元素包络）与
`hsum`（有理行和不等式），两者都是有限的有理数据。 -/
theorem TCSystem_unique_root_of_jacobian_enclosure {c : Fin 12 → ℝ} {ρ K : ℝ}
    (Y : Fin 12 → Fin 12 → ℚ) (hY : Function.Injective (ratMatCLM Y))
    (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hndRho : ∀ x ∈ closedBall c ρ, ∀ j : Fin 9,
      (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hndW : ∀ x ∈ closedBall c ρ, (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hndU1 : ∀ x ∈ closedBall c ρ, Uvec x 1 ≠ hub1 x)
    (hndU2 : ∀ x ∈ closedBall c ρ, Uvec x 2 ≠ hub0 x)
    (hndU3 : ∀ x ∈ closedBall c ρ, Uvec x 3 ≠ hub0 x)
    (hndU8 : ∀ x ∈ closedBall c ρ, Uvec x 8 ≠ hub1 x)
    (hndWp : ∀ x ∈ closedBall c ρ, wPoint x ≠ ringCenter x 6)
    (Jt : Fin 12 → Fin 12 → RatInterval)
    (hJ : ∀ x ∈ closedBall c ρ, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K)
    (hres : dist c (c - ratMatCLM Y (TCSystem c)) + K * ρ < ρ) :
    ∃! x : Fin 12 → ℝ, x ∈ closedBall c ρ ∧ TCSystem x = 0 :=
  TCSystem_unique_root_of_final_data (ratMatCLM Y) hY hρ hK0 hK1
    hndRho hndW hndU1 hndU2 hndU3 hndU8 hndWp (krawczykMat Y Jt)
    (fun x hx i j => mem_krawczykMat (Y := Y) (J := Jt) (A := fderiv ℝ TCSystem x)
      (hJ x hx) i j)
    hsum hres

end N11Formalization
