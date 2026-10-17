import N11Formalization.KrawczykDeriv
import N11Formalization.TCSystem

/-!
# 把 Krawczyk 解析链接到源系统 `TCSystem` 与证书盒

`KrawczykDeriv.lean` 给出通用链：**导数算子界 + 残差界 ⇒ 球内唯一根**。
本文件把它实例化到 `E = (Fin 12 → ℝ)`（mathlib 的 Pi 范数 = **sup 范数**，与源文的 ∞-范数口径一致）：

* `closedBall_eq_pi_Icc`：Krawczyk 的闭球 `B(c,ρ)` **就是证书里的积盒** `∏ᵢ [cᵢ−ρ, cᵢ+ρ]`；
* `exists_unique_TCSystem_of_krawczyk`：G1 的**命名化义务**（可微性 + 算子界 + 残差界 ⇒ `TCSystem` 的唯一根）；
* `exists_unique_TCSystem_of_cert_box`：把上面的球半径条件换成证书的 `boxLo/boxHi`。

⇒ 至此 G1 的**全部非数值环节**（中值不等式、Banach 收缩、包含性、唯一性、球↔盒等价）
都已 kernel 付清；剩余只有**数值**：`K`（= `Q`）与 `η` 的精确有理界，
以及 `TCSystem` 在盒上的**可微性**（含欧氏范数 `dist`；盒内各 `dist` 有正下界，由区间侧有理下界给出）。

**真实等级**：kernel-proved，无条件（除显式前提），零 sorry、零自定义 axiom。
-/

namespace N11Formalization

/-- **Krawczyk 的闭球就是证书的积盒**（`(Fin 12 → ℝ)` 的 Pi 范数 = sup 范数）。 -/
theorem closedBall_eq_pi_Icc (c : Fin 12 → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Metric.closedBall c ρ
      = Set.pi Set.univ (fun i : Fin 12 => Set.Icc (c i - ρ) (c i + ρ)) := by
  ext x
  rw [Metric.mem_closedBall, dist_eq_norm, Set.mem_univ_pi]
  constructor
  · intro h i
    have h1 : ‖(x - c) i‖ ≤ ‖x - c‖ := norm_le_pi_norm (x - c) i
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le] at h1
    rw [Set.mem_Icc]
    constructor <;> linarith [h1.1, h1.2, h]
  · intro h
    rw [pi_norm_le_iff_of_nonneg hρ]
    intro i
    have hi := h i
    rw [Set.mem_Icc] at hi
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hi.1, hi.2]

/-- 球成员条件的逐坐标形式。 -/
theorem mem_closedBall_iff_box {c : Fin 12 → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {x : Fin 12 → ℝ} :
    x ∈ Metric.closedBall c ρ ↔ ∀ i, c i - ρ ≤ x i ∧ x i ≤ c i + ρ := by
  rw [closedBall_eq_pi_Icc c hρ, Set.mem_univ_pi]
  exact forall_congr' fun i => Set.mem_Icc

/-- 证书盒（`boxLo/boxHi`，精确有理）与球坐标条件的等价。 -/
theorem mem_certBox_iff {boxLo boxHi : Fin 12 → ℚ} {c : Fin 12 → ℝ} {ρ : ℝ}
    (hLo : ∀ i, (boxLo i : ℝ) = c i - ρ) (hHi : ∀ i, (boxHi i : ℝ) = c i + ρ)
    {x : Fin 12 → ℝ} :
    (∀ i, (boxLo i : ℝ) ≤ x i ∧ x i ≤ (boxHi i : ℝ))
      ↔ ∀ i, c i - ρ ≤ x i ∧ x i ≤ c i + ρ := by
  constructor
  · intro h i
    have := h i
    constructor <;> linarith [hLo i, hHi i, this.1, this.2]
  · intro h i
    have := h i
    constructor <;> linarith [hLo i, hHi i, this.1, this.2]

/-- **G1 的命名化形式（源系统 `TCSystem`）**：可微性 + 算子界 + 残差界 ⇒ 球内唯一根。

这就是 C891 的 `exists_unique` 字段，剩下的只有数值（`K`、`η` 的有理界）与 `TCSystem` 在盒上的可微性。 -/
theorem exists_unique_TCSystem_of_krawczyk {c : Fin 12 → ℝ} {ρ K : ℝ}
    (Y : (Fin 12 → ℝ) →L[ℝ] (Fin 12 → ℝ)) (hY : Function.Injective Y)
    (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hdiff : ∀ x ∈ Metric.closedBall c ρ, DifferentiableAt ℝ TCSystem x)
    (hbound : ∀ x ∈ Metric.closedBall c ρ,
      ‖ContinuousLinearMap.id ℝ (Fin 12 → ℝ) - Y.comp (fderiv ℝ TCSystem x)‖ ≤ K)
    (hres : dist c (c - Y (TCSystem c)) + K * ρ < ρ) :
    ∃! x : (Fin 12 → ℝ), x ∈ Metric.closedBall c ρ ∧ TCSystem x = 0 :=
  krawczyk_banach_of_deriv_bound TCSystem Y hY c ρ K hρ hK0 hK1 hdiff hbound hres

/-- **证书盒版本**：同样的前提，结论换成证书 `boxLo/boxHi` 口径的唯一根。 -/
theorem exists_unique_TCSystem_of_cert_box {boxLo boxHi : Fin 12 → ℚ} {c : Fin 12 → ℝ} {ρ K : ℝ}
    (hLo : ∀ i, (boxLo i : ℝ) = c i - ρ) (hHi : ∀ i, (boxHi i : ℝ) = c i + ρ)
    (Y : (Fin 12 → ℝ) →L[ℝ] (Fin 12 → ℝ)) (hY : Function.Injective Y)
    (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hdiff : ∀ x ∈ Metric.closedBall c ρ, DifferentiableAt ℝ TCSystem x)
    (hbound : ∀ x ∈ Metric.closedBall c ρ,
      ‖ContinuousLinearMap.id ℝ (Fin 12 → ℝ) - Y.comp (fderiv ℝ TCSystem x)‖ ≤ K)
    (hres : dist c (c - Y (TCSystem c)) + K * ρ < ρ) :
    ∃! z : Fin 12 → ℝ, (∀ i, (boxLo i : ℝ) ≤ z i ∧ z i ≤ (boxHi i : ℝ)) ∧ TCSystem z = 0 := by
  have hρle : 0 ≤ ρ := hρ.le
  obtain ⟨z, hzball, hzuniq⟩ :=
    exists_unique_TCSystem_of_krawczyk Y hY hρ hK0 hK1 hdiff hbound hres
  refine ⟨z, ?_, ?_⟩
  · exact ⟨(mem_certBox_iff hLo hHi).mpr ((mem_closedBall_iff_box hρle).mp hzball.1), hzball.2⟩
  · intro w hw
    exact hzuniq w ⟨(mem_closedBall_iff_box hρle).mpr ((mem_certBox_iff hLo hHi).mp hw.1), hw.2⟩

end N11Formalization
