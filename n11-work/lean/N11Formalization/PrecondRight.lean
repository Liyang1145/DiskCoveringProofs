import N11Formalization.Precond

/-!
# 预条件子单射性的**正确**化归：另一侧的收缩不等式

**R10 发现（读源脚本得到）**：源证书的预条件子是
`Y = np.linalg.inv(np.array(Jmid, dtype=float))`（`repair_tc_krawczyk.py:44`），
即**binary64 近似逆**（每个 float 的确是精确 dyadic，但 `Y·J(m) = I` **不精确成立**）。
所以 `Precond.injective_ratMatCLM_of_leftInverse` 所需的有理左逆等式**在源数据上取不到**。

**正确路线**：单射性由**另一侧**的收缩不等式给出——
若 `‖I − A∘Y‖ < 1`（`A` 取盒内任一点的 Jacobian），则 `A∘Y` 可逆，故 `Y` 单射。
证明三行：`Au = 0 ⇒ u = (I−A)u ⇒ ‖u‖ ≤ ‖I−A‖·‖u‖ < ‖u‖ ⇒ u = 0`。

⇒ **`hY` 从"语义单射断言"变成"另一条有限有理行和不等式"**（`I − J·Y` 的逐元素包络），
与 `hsum` 同构，可由同一个区间矩阵机制产出。

**真实等级**：kernel-proved，无条件，零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

/-- `‖I − A‖ < 1 ⇒ A` 单射。 -/
theorem injective_of_norm_id_sub_lt_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (h : ‖ContinuousLinearMap.id ℝ E - A‖ < 1) : Function.Injective A := by
  have hker : ∀ v : E, A v = 0 → v = 0 := by
    intro v hv
    have h1 : (ContinuousLinearMap.id ℝ E - A) v = v := by
      rw [sub_apply, ContinuousLinearMap.id_apply, hv, sub_zero]
    have h2 : ‖v‖ ≤ ‖ContinuousLinearMap.id ℝ E - A‖ * ‖v‖ := by
      calc ‖v‖ = ‖(ContinuousLinearMap.id ℝ E - A) v‖ := by rw [h1]
        _ ≤ ‖ContinuousLinearMap.id ℝ E - A‖ * ‖v‖ := (ContinuousLinearMap.id ℝ E - A).le_opNorm v
    have h3 : ‖v‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hne)
      nlinarith [h2, h]
    exact norm_eq_zero.mp h3
  intro v w hvw
  have h0 : A (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hker (v - w) h0)

/-- `J∘Y` 单射 ⇒ `Y` 单射。 -/
theorem injective_of_comp_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J Y : E →L[ℝ] E) (h : Function.Injective (J.comp Y)) : Function.Injective Y :=
  fun _ _ hvw => h (by rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvw])

/-- **预条件子单射性由另一侧收缩给出**（取代"精确有理左逆"）。 -/
theorem injective_ratMatCLM_of_right_contraction {n : ℕ} (Y : Fin n → Fin n → ℚ)
    (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (h : ‖ContinuousLinearMap.id ℝ (Fin n → ℝ) - J.comp (ratMatCLM Y)‖ < 1) :
    Function.Injective (ratMatCLM Y) :=
  injective_of_comp_injective J (ratMatCLM Y) (injective_of_norm_id_sub_lt_one _ h)

/-! ## 右侧形状的矩阵包络：`I − A·Y`（乘法顺序与 `krawczykMat` 相反） -/

/-- `ratMatCLM Y` 在 `e_j` 处 = `Y` 的**第 j 列**。 -/
theorem ratMatCLM_single_col {n : ℕ} (Y : Fin n → Fin n → ℚ) (j : Fin n) :
    ratMatCLM Y (Pi.single j 1) = fun i => (Y i j : ℝ) := by
  funext i
  rw [ratMatCLM_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]; ring
  · intro k _ hk; rw [Pi.single_eq_of_ne hk, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- `(A·Y)(e_j)_i = Σ_k Y_kj · A(e_k)_i`。 -/
theorem comp_ratMatCLM_single {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (Y : Fin n → Fin n → ℚ) (j i : Fin n) :
    (A.comp (ratMatCLM Y)) (Pi.single j 1) i
      = ∑ k : Fin n, (Y k j : ℝ) * A (Pi.single k 1) i := by
  rw [ContinuousLinearMap.comp_apply, ratMatCLM_single_col]
  have hdecomp : (fun i : Fin n => (Y i j : ℝ))
      = ∑ k : Fin n, (Y k j : ℝ) • Pi.single k (1 : ℝ) := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [Pi.smul_apply, hk]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hdecomp, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- `I − A·Y` 的逐元素区间包络（`J` 逐元素包络 `A` 的矩阵表示，`Y` 有理）。 -/
def krawczykMatR {n : ℕ} (J : Fin n → Fin n → RatInterval) (Y : Fin n → Fin n → ℚ)
    (i j : Fin n) : RatInterval :=
  (RatInterval.ofRat (if i = j then (1 : ℚ) else 0)).sub
    (RatInterval.dot (fun k => Y k j) (fun k => J i k))

theorem mem_krawczykMatR {n : ℕ} {A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {J : Fin n → Fin n → RatInterval} {Y : Fin n → Fin n → ℚ}
    (hJ : ∀ k j : Fin n, (J k j).Mem (A (Pi.single j 1) k)) (i j : Fin n) :
    (krawczykMatR J Y i j).Mem
      ((ContinuousLinearMap.id ℝ (Fin n → ℝ) - A.comp (ratMatCLM Y)) (Pi.single j 1) i) := by
  have hdelta : (RatInterval.ofRat (if i = j then (1 : ℚ) else 0)).Mem
      (if i = j then (1 : ℝ) else 0) := by
    by_cases h : i = j
    · subst h; simpa using RatInterval.ofRat_mem (1 : ℚ)
    · have hL : RatInterval.ofRat (if i = j then (1 : ℚ) else 0) = RatInterval.ofRat 0 := by
        rw [if_neg h]
      rw [hL, if_neg h]
      simpa using RatInterval.ofRat_mem (0 : ℚ)
  have hdot : (RatInterval.dot (fun k => Y k j) (fun k => J i k)).Mem
      (∑ k : Fin n, (Y k j : ℝ) * A (Pi.single k 1) i) := by
    have hd := RatInterval.dot_mem (c := fun k => Y k j) (A := fun k => J i k)
      (x := fun k => A (Pi.single k 1) i) (fun k => hJ i k)
    rwa [dotR_eq_sum] at hd
  have hsub := RatInterval.sub_mem hdelta hdot
  have hgoal : (ContinuousLinearMap.id ℝ (Fin n → ℝ) - A.comp (ratMatCLM Y))
        (Pi.single j 1) i
      = (if i = j then (1 : ℝ) else 0) - ∑ k : Fin n, (Y k j : ℝ) * A (Pi.single k 1) i := by
    rw [sub_apply, ContinuousLinearMap.id_apply, Pi.sub_apply, comp_ratMatCLM_single]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij]
      have hs' : Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ) i = 0 :=
        @Pi.single_eq_of_ne (Fin n) (fun _ : Fin n => ℝ) _ _ j i hij (1 : ℝ)
      rw [hs']
  rw [hgoal]
  simpa only [krawczykMatR] using hsub

/-- **右侧收缩的区间化**：`I − A·Y` 的逐元素包络 + 行和 ≤ K' < 1 ⇒ `Y` 单射。 -/
theorem injective_ratMatCLM_of_right_enclosure {n : ℕ} (Y : Fin n → Fin n → ℚ)
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {K' : ℝ} (hK'0 : 0 ≤ K') (hK'1 : K' < 1)
    (Jt : Fin n → Fin n → RatInterval)
    (hJ : ∀ k j : Fin n, (Jt k j).Mem (A (Pi.single j 1) k))
    (hsum : ∀ i : Fin n, ∑ j : Fin n,
      max |((krawczykMatR Jt Y i j).lo : ℝ)| |((krawczykMatR Jt Y i j).hi : ℝ)| ≤ K') :
    Function.Injective (ratMatCLM Y) := by
  refine injective_ratMatCLM_of_right_contraction Y A ?_
  have hb : ‖ContinuousLinearMap.id ℝ (Fin n → ℝ) - A.comp (ratMatCLM Y)‖ ≤ K' :=
    opNorm_le_of_entry_bounds _ hK'0
      (fun i j => ((krawczykMatR Jt Y i j).lo : ℝ))
      (fun i j => ((krawczykMatR Jt Y i j).hi : ℝ))
      (fun i j => ⟨RatInterval.mem_lo_le (mem_krawczykMatR (Y := Y) (J := Jt) (A := A) hJ i j),
        RatInterval.mem_le_hi (mem_krawczykMatR (Y := Y) (J := Jt) (A := A) hJ i j)⟩) hsum
  linarith

end N11Formalization
