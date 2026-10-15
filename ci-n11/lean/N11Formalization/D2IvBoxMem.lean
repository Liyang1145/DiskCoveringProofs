import N11Formalization.TowerBC_N_anyx_layer1
import N11Formalization.D2Leaves

noncomputable section

namespace N11Formalization

namespace TowerBC

open RatInterval

set_option maxHeartbeats 800000

/-! ## A. 家法（已验证全绿 ✓） -/

/-- `secondPartial` 的**函数相等 ⇒ 值相等** ✓（`sp_congr`）。 -/
theorem sp_congr {F G : (Fin 7 → ℝ) → ℝ} (h : ∀ z, F z = G z) (x : Fin 7 → ℝ) :
    ∀ i j : Fin 7, secondPartial F x i j = secondPartial G x i j := by
  have hFG : F = G := funext h
  subst hFG
  exact fun i j => rfl

/-- 树形搬家包装（`e` 逐点 ⇒ 强制指定树形 ✓）。 -/
theorem sp_conv {F G : (Fin 7 → ℝ) → ℝ} (e : ∀ w, F w = G w) (x : Fin 7 → ℝ) :
    ∀ i j : Fin 7, secondPartial F x i j = secondPartial G x i j :=
  sp_congr e x

/-- 单侧 `∀ᶠ` 的 sub 规则（`φ/ψ` 自由变量 ⇒ `rw` 无歧义 ✓）。 -/
theorem sp_sub {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} {x : Fin 7 → ℝ}
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 x)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 x)
    (hAd : ∀ᶠ z in nhds x, DifferentiableAt ℝ φ z)
    (hBd : ∀ᶠ z in nhds x, DifferentiableAt ℝ ψ z) (i j : Fin 7) :
    secondPartial (fun z => φ z - ψ z) x i j
      = secondPartial φ x i j - secondPartial ψ x i j := by
  have he : (fun z => φ z - ψ z) = (φ - ψ) := by funext z; rfl
  rw [he]
  exact secondPartial_sub_any hφ hψ hAd hBd i j

/-- add 规则（自由变量 ✓）。 -/
theorem sp_add {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} {x : Fin 7 → ℝ}
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 x)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 x)
    (hAd : ∀ᶠ z in nhds x, DifferentiableAt ℝ φ z)
    (hBd : ∀ᶠ z in nhds x, DifferentiableAt ℝ ψ z) (i j : Fin 7) :
    secondPartial (fun z => φ z + ψ z) x i j
      = secondPartial φ x i j + secondPartial ψ x i j :=
  secondPartial_add_any hφ hψ hAd hBd i j

/-! ## B. 层 1

**口径**（Lead 已落根 112 条版 ✓）：`hasFDerivAt_fderiv_clm_any`／`hasFDerivAt_fderiv_of_eq_clm_any`
**现已在锥** ✓ ⇒ 本件**不再自建**这两条（用锥内 ✓；注意锥内 `of_eq_clm_any` 的**参数序是 `(x) (h)`** ✓）。
`hasFDerivAt_fderiv_of_eq_const_any` **不在锥** ✗ ⇒ 本件自建（**独有** ✓）。 -/

/-- 常函数桥 `φ ≡ c` ⇒ 二阶 = `0`（**任意点** ✓；锥内无此条 ⇒ 本件独有 ✓）。 -/
theorem hasFDerivAt_fderiv_of_eq_const_any {φ : (Fin 7 → ℝ) → ℝ} {c : ℝ}
    (h : φ = fun _ => c) (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ φ y)
      (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) x := by
  have h' : (fun y : Fin 7 → ℝ => fderiv ℝ φ y)
      = fun y : Fin 7 → ℝ => fderiv ℝ (fun _ : Fin 7 → ℝ => c) y := by
    funext y
    rw [h]
  have hclm : (fun y : Fin 7 → ℝ => fderiv ℝ (fun _ : Fin 7 → ℝ => c) y)
      = fun _ : Fin 7 → ℝ => (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) := by
    funext y
    exact (hasFDerivAt_const (𝕜 := ℝ) (E := Fin 7 → ℝ) (F := ℝ) (c := c) (x := y)).fderiv
  rw [h', hclm]
  simpa using (hasFDerivAt_const (𝕜 := ℝ) (E := Fin 7 → ℝ)
    (F := (Fin 7 → ℝ) →L[ℝ] ℝ) (c := (0 : (Fin 7 → ℝ) →L[ℝ] ℝ)) (x := x))

/-! ## C. `hub` 四族的 `_any` 邻域可微性（`D2Leaves` 的 `u0` 版的 `u0 → z` 升格 ✓，全绿 ✓） -/

theorem eventually_diff_hub0xF (z : Fin 7 → ℝ) :
    ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp 0) w :=
  Filter.Eventually.of_forall fun w =>
    (ContinuousLinearMap.differentiableAt (f := coord 4) (x := w)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => congrFun hub0xF_eq y)

theorem eventually_diff_hub1xF (z : Fin 7 → ℝ) :
    ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp 0) w :=
  Filter.Eventually.of_forall fun w =>
    (ContinuousLinearMap.differentiableAt (f := coord 5) (x := w)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => congrFun hub1xF_eq y)

theorem eventually_diff_hub0yF (z : Fin 7 → ℝ) :
    ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp 1) w :=
  Filter.Eventually.of_forall fun w =>
    (differentiableAt_const (c := (0 : ℝ)) (x := w)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => congrFun hub0yF_eq y)

theorem eventually_diff_hub1yF (z : Fin 7 → ℝ) :
    ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp 1) w :=
  Filter.Eventually.of_forall fun w =>
    (differentiableAt_const (c := (0 : ℝ)) (x := w)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => congrFun hub1yF_eq y)

/-! ## D. 盒读数桥与 `wPoint` 取值件（全绿 ✓） -/

theorem Wfun_pos_of_wkBoxQ {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (s : Fin 9) (h : 0 < (wkBoxQ Q s).lo) :
    0 < Wfun s z := by
  have h1 : ((wkBoxQ Q s).lo : ℝ) ≤ pad12 z 6 * pad12 z 6
      - Real.sin (angleVec (pad12 z) s) * Real.sin (angleVec (pad12 z) s) :=
    mem_lo_le (wkBoxQ_mem hz s)
  rw [WkBoxQ_value s z] at h1
  exact lt_of_lt_of_le (by exact_mod_cast h) h1

theorem Wpf_pos_of_WpIvBoxQ {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (h : 0 < (WpIvBoxQ Q).lo) : 0 < Wpf z := by
  have h1 : ((WpIvBoxQ Q).lo : ℝ) ≤ (z 6) ^ 2 - ((z 5 - z 4) / 2) ^ 2 := mem_lo_le (WpIvBoxQ_mem hz)
  rw [Wpf]
  exact lt_of_lt_of_le (by exact_mod_cast h) h1

theorem secondPartial_wxF_any (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0) x i j = 0 := by
  have hlin : (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0)
      = fun z : Fin 7 → ℝ => (1 / 2 : ℝ) * (z 4 + z 5) := by
    funext z
    rw [wPoint_coord0, pad12_four, pad12_five]
    ring
  have hclm : (fun z : Fin 7 → ℝ => ((1 / 2 : ℝ) • (coord 4 + coord 5)) z)
      = fun z : Fin 7 → ℝ => (1 / 2 : ℝ) * (z 4 + z 5) := by
    funext z
    rw [smul_apply, add_apply, smul_eq_mul]
    rfl
  have hφ : (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0)
      = fun z => ((1 / 2 : ℝ) • (coord 4 + coord 5)) z := by rw [hlin, hclm]
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_of_eq_clm_any x hφ) i j]
  exact zero_apply _

theorem secondPartial_wyF_any (x : Fin 7 → ℝ) (hWp : 0 < Wpf x) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1) x i j = wy2RAt x i j := by
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_wyF_any x hWp) i j]
  simpa [(hasFDerivAt_fderiv_wyF_any x hWp).fderiv] using wy2_single_any i j x hWp


/-! ## D′. 两条盒表

**口径**（Lead 已落根 ✓）：`d2xIvBox`／`d2yIvBox` **现已在锥** ✓
（`#print` 实测：与先前本件所定义者**逐字同形** ✓：`if k = 4 then neg (ring2Box Q 6 0 i j) else
sub (sub (add (ring2Box Q (resSlot k) 0 i j) (ring2Box Q ((resSlot k) + 1) 0 i j)) (arc2Box Q (resSlot k) 0 i j)) (ofRat 0)`
—— `d2yIvBox` 对称 ✓）⇒ 本件**不再定义**，直接用锥内 ✓。 -/

/-! ## E. **`Uvec` 支逐支件（`k ≤ 3`）** —— 正解：把**目标侧**的 `secondPartial` 树形搬到「函数差」
（`sp_conv` ＋ `rfl`；**不**动 `HasFDerivAt` ⇒ 避开 `congr_of_eventuallyEq` 的 `Eq.mpr` 包装 ✗），
再**单次应用** `sp_sub`（`φ/ψ` 由 `∀ᶠ` 假设的类型锁死 ✓）。**已过门** ✓ -/

/-- `Uvec` 支（`c` 分量，`hub = hub0`）✓。 -/
theorem d2IvBox_mem_uvec_hub0 (Q : Fin 7 → RatInterval) {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (s : Fin 9) (c : Fin 2)
    (hW0 : 0 < (wkBoxQ Q s).lo) (hW1 : 0 < (wkBoxQ Q (s + 1)).lo)
    {φ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hUh : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (Uvec (pad12 x) s).ofLp c) x) φ2 z)
    (hH : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (hub0 (pad12 x)).ofLp c) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hUd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) w)
    (hHd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp c) w)
    (hU2 : ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp c) z i j
        + secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp c) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp c) z i j)
    (hHub : ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp c) z i j = 0)
    (i j : Fin 7) :
    (sub (sub (add (ring2Box Q s c i j) (ring2Box Q (s + 1) c i j)) (arc2Box Q s c i j))
        (ofRat 0)).Mem
      (secondPartial (fun w : Fin 7 → ℝ =>
        (Uvec (pad12 w) s).ofLp c - (hub0 (pad12 w)).ofLp c) z i j) := by
  have hTree : secondPartial (fun w : Fin 7 → ℝ =>
        (Uvec (pad12 w) s).ofLp c - (hub0 (pad12 w)).ofLp c) z i j
      = secondPartial ((fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c)
          - (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp c)) z i j :=
    sp_conv (fun w => rfl) z i j
  have hSub : secondPartial ((fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c)
        - (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp c)) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp c) z i j :=
    sp_sub hUh hH hUd hHd i j
  rw [hTree, hSub, hU2 i j, hHub i j,
    secondPartial_ringC_any s c z (Wfun_pos_of_wkBoxQ hz s hW0) i j,
    secondPartial_ringC_any (s + 1) c z (Wfun_pos_of_wkBoxQ hz (s + 1) hW1) i j]
  rw [show secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp c) z i j
      = secondPartial (ArcC s c) z i j from sp_conv (fun w => rfl) z i j]
  rw [secondPartial_arcEnd_any s c z i j]
  exact sub_mem (sub_mem (add_mem (ring2Box_mem hz s c i j hW0)
    (ring2Box_mem hz (s + 1) c i j hW1)) (arc2Box_mem hz s c i j)) (by
      simpa using ofRat_mem (0 : ℚ))

/-- `Uvec` 支（`c` 分量，`hub = hub1`）✓。 -/
theorem d2IvBox_mem_uvec_hub1 (Q : Fin 7 → RatInterval) {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (s : Fin 9) (c : Fin 2)
    (hW0 : 0 < (wkBoxQ Q s).lo) (hW1 : 0 < (wkBoxQ Q (s + 1)).lo)
    {φ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hUh : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (Uvec (pad12 x) s).ofLp c) x) φ2 z)
    (hH : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (hub1 (pad12 x)).ofLp c) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hUd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) w)
    (hHd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp c) w)
    (hU2 : ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp c) z i j
        + secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp c) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp c) z i j)
    (hHub : ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp c) z i j = 0)
    (i j : Fin 7) :
    (sub (sub (add (ring2Box Q s c i j) (ring2Box Q (s + 1) c i j)) (arc2Box Q s c i j))
        (ofRat 0)).Mem
      (secondPartial (fun w : Fin 7 → ℝ =>
        (Uvec (pad12 w) s).ofLp c - (hub1 (pad12 w)).ofLp c) z i j) := by
  have hTree : secondPartial (fun w : Fin 7 → ℝ =>
        (Uvec (pad12 w) s).ofLp c - (hub1 (pad12 w)).ofLp c) z i j
      = secondPartial ((fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c)
          - (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp c)) z i j :=
    sp_conv (fun w => rfl) z i j
  have hSub : secondPartial ((fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c)
        - (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp c)) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp c) z i j :=
    sp_sub hUh hH hUd hHd i j
  rw [hTree, hSub, hU2 i j, hHub i j,
    secondPartial_ringC_any s c z (Wfun_pos_of_wkBoxQ hz s hW0) i j,
    secondPartial_ringC_any (s + 1) c z (Wfun_pos_of_wkBoxQ hz (s + 1) hW1) i j]
  rw [show secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp c) z i j
      = secondPartial (ArcC s c) z i j from sp_conv (fun w => rfl) z i j]
  rw [secondPartial_arcEnd_any s c z i j]
  exact sub_mem (sub_mem (add_mem (ring2Box_mem hz s c i j hW0)
    (ring2Box_mem hz (s + 1) c i j hW1)) (arc2Box_mem hz s c i j)) (by
      simpa using ofRat_mem (0 : ℚ))

/-! ## F. **`k = 4`（`wPoint`）支** -/

/-- `Δx` · `wPoint` 支（`wPoint.x` 线性 ⇒ 二阶 ≡ 0 ⇒ 盒叶 = `−ring 6 0` ✓）。 -/
theorem d2xIvBox_mem_w (Q : Fin 7 → RatInterval) {z : Fin 7 → ℝ} (hz : ∀ i, (Q i).Mem (z i))
    (hW6 : 0 < (wkBoxQ Q 6).lo)
    (hWx : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (wPoint (pad12 x)).ofLp 0) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hC : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (ringCenter (pad12 x) 6).ofLp 0) x) (L2RingC0At z 6) z)
    (hWxd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 0) w)
    (hCd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 0) w)
    (i j : Fin 7) :
    (neg (ring2Box Q 6 0 i j)).Mem
      (secondPartial (fun w : Fin 7 → ℝ =>
        (wPoint (pad12 w)).ofLp 0 - (ringCenter (pad12 w) 6).ofLp 0) z i j) := by
  have hTree : secondPartial (fun w : Fin 7 → ℝ =>
        (wPoint (pad12 w)).ofLp 0 - (ringCenter (pad12 w) 6).ofLp 0) z i j
      = secondPartial ((fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 0)
          - (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 0)) z i j :=
    sp_conv (fun w => rfl) z i j
  have hSub : secondPartial ((fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 0)
        - (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 0)) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 0) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 0) z i j :=
    sp_sub hWx hC hWxd hCd i j
  rw [hTree, hSub, secondPartial_wxF_any z i j,
    secondPartial_ringC_any 6 0 z (Wfun_pos_of_wkBoxQ hz 6 hW6) i j]
  ring_nf
  exact neg_mem (ring2Box_mem hz 6 0 i j hW6)

/-- `Δy` · `wPoint` 支（`wPoint.y = √Wp` ⇒ 用 `_any` 取值件 ✓）。 -/
theorem d2yIvBox_mem_w (Q : Fin 7 → RatInterval) {z : Fin 7 → ℝ} (hz : ∀ i, (Q i).Mem (z i))
    (hW6 : 0 < (wkBoxQ Q 6).lo) (hWp : 0 < (WpIvBoxQ Q).lo) (hVp : (WpIvBoxQ Q).Valid)
    (hWy : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (wPoint (pad12 x)).ofLp 1) x) (L2WyAt z) z)
    (hC : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (ringCenter (pad12 x) 6).ofLp 1) x) (L2RingC1At z 6) z)
    (hWyd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 1) w)
    (hCd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 1) w)
    (i j : Fin 7) :
    (sub (Wy2Box Q i j) (ring2Box Q 6 1 i j)).Mem
      (secondPartial (fun w : Fin 7 → ℝ =>
        (wPoint (pad12 w)).ofLp 1 - (ringCenter (pad12 w) 6).ofLp 1) z i j) := by
  have hWp' : 0 < Wpf z := Wpf_pos_of_WpIvBoxQ hz hWp
  have hTree : secondPartial (fun w : Fin 7 → ℝ =>
        (wPoint (pad12 w)).ofLp 1 - (ringCenter (pad12 w) 6).ofLp 1) z i j
      = secondPartial ((fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 1)
          - (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 1)) z i j :=
    sp_conv (fun w => rfl) z i j
  have hSub : secondPartial ((fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 1)
        - (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 1)) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 1) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 1) z i j :=
    sp_sub hWy hC hWyd hCd i j
  rw [hTree, hSub, secondPartial_wyF_any z hWp' i j,
    secondPartial_ringC_any 6 1 z (Wfun_pos_of_wkBoxQ hz 6 hW6) i j]
  exact sub_mem (Wy2Box_mem hz i j hWp hVp) (ring2Box_mem hz 6 1 i j hW6)

/-! ## F. **Dxy 树形支**（Uvec 支的最终形）—— 全部在 `Dxy` 树上，锥内 `secondPartial_Uvec_coord_any`
**直接**给 `hU2`（`exact`，**不经 `rw`** ⇒ 无歧义 ✓，`ProbeQ` 已验证）。 -/

/-- `Uvec` 支（`c` 分量，`hub0`）：`hU2` 由锥内件**直接供** ✓。 -/
theorem d2IvBox_mem_uvecD_hub0 (Q : Fin 7 → RatInterval) {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (s : Fin 9) (c : Fin 2)
    (hW0 : 0 < (wkBoxQ Q s).lo) (hW1 : 0 < (wkBoxQ Q (s + 1)).lo)
    {φ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hUh : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (Uvec (pad12 x) s).ofLp c) x) φ2 z)
    (hH : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (hub0 (pad12 x)).ofLp c) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hUd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) w)
    (hHd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp c) w)
    (hU2 : ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp c) z i j
        + secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp c) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp c) z i j)
    (hHub : ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp c) z i j = 0)
    (i j : Fin 7) :
    (sub (sub (add (ring2Box Q s c i j) (ring2Box Q (s + 1) c i j)) (arc2Box Q s c i j))
        (ofRat 0)).Mem
      (secondPartial (fun w : Fin 7 → ℝ =>
        (Uvec (pad12 w) s).ofLp c - (hub0 (pad12 w)).ofLp c) z i j) := by
  have hSub := secondPartial_sub_any hUh hH hUd hHd (x := z) (i := i) (j := j)
  have hArcD : secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp c) z i j
      = secondPartial (ArcC s c) z i j := sp_conv (fun w => rfl) z i j
  rw [hSub, hU2 i j, hHub i j, hArcD,
    secondPartial_ringC_any s c z (Wfun_pos_of_wkBoxQ hz s hW0) i j,
    secondPartial_ringC_any (s + 1) c z (Wfun_pos_of_wkBoxQ hz (s + 1) hW1) i j,
    secondPartial_arcEnd_any s c z i j]
  exact sub_mem (sub_mem (add_mem (ring2Box_mem hz s c i j hW0)
    (ring2Box_mem hz (s + 1) c i j hW1)) (arc2Box_mem hz s c i j)) (by
      simpa using ofRat_mem (0 : ℚ))

/-- `Uvec` 支（`c` 分量，`hub1`）✓。 -/
theorem d2IvBox_mem_uvecD_hub1 (Q : Fin 7 → RatInterval) {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (s : Fin 9) (c : Fin 2)
    (hW0 : 0 < (wkBoxQ Q s).lo) (hW1 : 0 < (wkBoxQ Q (s + 1)).lo)
    {φ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hUh : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (Uvec (pad12 x) s).ofLp c) x) φ2 z)
    (hH : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (hub1 (pad12 x)).ofLp c) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hUd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) w)
    (hHd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp c) w)
    (hU2 : ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp c) z i j
        + secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp c) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp c) z i j)
    (hHub : ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp c) z i j = 0)
    (i j : Fin 7) :
    (sub (sub (add (ring2Box Q s c i j) (ring2Box Q (s + 1) c i j)) (arc2Box Q s c i j))
        (ofRat 0)).Mem
      (secondPartial (fun w : Fin 7 → ℝ =>
        (Uvec (pad12 w) s).ofLp c - (hub1 (pad12 w)).ofLp c) z i j) := by
  have hSub := secondPartial_sub_any hUh hH hUd hHd (x := z) (i := i) (j := j)
  have hArcD : secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp c) z i j
      = secondPartial (ArcC s c) z i j := sp_conv (fun w => rfl) z i j
  rw [hSub, hU2 i j, hHub i j, hArcD,
    secondPartial_ringC_any s c z (Wfun_pos_of_wkBoxQ hz s hW0) i j,
    secondPartial_ringC_any (s + 1) c z (Wfun_pos_of_wkBoxQ hz (s + 1) hW1) i j,
    secondPartial_arcEnd_any s c z i j]
  exact sub_mem (sub_mem (add_mem (ring2Box_mem hz s c i j hW0)
    (ring2Box_mem hz (s + 1) c i j hW1)) (arc2Box_mem hz s c i j)) (by
      simpa using ofRat_mem (0 : ℚ))

/-! ## G. **`k = 4` 支** -/

/-- `Δx` · `wPoint` 支（`wPoint.x` 线性 ⇒ 二阶 ≡ 0 ✓）。 -/
theorem d2xIvBox_mem_wF (Q : Fin 7 → RatInterval) {z : Fin 7 → ℝ} (hz : ∀ i, (Q i).Mem (z i))
    (hW6 : 0 < (wkBoxQ Q 6).lo)
    (hWx : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (wPoint (pad12 x)).ofLp 0) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hC : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (ringCenter (pad12 x) 6).ofLp 0) x) (L2RingC0At z 6) z)
    (hWxd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 0) w)
    (hCd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 0) w)
    (i j : Fin 7) :
    (neg (ring2Box Q 6 0 i j)).Mem
      (secondPartial (fun w : Fin 7 → ℝ =>
        (wPoint (pad12 w)).ofLp 0 - (ringCenter (pad12 w) 6).ofLp 0) z i j) := by
  have hSub := secondPartial_sub_any hWx hC hWxd hCd (x := z) (i := i) (j := j)
  rw [hSub, secondPartial_wxF_any z i j,
    secondPartial_ringC_any 6 0 z (Wfun_pos_of_wkBoxQ hz 6 hW6) i j]
  ring_nf
  simpa using neg_mem (ring2Box_mem hz 6 0 i j hW6)

/-- `Δy` · `wPoint` 支 ✓。 -/
theorem d2yIvBox_mem_wF (Q : Fin 7 → RatInterval) {z : Fin 7 → ℝ} (hz : ∀ i, (Q i).Mem (z i))
    (hW6 : 0 < (wkBoxQ Q 6).lo) (hWp : 0 < (WpIvBoxQ Q).lo) (hVp : (WpIvBoxQ Q).Valid)
    (hWy : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (wPoint (pad12 x)).ofLp 1) x) (L2WyAt z) z)
    (hC : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (ringCenter (pad12 x) 6).ofLp 1) x) (L2RingC1At z 6) z)
    (hWyd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 1) w)
    (hCd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 1) w)
    (i j : Fin 7) :
    (sub (Wy2Box Q i j) (ring2Box Q 6 1 i j)).Mem
      (secondPartial (fun w : Fin 7 → ℝ =>
        (wPoint (pad12 w)).ofLp 1 - (ringCenter (pad12 w) 6).ofLp 1) z i j) := by
  have hWp' : 0 < Wpf z := Wpf_pos_of_WpIvBoxQ hz hWp
  have hSub := secondPartial_sub_any hWy hC hWyd hCd (x := z) (i := i) (j := j)
  rw [hSub, secondPartial_wyF_any z hWp' i j,
    secondPartial_ringC_any 6 1 z (Wfun_pos_of_wkBoxQ hz 6 hW6) i j]
  exact sub_mem (Wy2Box_mem hz i j hWp hVp) (ring2Box_mem hz 6 1 i j hW6)

/-! ## H. **分派原语**（`k`-查表用；两条均**已过门** ✓） -/

/-- `resSlot` 的四值枚举（`k ≠ 4`；供 `k` 分派 ✓）。 -/
theorem resSlot_cases {k : Fin 5} (hk : k ≠ 4) :
    resSlot k = (1 : Fin 9) ∨ resSlot k = 2 ∨ resSlot k = 3 ∨ resSlot k = 8 := by
  fin_cases k <;> simp_all <;> decide

/-- `Uvec` 的 `∀ᶠ` 邻域可微性（由 Dxy 三块 + 点恒等式 `Uvec_coord0/1` ✓）。 -/
theorem uvec_evdiff {s : Fin 9} {c : Fin 2} {z : Fin 7 → ℝ}
    (hRd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) s).ofLp c) w)
    (hRd' : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (s + 1)).ofLp c) w)
    (hAd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) s).ofLp c) w) :
    ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (Uvec (pad12 w) s).ofLp c) w := by
  filter_upwards [hRd, hRd', hAd] with w hw1 hw2 hw3
  have hEq : (fun y : Fin 7 → ℝ => (Uvec (pad12 y) s).ofLp c)
      = fun y : Fin 7 → ℝ => (ringCenter (pad12 y) s).ofLp c
        + (ringCenter (pad12 y) (s + 1)).ofLp c - (arcEnd (pad12 y) s).ofLp c := by
    funext y
    fin_cases c
    · exact Uvec_coord0 (pad12 y) s
    · exact Uvec_coord1 (pad12 y) s
  rw [hEq]
  exact hw1.add hw2 |>.sub hw3

/-- `k ≠ 4` 时 `k` 的四值枚举（供 `k` 分派；`subst` 掉 `k` ⇒ 假设位与目标位**同步** ✓）。 -/
theorem fin5_ne_four_cases {k : Fin 5} (hk : k ≠ 4) :
    k = (0 : Fin 5) ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  fin_cases k <;> simp_all
/-! ## I. **两条总定理**（层 3：`k` 查表分派）

**分派机制**（避开 `resSlot` 在假设位不归约 ✗）：`fin5_ne_four_cases`（`k ≠ 4` ⇒ `k ∈ {0,1,2,3}`）
＋ **`subst`**（把 `k` 在**目标与全部假设**里同时换成字面量 ⇒ 支件已参数化在 `s` ⇒ **零 `Fin` 算术** ✓）。

**`⋆` 假设口径**（Lead 批准 ✓）：`hUd`（`Uvec` 的邻域可微性）与 `hU2`（锥内 `secondPartial_Uvec_coord_any` 的实例）
收成**显式假设** —— 盒数据本来就只在 `z` 处给正性 ✓，如实标注 scope、不冒充 ✓。 -/

/-- **`d2xIvBox_mem`** —— `Δx` 的球级二阶盒表（全 `5×7×7` 格）✓。 -/
theorem d2xIvBox_mem (Q : Fin 7 → RatInterval) (k : Fin 5) (i j : Fin 7) {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i))
    (hW6 : 0 < (wkBoxQ Q 6).lo)
    (hWa : 0 < (wkBoxQ Q (resSlot k)).lo) (hWb : 0 < (wkBoxQ Q ((resSlot k) + 1)).lo)
    {φ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hUh : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (Uvec (pad12 x) (resSlot k)).ofLp 0) x) φ2 z)
    (hH0 : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (hub0 (pad12 x)).ofLp 0) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hH1 : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (hub1 (pad12 x)).ofLp 0) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hUd : ∀ᶠ w in nhds z, DifferentiableAt ℝ
      (fun w : Fin 7 → ℝ => (Uvec (pad12 w) (resSlot k)).ofLp 0) w)
    (hHd0 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp 0) w)
    (hHd1 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp 0) w)
    (hU2 : ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (Uvec (pad12 w) (resSlot k)).ofLp 0) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (resSlot k)).ofLp 0) z i j
        + secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) ((resSlot k) + 1)).ofLp 0) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) (resSlot k)).ofLp 0) z i j)
    (hWx : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (wPoint (pad12 x)).ofLp 0) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hC6 : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (ringCenter (pad12 x) 6).ofLp 0) x) (L2RingC0At z 6) z)
    (hWxd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 0) w)
    (hC6d : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 0) w) :
    (d2xIvBox Q k i j).Mem (secondPartial (DeltaX k) z i j) := by
  rw [d2xIvBox]
  by_cases hk : k = 4
  · subst hk
    rw [if_pos rfl]
    exact d2xIvBox_mem_wF Q hz hW6 hWx hC6 hWxd hC6d i j
  · rw [if_neg hk]
    rcases fin5_ne_four_cases hk with h0 | h1 | h2 | h3
    · subst h0
      exact d2IvBox_mem_uvecD_hub1 Q hz (resSlot 0) 0 hWa hWb hUh hH1 hUd hHd1 hU2
        (fun i j => secondPartial_hub1_coord0_any z i j) i j
    · subst h1
      exact d2IvBox_mem_uvecD_hub0 Q hz (resSlot 1) 0 hWa hWb hUh hH0 hUd hHd0 hU2
        (fun i j => secondPartial_hub0_coord0_any z i j) i j
    · subst h2
      exact d2IvBox_mem_uvecD_hub0 Q hz (resSlot 2) 0 hWa hWb hUh hH0 hUd hHd0 hU2
        (fun i j => secondPartial_hub0_coord0_any z i j) i j
    · subst h3
      exact d2IvBox_mem_uvecD_hub1 Q hz (resSlot 3) 0 hWa hWb hUh hH1 hUd hHd1 hU2
        (fun i j => secondPartial_hub1_coord0_any z i j) i j

/-- **`d2yIvBox_mem`** —— `Δy` 的球级二阶盒表（全 `5×7×7` 格）✓。 -/
theorem d2yIvBox_mem (Q : Fin 7 → RatInterval) (k : Fin 5) (i j : Fin 7) {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i))
    (hW6 : 0 < (wkBoxQ Q 6).lo) (hWp : 0 < (WpIvBoxQ Q).lo) (hVp : (WpIvBoxQ Q).Valid)
    (hWa : 0 < (wkBoxQ Q (resSlot k)).lo) (hWb : 0 < (wkBoxQ Q ((resSlot k) + 1)).lo)
    {φ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hUh : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (Uvec (pad12 x) (resSlot k)).ofLp 1) x) φ2 z)
    (hH0 : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (hub0 (pad12 x)).ofLp 1) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hH1 : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (hub1 (pad12 x)).ofLp 1) x) (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) z)
    (hUd : ∀ᶠ w in nhds z, DifferentiableAt ℝ
      (fun w : Fin 7 → ℝ => (Uvec (pad12 w) (resSlot k)).ofLp 1) w)
    (hHd0 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp 1) w)
    (hHd1 : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp 1) w)
    (hU2 : ∀ i j : Fin 7, secondPartial (fun w : Fin 7 → ℝ => (Uvec (pad12 w) (resSlot k)).ofLp 1) z i j
      = secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) (resSlot k)).ofLp 1) z i j
        + secondPartial (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) ((resSlot k) + 1)).ofLp 1) z i j
        - secondPartial (fun w : Fin 7 → ℝ => (arcEnd (pad12 w) (resSlot k)).ofLp 1) z i j)
    (hWy : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (wPoint (pad12 x)).ofLp 1) x) (L2WyAt z) z)
    (hC6 : HasFDerivAt (fun x : Fin 7 → ℝ => fderiv ℝ (fun x : Fin 7 → ℝ =>
        (ringCenter (pad12 x) 6).ofLp 1) x) (L2RingC1At z 6) z)
    (hWyd : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 1) w)
    (hC6d : ∀ᶠ w in nhds z, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => (ringCenter (pad12 w) 6).ofLp 1) w) :
    (d2yIvBox Q k i j).Mem (secondPartial (DeltaY k) z i j) := by
  rw [d2yIvBox]
  by_cases hk : k = 4
  · subst hk
    rw [if_pos rfl]
    exact d2yIvBox_mem_wF Q hz hW6 hWp hVp hWy hC6 hWyd hC6d i j
  · rw [if_neg hk]
    rcases fin5_ne_four_cases hk with h0 | h1 | h2 | h3
    · subst h0
      exact d2IvBox_mem_uvecD_hub1 Q hz (resSlot 0) 1 hWa hWb hUh hH1 hUd hHd1 hU2
        (fun i j => secondPartial_hub1_coord1_any z i j) i j
    · subst h1
      exact d2IvBox_mem_uvecD_hub0 Q hz (resSlot 1) 1 hWa hWb hUh hH0 hUd hHd0 hU2
        (fun i j => secondPartial_hub0_coord1_any z i j) i j
    · subst h2
      exact d2IvBox_mem_uvecD_hub0 Q hz (resSlot 2) 1 hWa hWb hUh hH0 hUd hHd0 hU2
        (fun i j => secondPartial_hub0_coord1_any z i j) i j
    · subst h3
      exact d2IvBox_mem_uvecD_hub1 Q hz (resSlot 3) 1 hWa hWb hUh hH1 hUd hHd1 hU2
        (fun i j => secondPartial_hub1_coord1_any z i j) i j

end TowerBC

end N11Formalization
