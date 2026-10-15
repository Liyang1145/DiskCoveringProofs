import Mathlib

/-!
# STATEMENT-AUDIT — adversarial drift file for the n=11 statement

Owner: teammate `stmt-audit` (independent auditor). Write scope: `N11Formalization/Audit/**`.

Purpose: decide, **by kernel proof**, which mutations of the GUIDE §2 interface are real
statements-and-fact drifts and which are harmless. This file is an *independent transcription*
of GUIDE §2 (it deliberately does NOT import the Lead's `Definitions.lean` / `Statement.lean`,
so that the two can be diffed declaration by declaration).

Rules honoured here: no `sorry`, no new `axiom`, no `opaque`, no `native_decide`.

Contents
* A. definitional layer: `Pt`, `Covers`, `FeasibleSet`; ℓ²-vs-sup norm evidence is in the probe
  log (`audit/probe/ProbeA.out.txt`), plus `EuclideanSpace.norm_sq_eq` below.
* B. the strong-interface ↔ `IsLeast` ↔ (`sInf` + membership) equivalence, and four
  counterexample lemmas showing which weakened forms are *not* equivalent.
* B′. `≤ r` vs `< r` in the covering condition: the strict variant is not equivalent, and —
  conditionally on the theorem's own lower-bound interface — it makes the attainment half false.
* A′. `≤ 1` vs `< 1` for the target disk: provably a non-drift.
-/

namespace N11Formalization.Audit

open Metric

/-- GUIDE §2 point type: R² with the Euclidean (ℓ²) structure. -/
abbrev Pt : Type := EuclideanSpace ℝ (Fin 2)

/-- GUIDE §2 covering predicate, transcribed literally: the closed unit disk is covered by
11 closed disks of common radius `r`, centers arbitrary in ℝ², coincidences allowed. -/
def Covers (c : Fin 11 → Pt) (r : ℝ) : Prop := ∀ x, ‖x‖ ≤ 1 → ∃ i, dist x (c i) ≤ r

/-- Mutation of `Covers`: the 11 disks are made *open* (`< r` instead of `≤ r`). -/
def CoversOpenBalls (c : Fin 11 → Pt) (r : ℝ) : Prop := ∀ x, ‖x‖ ≤ 1 → ∃ i, dist x (c i) < r

/-- Mutation of `Covers`: only the *open* unit disk is required to be covered. -/
def CoversOpenTarget (c : Fin 11 → Pt) (r : ℝ) : Prop := ∀ x, ‖x‖ < 1 → ∃ i, dist x (c i) ≤ r

/-- GUIDE §2 feasible-radius set. -/
def FeasibleSet : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ c : Fin 11 → Pt, Covers c r}

/-- GUIDE §2 strong interface (the two-property form the main theorem must deliver). -/
def N11Optimum (R : ℝ) : Prop :=
  (∃ c : Fin 11 → Pt, Covers c R) ∧
    (∀ (r : ℝ) (c : Fin 11 → Pt), 0 ≤ r → Covers c r → R ≤ r)

/-! ## A. definitional sanity checks -/

theorem origin_mem_disk : ‖(0 : Pt)‖ ≤ 1 := by simp

/-- `Covers` is not vacuous: the disk is non-empty, so any covering radius is non-negative. -/
theorem covers_nonneg (c : Fin 11 → Pt) (r : ℝ) (h : Covers c r) : 0 ≤ r := by
  obtain ⟨i, hi⟩ := h 0 origin_mem_disk
  exact le_trans dist_nonneg hi

/-- B-test: the conjunct `0 ≤ r` in `FeasibleSet` is *redundant*. Dropping it is therefore not a
drift, despite GUIDE §2 asking for it explicitly. -/
theorem feasibleSet_eq_without_nonneg :
    FeasibleSet = {r : ℝ | ∃ c : Fin 11 → Pt, Covers c r} := by
  ext r
  constructor
  · rintro ⟨_, c, hc⟩; exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩; exact ⟨covers_nonneg c r hc, c, hc⟩

/-- A-test: `Fin 11 → Pt` does not build in injectivity: coincident/redundant centers are
admissible by definition (excluding them is a proof obligation, not part of the definition). -/
theorem centers_may_coincide : ∃ c : Fin 11 → Pt, ¬ Function.Injective c := by
  refine ⟨fun _ => 0, fun h => ?_⟩
  have h01 : (0 : Fin 11) = 1 := h rfl
  exact absurd h01 (show ¬ ((0 : Fin 11) = 1) from by decide)

/-- A-test: no hidden equality/upper-bound constraint — `Covers` is monotone in `r`. -/
theorem covers_mono {c : Fin 11 → Pt} {r r' : ℝ} (h : Covers c r) (hr : r ≤ r') :
    Covers c r' := by
  intro x hx
  obtain ⟨i, hi⟩ := h x hx
  exact ⟨i, le_trans hi hr⟩

/-- A-test: no symmetry is imposed — `Covers` is invariant under relabelling of the 11 centers. -/
theorem covers_perm (c : Fin 11 → Pt) (σ : Equiv.Perm (Fin 11)) (r : ℝ) (h : Covers c r) :
    Covers (c ∘ σ) r := by
  intro x hx
  obtain ⟨i, hi⟩ := h x hx
  exact ⟨σ.symm i, by simpa using hi⟩

/-- A-test: the norm of `Pt` is the ℓ² norm, not the sup norm (`EuclideanSpace.norm_sq_eq`).
This is the kernel-level version of the `#check`/`#print` evidence. -/
theorem norm_sq_eq_sum (x : Pt) : ‖x‖ ^ 2 = ‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

/-- A-test, numeric witness that `Pt` carries the ℓ² and not the sup norm: the vector `(1,1)`
has squared norm `2`, whereas its sup norm is `1`. -/
theorem norm_sq_two_one_one :
    ‖((PiLp.single 2 (0 : Fin 2) (1 : ℝ) : Pt) + (PiLp.single 2 (1 : Fin 2) (1 : ℝ) : Pt))‖ ^ 2
      = 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, PiLp.add_apply, PiLp.add_apply,
    PiLp.single_apply, PiLp.single_apply]
  norm_num

/-! ## A′. `≤ 1` → `< 1` for the target disk: provably NOT a drift -/

/-- In any real normed space, the closed unit ball is the closure of the open unit ball. -/
lemma closure_ball_one_eq_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    closure (ball (0 : E) 1) = closedBall (0 : E) 1 := by
  refine Set.Subset.antisymm closure_ball_subset_closedBall ?_
  intro x hx
  have hx' : ‖x‖ ≤ 1 := by simpa [dist_zero_right] using mem_closedBall.mp hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min (ε / 2) (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδle : δ ≤ ε / 2 := min_le_left _ _
  have hδle2 : δ ≤ 1 / 2 := min_le_right _ _
  have h1δ : 0 < 1 - δ := by linarith
  refine ⟨(1 - δ) • x, ?_, ?_⟩
  · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos h1δ]
    have h1 : (1 - δ) * ‖x‖ ≤ (1 - δ) * 1 := mul_le_mul_of_nonneg_left hx' h1δ.le
    linarith
  · rw [dist_comm, dist_eq_norm]
    have h1smul : (1 - δ) • x - x = (1 - δ) • x - (1 : ℝ) • x := by rw [one_smul]
    have hsub : (1 - δ) • x - x = ((1 - δ) - 1) • x := by rw [h1smul, ← sub_smul]
    rw [hsub, norm_smul, Real.norm_eq_abs]
    have habs : |(1 - δ) - 1| = δ := by
      rw [abs_of_nonpos (by linarith : (1 - δ) - 1 ≤ 0)]
      ring
    rw [habs]
    have h1 : δ * ‖x‖ ≤ δ * 1 := mul_le_mul_of_nonneg_left hx' hδpos.le
    linarith

/-- A′-test: **non-drift**. Opening the target disk does not change the covering predicate,
because the union of the 11 closed `r`-balls is closed and the closed unit disk is the closure
of the open unit disk. So `‖x‖ ≤ 1` and `‖x‖ < 1` in `Covers` are interchangeable. -/
theorem covers_iff_coversOpenTarget (c : Fin 11 → Pt) (r : ℝ) :
    Covers c r ↔ CoversOpenTarget c r := by
  refine ⟨fun h x hx => h x (le_of_lt hx), fun h x hx => ?_⟩
  have hK : IsClosed (⋃ i, closedBall (c i) r) := by
    have h := (Set.finite_univ (α := Fin 11)).isClosed_biUnion
      (fun i _ => isClosed_closedBall (x := c i) (ε := r))
    simpa using h
  have hsub : ball (0 : Pt) 1 ⊆ ⋃ i, closedBall (c i) r := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa [mem_ball, dist_zero_right] using hy
    obtain ⟨i, hi⟩ := h y hy'
    exact Set.mem_iUnion.mpr ⟨i, mem_closedBall.mpr hi⟩
  have hxcl : x ∈ closure (ball (0 : Pt) 1) := by
    rw [closure_ball_one_eq_closedBall]
    exact mem_closedBall.mpr (by simpa [dist_zero_right] using hx)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hK.closure_subset (closure_mono hsub hxcl))
  exact ⟨i, mem_closedBall.mp hi⟩

/-! ## A″. `≤ r` → `< r` for the disks: NOT a non-drift -/

theorem covers_zero_one : Covers (fun _ : Fin 11 => (0 : Pt)) 1 := by
  intro x hx
  exact ⟨0, by simpa [dist_zero_right] using hx⟩

theorem not_coversOpenBalls_zero_one :
    ¬ CoversOpenBalls (fun _ : Fin 11 => (0 : Pt)) 1 := by
  intro h
  have hx : ‖(PiLp.single 2 (0 : Fin 2) (1 : ℝ) : Pt)‖ ≤ 1 := by
    rw [PiLp.norm_single]; norm_num
  obtain ⟨_, hi⟩ := h _ hx
  have h1 : dist (PiLp.single 2 (0 : Fin 2) (1 : ℝ) : Pt) (0 : Pt) = 1 := by
    rw [dist_zero_right, PiLp.norm_single]; norm_num
  linarith

/-- A″-test: making the 11 disks open **does** change the predicate at the same radius
(concrete `c ≡ 0`, `r = 1`). So `< r` is not a stylistic variant of `≤ r`. -/
theorem openBalls_mutation_changes_the_predicate :
    ¬ (∀ (c : Fin 11 → Pt) (r : ℝ), Covers c r ↔ CoversOpenBalls c r) := by
  intro h
  exact not_coversOpenBalls_zero_one ((h (fun _ => (0 : Pt)) 1).mp covers_zero_one)

/-! ## B. strong interface ↔ `IsLeast` ↔ (`sInf` + membership) -/

/-- The GUIDE §2 strong interface is *equivalent* to `IsLeast FeasibleSet R`. Note the two
non-obvious points: (i) the strong interface does not need to state `0 ≤ R`, because
`covers_nonneg` supplies it — the redundancy of `feasibleSet_eq_without_nonneg` is what makes the
two forms interderivable; (ii) the equivalence is two-sided (a genuine iff, not one implication). -/
theorem n11Optimum_iff_isLeast (R : ℝ) : N11Optimum R ↔ IsLeast FeasibleSet R := by
  constructor
  · rintro ⟨⟨c, hc⟩, hlow⟩
    refine ⟨⟨covers_nonneg c R hc, c, hc⟩, ?_⟩
    intro b hb
    have hb' : 0 ≤ b ∧ ∃ c : Fin 11 → Pt, Covers c b := hb
    exact hlow b hb'.2.choose hb'.1 hb'.2.choose_spec
  · rintro ⟨hmem, hlow⟩
    have hmem' : 0 ≤ R ∧ ∃ c : Fin 11 → Pt, Covers c R := hmem
    exact ⟨hmem'.2, fun r c hr hc => hlow (show r ∈ FeasibleSet from ⟨hr, c, hc⟩)⟩

/-- `IsLeast S R` is *equivalent* to `sInf S = R` **together with** `R ∈ S`; the membership is
not implied by the `sInf` equation. (Condition: `S` non-empty and bounded below — the hypothesis
GUIDE §2 demands before touching `sInf`.) -/
theorem isLeast_iff_sInf_eq_and_mem (S : Set ℝ) (R : ℝ) (hne : S.Nonempty)
    (hbdd : BddBelow S) : IsLeast S R ↔ (sInf S = R ∧ R ∈ S) := by
  constructor
  · intro h; exact ⟨h.csInf_eq, h.1⟩
  · rintro ⟨heq, hmem⟩
    refine ⟨hmem, ?_⟩
    have hglb : IsGLB S (sInf S) := isGLB_csInf hne hbdd
    rw [heq] at hglb
    exact hglb.1

/-- B-test: `FeasibleSet` is **unconditionally** bounded below (by `0`, via `covers_nonneg`) —
this half of GUIDE §2's precondition costs nothing. -/
theorem feasibleSet_bddBelow : BddBelow FeasibleSet := ⟨0, fun _ hr => hr.1⟩

/-- B-test: `FeasibleSet` is upward closed (a half-line, no gaps), by `covers_mono`. -/
theorem feasibleSet_upward : ∀ r ∈ FeasibleSet, ∀ r' : ℝ, r ≤ r' → r' ∈ FeasibleSet := by
  rintro r ⟨hr0, c, hc⟩ r' hrr'
  exact ⟨le_trans hr0 hrr', c, covers_mono hc hrr'⟩

/-- B-test: `FeasibleSet.Nonempty` is also **free** (take the 11 coincident centers at the origin
and `r = 1`): it only asks for *some* covering radius, not for one at a distinguished value. The
half of GUIDE §2's precondition that is *not* free is membership at the specific `R`
(`R ∈ FeasibleSet` = attainment at that radius). -/
theorem feasibleSet_nonempty : FeasibleSet.Nonempty :=
  ⟨1, by norm_num, fun _ => 0, covers_zero_one⟩

/-- B-test: `FeasibleSet.Nonempty` is exactly "some cover exists at some radius" — it carries no
information about the *optimal* radius. -/
theorem feasibleSet_nonempty_iff :
    FeasibleSet.Nonempty ↔ ∃ (r : ℝ) (c : Fin 11 → Pt), 0 ≤ r ∧ Covers c r := by
  constructor
  · rintro ⟨r, hr⟩
    have hr' : 0 ≤ r ∧ ∃ c : Fin 11 → Pt, Covers c r := hr
    exact ⟨r, hr'.2.choose, hr'.1, hr'.2.choose_spec⟩
  · rintro ⟨r, c, hr, hc⟩
    exact ⟨r, hr, c, hc⟩

/-- B: the form of the main theorem via `sInf`. Note the honest content: `BddBelow` and `Nonempty`
are both free (`feasibleSet_bddBelow`, `feasibleSet_nonempty`), so the *only* non-trivial conjunct
on the right-hand side is `R ∈ FeasibleSet` (attainment at this specific `R`); it cannot be
dropped — see `sInf_eq_does_not_imply_isLeast`. -/
theorem n11Optimum_iff_sInf_eq_and_attained (R : ℝ) :
    N11Optimum R ↔ (sInf FeasibleSet = R ∧ R ∈ FeasibleSet) :=
  (n11Optimum_iff_isLeast R).trans
    (isLeast_iff_sInf_eq_and_mem FeasibleSet R feasibleSet_nonempty feasibleSet_bddBelow)

/-- B-drift 1: `sInf S = a` alone does **not** give `IsLeast S a` (witness `S = Ioi 0`, `a = 0`).
This is the "default value of `sInf` on an empty/unbounded set" hazard of GUIDE §2. -/
theorem sInf_eq_does_not_imply_isLeast :
    ∃ (S : Set ℝ) (a : ℝ), sInf S = a ∧ ¬ IsLeast S a :=
  ⟨Set.Ioi 0, 0, csInf_Ioi, fun h => (lt_irrefl (0 : ℝ)) h.1⟩

/-- B-drift 2: proving only `IsGLB` (glb, without membership) does not give the minimum. -/
theorem isGLB_does_not_imply_isLeast :
    ∃ (S : Set ℝ) (a : ℝ), IsGLB S a ∧ ¬ IsLeast S a :=
  ⟨Set.Ioi 0, 0, isGLB_Ioi, fun h => (lt_irrefl (0 : ℝ)) h.1⟩

/-- B-drift 3: the reversed reading of `IsLeast` (upper bound instead of lower bound) is false. -/
theorem reversed_isLeast_is_false :
    ∃ (S : Set ℝ) (a : ℝ), IsLeast S a ∧ ¬ (a ∈ S ∧ ∀ b ∈ S, b ≤ a) :=
  ⟨Set.Ici 0, 0, isLeast_Ici, fun h => by
    have h1 : (1 : ℝ) ≤ 0 := h.2 1 (show (1 : ℝ) ∈ Set.Ici 0 from by norm_num)
    linarith⟩

/-- B-drift 4: the lower-bound side alone cannot pin the number (any smaller number satisfies it);
what is missing is exactly membership/attainment. -/
theorem lowerBound_side_alone_not_determining :
    ∃ (S : Set ℝ) (a a' : ℝ),
      a ≠ a' ∧ (∀ b ∈ S, a ≤ b) ∧ (∀ b ∈ S, a' ≤ b) ∧ ¬ IsLeast S a' :=
  ⟨Set.Ioi 0, 0, -1, by norm_num,
    fun _ hb => le_of_lt hb,
    fun _ hb => le_trans (show (-1 : ℝ) ≤ 0 by norm_num) (le_of_lt hb),
    fun h => absurd (show (0 : ℝ) < -1 from h.1) (by norm_num)⟩

/-! ## B′. `≤ r` → `< r` on the *attainment* half is a fatal drift (conditional on the
lower-bound interface, which is the object of the audit — no circularity, no axiom) -/

/-- Minimum distance from `x` to the 11 centers. -/
noncomputable def clearance (c : Fin 11 → Pt) (x : Pt) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => dist x (c i))

lemma continuous_clearance (c : Fin 11 → Pt) : Continuous (clearance c) := by
  have h' : Continuous
      (Finset.univ.inf' Finset.univ_nonempty (fun i => fun x : Pt => dist x (c i))) :=
    Continuous.finset_inf' (s := Finset.univ) Finset.univ_nonempty
      (fun i _ => by exact continuous_id.dist continuous_const)
  have heq : clearance c
      = Finset.univ.inf' Finset.univ_nonempty (fun i => fun x : Pt => dist x (c i)) := by
    funext x
    exact (Finset.inf'_apply Finset.univ_nonempty (fun i (y : Pt) => dist y (c i)) x).symm
  rw [heq]
  exact h'

/-- **Main drift lemma.** If the lower-bound half of the n=11 statement holds at `R`, then the
mutated attainment statement `∃ c, CoversOpenBalls c R` is *false*. Proof: the clearance function
`x ↦ min_i dist x (c i)` is continuous, so on the compact disk it attains its maximum `m < R`
(strictness); the radius `r' = (m+R)/2 < R` then still covers, contradicting the lower bound.
Consequence: replacing `≤ r` by `< r` in `Covers` does not merely restyle the statement — it makes
the attainment half false, while leaving `sInf` unchanged. (`∃ c, Covers c R` is not even needed
as a hypothesis: strictness already implies `Covers c R`.) -/
theorem no_strict_cover_at_lowerBound (R : ℝ)
    (hlow : ∀ (r : ℝ) (c : Fin 11 → Pt), 0 ≤ r → Covers c r → R ≤ r) :
    ¬ ∃ c : Fin 11 → Pt, CoversOpenBalls c R := by
  rintro ⟨c₀, hstrict⟩
  obtain ⟨x₀, hx₀mem, hx₀max⟩ :=
    (ProperSpace.isCompact_closedBall (0 : Pt) 1).exists_isMaxOn
      ⟨0, by simp⟩ (continuous_clearance c₀).continuousOn
  have hx₀norm : ‖x₀‖ ≤ 1 := by simpa [dist_zero_right] using mem_closedBall.mp hx₀mem
  have hmax : ∀ y ∈ closedBall (0 : Pt) 1, clearance c₀ y ≤ clearance c₀ x₀ :=
    Filter.eventually_principal.mp hx₀max
  obtain ⟨i₀, hi₀⟩ := hstrict x₀ hx₀norm
  have hle₀ : clearance c₀ x₀ ≤ dist x₀ (c₀ i₀) := by
    change Finset.univ.inf' Finset.univ_nonempty (fun i => dist x₀ (c₀ i)) ≤ dist x₀ (c₀ i₀)
    exact Finset.inf'_le (fun i => dist x₀ (c₀ i)) (Finset.mem_univ i₀)
  have hlt : clearance c₀ x₀ < R := lt_of_le_of_lt hle₀ hi₀
  have hnn : 0 ≤ clearance c₀ x₀ := by
    change 0 ≤ Finset.univ.inf' Finset.univ_nonempty (fun i => dist x₀ (c₀ i))
    exact Finset.le_inf' Finset.univ_nonempty (fun i => dist x₀ (c₀ i)) (fun _ _ => dist_nonneg)
  set r' : ℝ := (clearance c₀ x₀ + R) / 2 with hr'def
  have hr'nn : 0 ≤ r' := by rw [hr'def]; linarith
  have hr'lt : r' < R := by rw [hr'def]; linarith
  have hc' : Covers c₀ r' := by
    intro x hx
    have hxD : x ∈ closedBall (0 : Pt) 1 :=
      mem_closedBall.mpr (by simpa [dist_zero_right] using hx)
    have hle : clearance c₀ x ≤ clearance c₀ x₀ := hmax x hxD
    have hlt2 : clearance c₀ x < r' := by rw [hr'def]; linarith
    have hlt3 : Finset.univ.inf' Finset.univ_nonempty (fun i => dist x (c₀ i)) < r' := hlt2
    obtain ⟨i, _, hi⟩ := (Finset.inf'_lt_iff Finset.univ_nonempty).mp hlt3
    exact ⟨i, le_of_lt hi⟩
  have := hlow r' c₀ hr'nn hc'
  linarith

/-- B′-corollary: with the theorem's lower bound in force, the strict variant and the original
differ exactly in attainment (the original still has an attainting configuration, the strict one
has none). -/
theorem strict_variant_makes_attainment_false (R : ℝ)
    (hlow : ∀ (r : ℝ) (c : Fin 11 → Pt), 0 ≤ r → Covers c r → R ≤ r)
    (hatt : ∃ c : Fin 11 → Pt, Covers c R) :
    (∃ c : Fin 11 → Pt, Covers c R) ∧ ¬ ∃ c : Fin 11 → Pt, CoversOpenBalls c R :=
  ⟨hatt, no_strict_cover_at_lowerBound R hlow⟩

/-! ## D-note. arithmetic sanity of the *stated* outward bracket of `Rstar`

This is **not** a proof that `Rstar` lies there (that is C891/C922, not formalized yet). It is an
exact-rational check that the bracket quoted in GUIDE §2 is well-formed, read as exact decimal
rationals (never as floats), and lies inside the elementary window `(1/4, 1/2)`. -/

theorem rstar_stated_bracket_sane :
    ((3799838531198386897222616061358 : ℚ) / 10 ^ 31
        < 3799838531198386897222616061364 / 10 ^ 31)
      ∧ ((1 : ℚ) / 4 < 3799838531198386897222616061358 / 10 ^ 31)
      ∧ ((3799838531198386897222616061364 : ℚ) / 10 ^ 31 < 1 / 2) := by
  norm_num

/-! ## E. anti-drift artefact: full types of the audited statements -/

#print N11Optimum
#print n11Optimum_iff_isLeast
#print n11Optimum_iff_sInf_eq_and_attained
#print isLeast_iff_sInf_eq_and_mem
#print no_strict_cover_at_lowerBound
#print axioms n11Optimum_iff_isLeast
#print axioms n11Optimum_iff_sInf_eq_and_attained
#print axioms no_strict_cover_at_lowerBound
#print axioms covers_iff_coversOpenTarget
#print axioms norm_sq_two_one_one

end N11Formalization.Audit
