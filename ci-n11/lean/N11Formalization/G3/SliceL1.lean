/-
  G3 first slice, level L1 -- the cos/sin Taylor window extension.

  WHY THIS SLICE.  The C921 per-leaf obligation has exactly one transcendental
  input: for each recorded minorant line, the assertion
        1 - cos mu >= s*mu + v      on the leaf's cell interval [a,b] .
  Proof route: bound `cos` ABOVE by its Taylor polynomial plus an explicit
  remainder, then reduce the obligation to a POLYNOMIAL inequality with rational
  coefficients (decidable by norm_num / nlinarith / positivity).

  The measured blocker (evidence/g3-recon/FIRST-SLICE-PROBE.md SS2.1): the
  project's high-order rational sin/cos bounds are presently stated only on the
  window [0,1] (N11Formalization.Interval.Taylor19C), while the leaf cell
  intervals, after the pi-shift reduction cos(x + k*pi) = (-1)^k cos x, need the
  window |x| <= 1.559185 -- the maximum, over all 2386 energy leaves x 36 pairs
  = 85896 cell intervals, of the distance to the nearest multiple of pi (computed
  by evidence/g3-recon/window_requirement.py).  39/25 = 1.56 covers it.

  QUANTIFIER RANGE OF THE ORIGINAL OBLIGATION (required to read SS3 correctly).
  The obligation is NOT a statement about the symmetric window: it is, for each of
  the 85896 concrete cell intervals [a,b] of the C921 tree (2386 energy leaves x 36
  pairs, each [a,b] inside (-2pi, 2pi)), the per-line assertion
        1 - cos mu >= s*mu + v      for all mu in THAT interval .
  Measured over the data (evidence/g3-recon/shift_data.py): 0 of the 85896 intervals
  straddle 0; after the pi-shift reduction 0 of the shifted intervals straddle 0
  either (33404 lie entirely >= 0, 52492 entirely <= 0).
  The `|x|` form below is therefore a TOOL, not a widened claim: it supplies an
  upper bound for cos at an argument whose absolute value is given; the consumer
  instantiates it only at nu = |mu - k*pi| >= 0, i.e. it is applied to the shifted
  interval, not to a symmetrised one.  Nothing here asserts a bound on cos over a
  set of arguments larger than the one the consumer feeds in.

  WHAT THIS FILE DELIVERS (all mirroring the two Taylor19C lemmas, with 1 -> 39/25)
    * iteratedDerivWithin20_sin_le_one_window, iteratedDerivWithin21_cos_le_one_window
      -- the uniform derivative bounds on the widened interval (endpoints included);
    * sin_taylor19_bound_window, cos_taylor20_bound_window
      -- the widened remainder bounds, x^20/19! and x^21/20!;
    * cos_le_taylor20_add_remainder_abs
      -- THE USABLE FORM on the whole symmetric window:
           cos x <= taylorWithinEval Real.cos 20 (Icc 0 (39/25)) 0 |x| + |x|^21/20! .
      It is stated with |x| on purpose: only `Real.cos_neg` and `abs_choice` are
      needed, NOT the evenness of the Taylor polynomial.  A consumer handling a cell
      interval [a,b] with a < 0 < b splits at 0 and substitutes nu = |mu|, so every
      coefficient and every argument stays rational (hence decidable);
    * the MAGNITUDE CRITERIA as exact rational facts:
        deltaMax_lt_window : 1.559185 < 39/25;
        cosRem_lt_margin, sinRem_lt_margin : both window-edge remainders are below
          the TIGHTEST leaf margin stored4348 - T^2;
        margin_gt_1e4_cosRem : that margin beats the cos remainder by > 10^4.

  Exact values (from the source certificate data; no hand transcription):
    T          = (1899919265599193545242591 : ℚ) / (5000000000000000000000000 : ℚ)
    T^2        = (3609693215794978945499128383491614947609040393281 : ℚ) / (25000000000000000000000000000000000000000000000000 : ℚ)
    stored4348 = (14438773027413103364747526082504086048756863066479200760509283185397963923981387 : ℚ) / (100000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
    margin4348 = (164233187582751012548537626258320701493355200760509283185397963923981387 : ℚ) / (100000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
               ~ 1.642332e-09
    (39/25)^21/20! ~ 4.671883e-15      (39/25)^20/19! ~ 5.989593e-14
    headroom margin4348 / ((39/25)^21/20!) ~ 3.5154e+05
  (The per-line error entering the leaf bound is further multiplied by the leaf's
  normalised weights; their total is ~0.30-0.32 on the leaves measured, which only
  improves the headroom.)

  WHAT THIS FILE DOES NOT DO
    * the pi-shift reduction itself (a separate bounded piece: cos(x+k*pi) =
      (-1)^k cos x plus rational selection of k);
    * the per-line minorant lemma;
    * the leaf identity, which needs outward brackets for L = 2*arcsin(19/50) and pi.
  Discipline: no sorry, no custom axiom, no native_decide, no #eval.
-/
import Mathlib
import N11Formalization.Interval.Taylor19C

namespace N11Formalization.G3SliceL1

/-! ## 1. The widened uniform derivative bounds -/

/-- On `Icc 0 (39/25)`, the 20th `Within` derivative of `sin` is bounded by `1`
(endpoints included, via the `UniqueDiffOn` bridge). -/
theorem iteratedDerivWithin20_sin_le_one_window :
    ∀ y ∈ Set.Icc (0 : ℝ) (39 / 25),
      ‖iteratedDerivWithin 20 Real.sin (Set.Icc (0 : ℝ) (39 / 25)) y‖ ≤ 1 := by
  intro y hy
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 39 / 25))
    (Real.contDiff_sin.contDiffAt) hy]
  rw [N11Formalization.RatInterval.iteratedDeriv20_sin, Real.norm_eq_abs]
  exact Real.abs_sin_le_one y

/-- On `Icc 0 (39/25)`, the 21st `Within` derivative of `cos` is bounded by `1`. -/
theorem iteratedDerivWithin21_cos_le_one_window :
    ∀ y ∈ Set.Icc (0 : ℝ) (39 / 25),
      ‖iteratedDerivWithin 21 Real.cos (Set.Icc (0 : ℝ) (39 / 25)) y‖ ≤ 1 := by
  intro y hy
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 39 / 25))
    (Real.contDiff_cos.contDiffAt) hy]
  rw [N11Formalization.RatInterval.iteratedDeriv21_cos, Pi.neg_apply, Real.norm_eq_abs, abs_neg]
  exact Real.abs_sin_le_one y

/-! ## 2. The widened Taylor remainder bounds -/

/-- **`sin`, order 19, window `[0, 39/25]`**:
`‖sin x − taylorWithinEval sin 19 (Icc 0 (39/25)) 0 x‖ ≤ x^20 / 19!`. -/
theorem sin_taylor19_bound_window {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (39 / 25)) :
    ‖Real.sin x - taylorWithinEval Real.sin 19 (Set.Icc (0 : ℝ) (39 / 25)) 0 x‖
      ≤ x ^ 20 / (Nat.factorial 19 : ℝ) := by
  have h := taylor_mean_remainder_bound (a := (0 : ℝ)) (b := (39 / 25 : ℝ)) (C := (1 : ℝ))
    (n := 19) (x := x) (by norm_num) Real.contDiff_sin.contDiffOn hx
    iteratedDerivWithin20_sin_le_one_window
  have h' : ‖Real.sin x - taylorWithinEval Real.sin 19 (Set.Icc (0 : ℝ) (39 / 25)) 0 x‖
      ≤ 1 * (x - 0) ^ (19 + 1) / (Nat.factorial 19 : ℝ) := h
  rw [sub_zero, one_mul] at h'
  exact h'

/-- **`cos`, order 20, window `[0, 39/25]`**:
`‖cos x − taylorWithinEval cos 20 (Icc 0 (39/25)) 0 x‖ ≤ x^21 / 20!`. -/
theorem cos_taylor20_bound_window {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (39 / 25)) :
    ‖Real.cos x - taylorWithinEval Real.cos 20 (Set.Icc (0 : ℝ) (39 / 25)) 0 x‖
      ≤ x ^ 21 / (Nat.factorial 20 : ℝ) := by
  have h := taylor_mean_remainder_bound (a := (0 : ℝ)) (b := (39 / 25 : ℝ)) (C := (1 : ℝ))
    (n := 20) (x := x) (by norm_num) Real.contDiff_cos.contDiffOn hx
    iteratedDerivWithin21_cos_le_one_window
  have h' : ‖Real.cos x - taylorWithinEval Real.cos 20 (Set.Icc (0 : ℝ) (39 / 25)) 0 x‖
      ≤ 1 * (x - 0) ^ (20 + 1) / (Nat.factorial 20 : ℝ) := h
  rw [sub_zero, one_mul] at h'
  exact h'

/-! ## 3. The usable form: a cosine upper bound on the whole symmetric window -/

/-- **The form the leaf-minorant step consumes.**  For `|x| ≤ 39/25`,
`cos x ≤ taylorWithinEval Real.cos 20 (Icc 0 (39/25)) 0 |x| + |x|^21 / 20!`.

Stated in terms of `|x|` on purpose: this needs only `Real.cos_neg` and
`abs_choice`, NOT the evenness of the Taylor polynomial.  A consumer handling a
cell interval `[a,b]` with `a < 0 < b` splits at `0` and substitutes `nu = |mu|`,
so every coefficient and every argument remains rational. -/
theorem cos_le_taylor20_add_remainder_abs {x : ℝ} (hx : |x| ≤ (39 / 25 : ℝ)) :
    Real.cos x ≤ taylorWithinEval Real.cos 20 (Set.Icc (0 : ℝ) (39 / 25)) 0 |x|
      + |x| ^ 21 / (Nat.factorial 20 : ℝ) := by
  have habs : |x| ∈ Set.Icc (0 : ℝ) (39 / 25) := ⟨abs_nonneg x, hx⟩
  have h := cos_taylor20_bound_window habs
  rw [Real.norm_eq_abs] at h
  have h2 : Real.cos |x| - taylorWithinEval Real.cos 20 (Set.Icc (0 : ℝ) (39 / 25)) 0 |x|
      ≤ |x| ^ 21 / (Nat.factorial 20 : ℝ) := le_trans (le_abs_self _) h
  have hcos : Real.cos |x| = Real.cos x := by
    rcases abs_choice x with h1 | h1
    · rw [h1]
    · rw [h1, Real.cos_neg]
  linarith [hcos ▸ h2]

/-! ## 4. The magnitude criteria (exact rational facts) -/

/-- The measured maximum distance of any C921 cell interval to a multiple of `pi`
(over all 2386 energy leaves x 36 pairs = 85896 intervals) is `1.559185`, which the
window `39/25 = 1.56` covers.  Source: evidence/g3-recon/window_requirement.py. -/
theorem deltaMax_lt_window : (311837 : ℚ) / (200000 : ℚ) < (39 : ℚ) / 25 := by norm_num

/-- The root threshold ceiling `T`, as recorded in every certificate. -/
def T : ℚ := (1899919265599193545242591 : ℚ) / (5000000000000000000000000 : ℚ)
def T2 : ℚ := (3609693215794978945499128383491614947609040393281 : ℚ) / (25000000000000000000000000000000000000000000000000 : ℚ)
/-- The recorded lower bound of the tightest energy leaf (leaf 4348, depth 62). -/
def stored4348 : ℚ := (14438773027413103364747526082504086048756863066479200760509283185397963923981387 : ℚ) / (100000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
/-- The tightest leaf margin `stored4348 - T^2` (about 1.642332e-9). -/
def margin4348 : ℚ := (164233187582751012548537626258320701493355200760509283185397963923981387 : ℚ) / (100000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem margin4348_eq : stored4348 - T2 = margin4348 := by
  unfold stored4348 T2 margin4348; norm_num

/-- The `cos` remainder at the window edge, `(39/25)^21 / 20!`. -/
def cosRem : ℚ := (39 / 25 : ℚ) ^ 21 / (Nat.factorial 20 : ℚ)
/-- The `sin` remainder at the window edge, `(39/25)^20 / 19!`. -/
def sinRem : ℚ := (39 / 25 : ℚ) ^ 20 / (Nat.factorial 19 : ℚ)

/-- **Usability criterion (headline).**  Both window-edge remainders are strictly
below the tightest leaf margin, so the window extension is strong enough. -/
theorem cosRem_lt_margin : cosRem < margin4348 := by
  unfold cosRem margin4348; norm_num

theorem sinRem_lt_margin : sinRem < margin4348 := by
  unfold sinRem margin4348; norm_num

/-- **Headroom.**  The tightest margin beats the `cos` remainder by more than `10^4`. -/
theorem margin_gt_1e4_cosRem : margin4348 > 10000 * cosRem := by
  unfold margin4348 cosRem; norm_num

end N11Formalization.G3SliceL1

/-! ## 5. Axiom profile (read only when this file has 0 errors) -/

#print axioms N11Formalization.G3SliceL1.iteratedDerivWithin20_sin_le_one_window
#print axioms N11Formalization.G3SliceL1.iteratedDerivWithin21_cos_le_one_window
#print axioms N11Formalization.G3SliceL1.sin_taylor19_bound_window
#print axioms N11Formalization.G3SliceL1.cos_taylor20_bound_window
#print axioms N11Formalization.G3SliceL1.cos_le_taylor20_add_remainder_abs
#print axioms N11Formalization.G3SliceL1.deltaMax_lt_window
#print axioms N11Formalization.G3SliceL1.margin4348_eq
#print axioms N11Formalization.G3SliceL1.cosRem_lt_margin
#print axioms N11Formalization.G3SliceL1.sinRem_lt_margin
#print axioms N11Formalization.G3SliceL1.margin_gt_1e4_cosRem
