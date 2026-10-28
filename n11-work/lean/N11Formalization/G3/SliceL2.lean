/-
  G3 first slice, level L2 -- the pi-shift reduction.

  ROLE.  L1 gives a cosine bound on the WINDOW |x| <= 39/25.  The C921 leaf
  minorant lines live on the leaf cell intervals, which lie in (-2pi, 2pi) -- and
  measured over the data, ALL 85896 cell intervals (2386 energy leaves x 36 pairs)
  lie outside [0, 39/25], so the window lemma alone never applies.  This slice
  supplies the missing step:
        cos mu = (-1)^k * cos (mu - k*pi)      (Real.cos_add_int_mul_pi),
  together with a DECIDABLE, RATIONAL criterion for choosing the integer k so that
  the shifted interval lands in the window -- using only the project's rational
  brackets piLo < pi < piHi, hence sound without knowing pi exactly.

  MEASURED DATA FACTS (evidence/g3-recon/{window_requirement,shift_data,
  k_distribution}.py, pi bracketed outward):
    * all 85896 cell intervals admit a fitting k; the admissible sets are
        {k = -1}: 42948,  {k = 0}: 35790,  {k = -2}: 7158;
    * after shifting, 0 of the 85896 shifted intervals STRADDLE 0
      (33404 lie entirely >= 0, 52492 entirely <= 0);
    * original intervals straddling 0: 0.
  (These counts are a Python computation over the recorded data, not a kernel
  result; two of the intervals are kernel-checked below.)

  HOW THE PARITY IS HANDLED (this replaces an earlier 'sorry'): the identity
  carries (-1)^k, so an UPPER bound on cos (mu - k*pi) transfers to cos mu when k
  is even, and a LOWER bound does when k is odd.  Rather than assuming anything,
  this file PROVES the absolute-value form of the L1 bound
        |cos x - cosP |x|| <= |x|^21/20!        (|x| <= 39/25)
  -- which is exactly what L1's norm-form lemma already states -- and derives both
  transfer rules from it:
        cos_eq_shift_even : Even k -> cos mu = cos (mu - k*pi)
        cos_eq_shift_odd  : Odd k  -> cos mu = -cos (mu - k*pi)
        cos_le_of_even_shift / cos_le_of_odd_shift : the two transfer rules.
  Nothing is assumed about cos and no claim is strengthened: the |cos| statement
  is DERIVED from the already-audited L1 lemma, not postulated.

  WHY NOT SIMPLY FORCE k TO BE EVEN.  Replacing an odd k by the even k-1 shifts the
  argument by an extra pi; the window has width 78/25 = 3.12 < pi, so that can leave
  the window.  (78/25 < 3 <= pi, and the project already has `three_le_pi`.)

  WHAT THIS FILE DOES NOT DO: the per-line minorant lemma and the leaf identity.
  Discipline: no sorry, no custom axiom, no native_decide, no #eval.

  DEPENDENCY NOTE.  L2 needs L1's `cos_taylor20_bound_window`.  Evidence-directory
  files are not lake-library modules, so L2 cannot `import` L1 while both live in
  `evidence/g3-recon/`.  Run this generator with `--modular` ONCE the Lead has wired
  L0+L1 into the root (modules `N11Formalization.G3.SliceL0/SliceL1`): in that mode
  the embedded block below is replaced by `import N11Formalization.G3.SliceL1` and
  the lemmas are referenced by name -- which removes the duplicate copy.
-/
import Mathlib
import N11Formalization.Interval.Taylor19C
import N11Formalization.G3.SliceL1

-- MODULAR MODE: L1 is imported as a module; no embedded copy.

namespace N11Formalization.G3SliceL2

open N11Formalization.RatInterval

/-! ## 1. The pi-shift identity -/

/-- **The pi-shift identity**: `cos mu = (-1)^k * cos (mu - k*pi)` for every integer
`k`.  (Direct from mathlib's `Real.cos_add_int_mul_pi`.) -/
theorem cos_eq_shift (mu : ℝ) (k : ℤ) :
    Real.cos mu = (-1 : ℝ) ^ k * Real.cos (mu - (k : ℝ) * Real.pi) := by
  have h := Real.cos_add_int_mul_pi (mu - (k : ℝ) * Real.pi) k
  have hr : mu - (k : ℝ) * Real.pi + (k : ℝ) * Real.pi = mu := by ring
  rw [hr] at h
  exact h

/-! ## 2. The absolute-value form of the L1 window bound -/

/-- The window Taylor polynomial of `cos`, order 20, centre 0. -/
noncomputable def cosP (x : ℝ) : ℝ :=
  taylorWithinEval Real.cos 20 (Set.Icc (0 : ℝ) (39 / 25)) 0 x

/-- **Derived, not assumed**: `|cos x - cosP |x|| <= |x|^21/20!` for `|x| <= 39/25`.
This is the content of L1's `cos_taylor20_bound_window` (a norm statement) restated
for the symmetric window via `Real.cos_neg` and `abs_choice`. -/
theorem abs_cos_sub_cosP_le {x : ℝ} (hx : |x| ≤ (39 / 25 : ℝ)) :
    abs (Real.cos x - cosP |x|) ≤ |x| ^ 21 / (Nat.factorial 20 : ℝ) := by
  have habs : |x| ∈ Set.Icc (0 : ℝ) (39 / 25) := Set.mem_Icc.mpr ⟨abs_nonneg x, hx⟩
  have h := N11Formalization.G3SliceL1.cos_taylor20_bound_window habs
  rw [Real.norm_eq_abs] at h
  have hcos : Real.cos |x| = Real.cos x := by
    rcases abs_choice x with h1 | h1
    · rw [h1]
    · rw [h1, Real.cos_neg]
  unfold cosP
  rwa [hcos] at h

/-! ## 3. The two parity transfer rules -/

/-- For even `k` the shift preserves `cos`. -/
theorem cos_eq_shift_even {mu : ℝ} {k : ℤ} (hk : Even k) :
    Real.cos mu = Real.cos (mu - (k : ℝ) * Real.pi) := by
  rw [cos_eq_shift mu k, Even.neg_one_zpow hk, one_mul]

/-- For odd `k` the shift flips the sign of `cos`. -/
theorem cos_eq_shift_odd {mu : ℝ} {k : ℤ} (hk : Odd k) :
    Real.cos mu = -Real.cos (mu - (k : ℝ) * Real.pi) := by
  rw [cos_eq_shift mu k, Odd.neg_one_zpow hk, neg_one_mul]

/-- **Transfer rule, even `k`**: an upper bound on `cos (mu - k*pi)` is an upper
bound on `cos mu`. -/
theorem cos_le_of_even_shift {mu B : ℝ} {k : ℤ} (hk : Even k)
    (hB : Real.cos (mu - (k : ℝ) * Real.pi) ≤ B) :
    Real.cos mu ≤ B :=
  (cos_eq_shift_even hk).trans_le hB

/-- **Transfer rule, odd `k`**: a LOWER bound on `cos (mu - k*pi)` gives an upper
bound on `cos mu`, namely `-c`.  (Consumers combine this with the lower half of
`abs_cos_sub_cosP_le`, which reads `cosP |x| - |x|^21/20! ≤ cos x`.) -/
theorem cos_le_of_odd_shift {mu c : ℝ} {k : ℤ} (hk : Odd k)
    (hB : c ≤ Real.cos (mu - (k : ℝ) * Real.pi)) :
    Real.cos mu ≤ -c := by
  rw [cos_eq_shift_odd hk]
  linarith

/-! ## 4. The decidable rational shift criterion -/

/-- **The rational, decidable window criterion.**  Both rational-bracket shifts of
`[a,b]` must land inside the window.  Requiring BOTH bracket ends is what makes the
criterion sound without knowing `pi`: the true shifted interval is a convex
combination of the two, so it is inside whenever both are. -/
def fitsWindow (a b : ℚ) (k : ℤ) : Prop :=
  (-(39 / 25 : ℚ) ≤ a - (k : ℚ) * piLo ∧ b - (k : ℚ) * piLo ≤ (39 / 25 : ℚ)) ∧
  (-(39 / 25 : ℚ) ≤ a - (k : ℚ) * piHi ∧ b - (k : ℚ) * piHi ≤ (39 / 25 : ℚ))

/-- **Soundness**: `fitsWindow a b k` puts the true shifted interval `[a - k*pi,
b - k*pi]` inside the window. -/
theorem fitsWindow_sound {a b : ℚ} {k : ℤ} (h : fitsWindow a b k)
    (hπ1 : (piLo : ℝ) ≤ Real.pi) (hπ2 : Real.pi ≤ (piHi : ℝ)) :
    -(39 / 25 : ℝ) ≤ (a : ℝ) - (k : ℝ) * Real.pi ∧
      (b : ℝ) - (k : ℝ) * Real.pi ≤ (39 / 25 : ℝ) := by
  obtain ⟨⟨ha1, hb1⟩, ha2, hb2⟩ := h
  have ha1' : (-(39 / 25 : ℚ) : ℝ) ≤ (a : ℝ) - (k : ℝ) * (piLo : ℝ) := by
    exact_mod_cast ha1
  have ha2' : (-(39 / 25 : ℚ) : ℝ) ≤ (a : ℝ) - (k : ℝ) * (piHi : ℝ) := by
    exact_mod_cast ha2
  have hb1' : (b : ℝ) - (k : ℝ) * (piLo : ℝ) ≤ ((39 / 25 : ℚ) : ℝ) := by
    exact_mod_cast hb1
  have hb2' : (b : ℝ) - (k : ℝ) * (piHi : ℝ) ≤ ((39 / 25 : ℚ) : ℝ) := by
    exact_mod_cast hb2
  constructor
  · rcases le_total (0 : ℝ) (k : ℝ) with hk | hk
    · have hprod : (0 : ℝ) ≤ (k : ℝ) * ((piHi : ℝ) - Real.pi) :=
        mul_nonneg hk (by linarith [hπ2])
      linarith [ha2', hprod]
    · have hprod : (0 : ℝ) ≤ (k : ℝ) * ((piLo : ℝ) - Real.pi) := by
        have h1 : (0 : ℝ) ≤ -(k : ℝ) := by linarith
        have h2 : (0 : ℝ) ≤ -((piLo : ℝ) - Real.pi) := by linarith [hπ1]
        nlinarith [mul_nonneg h1 h2]
      linarith [ha1', hprod]
  · rcases le_total (0 : ℝ) (k : ℝ) with hk | hk
    · have hprod : (k : ℝ) * ((piLo : ℝ) - Real.pi) ≤ 0 := by
        have h2 : ((piLo : ℝ) - Real.pi) ≤ 0 := by linarith [hπ1]
        nlinarith
      linarith [hb1', hprod]
    · have hprod : (k : ℝ) * ((piHi : ℝ) - Real.pi) ≤ 0 := by
        have h2 : (0 : ℝ) ≤ (piHi : ℝ) - Real.pi := by linarith [hπ2]
        nlinarith
      linarith [hb2', hprod]

/-! ## 5. Concrete instances on recorded data (leaf 3 of the C921 tree) -/

/-- Leaf 3, pair 0: the cell interval of `z_01`, already inside the window with
shift `k = 0`.  (Exact decimal literals from `cosine_dbm_local920.json`.) -/
def leaf3Pair0A : ℚ := (-487245370592825704491049684851012852549469324216366861056842412881814710897169 : ℚ) / (625000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def leaf3Pair0B : ℚ := (-20650928913498464665638257405691545496007059188171985705999583896182301404195767 : ℚ) / (50000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem fits_leaf3_pair0 : fitsWindow leaf3Pair0A leaf3Pair0B 0 := by
  unfold fitsWindow leaf3Pair0A leaf3Pair0B piLo piHi
  norm_num

/-- Leaf 3, pair 2: the cell interval lies at `(-2.34, -2.32)`, i.e. OUTSIDE the
window, and the shift `k = -1` (i.e. `+pi`) brings it inside. -/
def leaf3Pair2A : ℚ := (-1461736111778477113473149054553038557648407972649101418409499142456583551609153 : ℚ) / (625000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def leaf3Pair2B : ℚ := (-4930509410417528869210310349092680095196107553139497423239954730173498325010717 : ℚ) / (2500000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem fits_leaf3_pair2 : fitsWindow leaf3Pair2A leaf3Pair2B (-1) := by
  unfold fitsWindow leaf3Pair2A leaf3Pair2B piLo piHi
  norm_num

/-- The pair-2 interval really is outside the window before shifting (so the shift
is used, not decorative). -/
theorem leaf3Pair2_outside : leaf3Pair2A < -(39 / 25 : ℚ) := by
  unfold leaf3Pair2A; norm_num

/-- The shift moves it inside, with the `piLo` end: `a - (-1)*piLo > 0`. -/
theorem leaf3Pair2_shifted_pos : 0 < leaf3Pair2A - (-1 : ℤ) * piLo := by
  unfold leaf3Pair2A piLo; norm_num

/-- The window is narrower than `pi`, so an odd shift cannot be replaced by the
even `k - 1` in general. -/
theorem window_lt_pi : (78 / 25 : ℝ) < Real.pi := by
  have h1 : (78 / 25 : ℝ) < 3.14159265358979323846 := by norm_num
  have h2 : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  linarith

end N11Formalization.G3SliceL2

/-! ## 6. Axiom profile (read only when this file has 0 errors) -/

#print axioms N11Formalization.G3SliceL2.cos_eq_shift
#print axioms N11Formalization.G3SliceL2.abs_cos_sub_cosP_le
#print axioms N11Formalization.G3SliceL2.cos_eq_shift_even
#print axioms N11Formalization.G3SliceL2.cos_eq_shift_odd
#print axioms N11Formalization.G3SliceL2.cos_le_of_even_shift
#print axioms N11Formalization.G3SliceL2.cos_le_of_odd_shift
#print axioms N11Formalization.G3SliceL2.fitsWindow_sound
#print axioms N11Formalization.G3SliceL2.fits_leaf3_pair0
#print axioms N11Formalization.G3SliceL2.fits_leaf3_pair2
#print axioms N11Formalization.G3SliceL2.leaf3Pair2_outside
#print axioms N11Formalization.G3SliceL2.leaf3Pair2_shifted_pos
#print axioms N11Formalization.G3SliceL2.window_lt_pi
