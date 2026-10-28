/-
  **The leaf-level aggregation checker** -- 2386 certificates instead of 124130, and at the
  same time the endpoint of the leaf accounting.

  Leaf obligation:  f0 - lambda.b + min_q r_q > T^2  with
        f0 = sum_l weight_k * gamma_l * ( s_l * (i-j) * L + v'_l ),  L = 2 arcsin(19/50).

  `L` enters LINEARLY, with coefficient c_l = weight*gamma*s*(i-j) of either sign, so the
  outward direction depends on that sign; this consumes the root-resident
  `ArcsinBracket.arc_L_mem`.

  WHY THE BRACKET MUST BE NARROW (measured, not assumed).  The leaf sum amplifies the
  bracket half-width by sum|c_l|: for leaf 4348 (the tightest, margin 1.64233187582751e-09)
  sum|c_l| = 0.447626, so a 4e-4-wide bracket loses sum|c|*w/2 = 8.952525e-05 -- matching
  the observed deficit 8.951780e-05 to 8e-5 relative, i.e. the whole deficit was bracket
  width, nothing to do with the kernel (~1e-30).  With the 1e-12 bracket the worst-case
  loss is 4.48e-13 and the margin survives with ~3660x room.

  SCALE CONVENTION.  All quantities are integers at one common scale D > 0:
        c_i = D*(weight*gamma*s*(i-j))  (rounded DOWN)      d_i = D*(weight*gamma*v'_i)
        Llo/Lhi = D*(L bounds) rounded OUTWARD
        lamB = D*(lambda.b) rounded UP ; rmin = D*(min_q r_q) rounded DOWN ; T2 = D*(T^2) UP
  The checker recomputes  sum_i ( c_i * (if 0 < c_i then Llo else Lhi) + d_i*D )
      - lamB*D + rmin*D  >  T2*D
  from the raw arrays; it never trusts a precomputed f0.

  Discipline: no sorry, no custom axiom, no native_decide, no #eval.
-/
import Mathlib
import N11Formalization.Interval.ArcsinBracket

namespace N11Formalization.LeafAgg

/-! ## 1. The checker -/

/-- The scaled L-dependent sum: `Llo` for positive coefficients, `Lhi` for the rest. -/
def lsum {n : ℕ} (c d : Fin n → ℤ) (Llo Lhi D : ℤ) : ℤ :=
  ∑ i, (if 0 < c i then c i * Llo + d i * D else c i * Lhi + d i * D)

/-- **The leaf checker.**  `b` records the sign branch used for each line; the checker
verifies that this branch table really is the sign table, then performs ONE integer
comparison. -/
def leafCheck {n : ℕ} (c d : Fin n → ℤ) (b : Fin n → Bool)
    (Llo Lhi D lamB rmin T2 : ℤ) : Bool :=
  decide (0 < D) && decide (Llo ≤ Lhi) &&
  decide (∀ i, b i = decide (0 < c i)) &&
  decide (lsum c d Llo Lhi D - lamB * D + rmin * D > T2 * D)

/-! ## 2. Soundness (one theorem, no literals), in scaled form -/

/-- **Soundness** in SCALED form: multiply the leaf obligation by `D^2 > 0`, which keeps the
algebra division-free.  The unscaled form is the corollary below. -/
theorem leafCheck_sound {n : ℕ} {c d : Fin n → ℤ} {b : Fin n → Bool}
    {Llo Lhi D lamB rmin T2 : ℤ} {cR dR : Fin n → ℝ} {L lamBR rminR T2R : ℝ}
    (h : leafCheck c d b Llo Lhi D lamB rmin T2 = true)
    (hD : (0 : ℝ) < D)
    (hLlo : (Llo : ℝ) / D ≤ L) (hLhi : L ≤ (Lhi : ℝ) / D)
    (hLlo0 : 0 ≤ (Llo : ℝ) / D) (_hLhi0 : 0 ≤ (Lhi : ℝ) / D)
    (hcR : ∀ i, (c i : ℝ) / D ≤ cR i)
    (hcR0 : ∀ i, b i = false → cR i ≤ 0)
    (hd : ∀ i, (d i : ℝ) / D ≤ dR i)
    (hlamB : lamBR ≤ (lamB : ℝ) / D) (hrmin : (rmin : ℝ) / D ≤ rminR)
    (hT2 : T2R ≤ (T2 : ℝ) / D) :
    ((∑ i, (cR i * L + dR i)) - lamBR + rminR) * D ^ 2 > T2R * D ^ 2 := by
  have h' := h
  simp only [leafCheck, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨hDpos, hLH⟩, hb⟩, hsum⟩ := h'
  have hDposR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  -- termwise: the checker's scaled term is below the real term scaled by D^2
  have hterm : ∀ i, (c i : ℝ) * (if b i then (Llo : ℝ) else (Lhi : ℝ)) + (d i : ℝ) * D
      ≤ (cR i * L + dR i) * D ^ 2 := by
    intro i
    have hbi : b i = decide (0 < c i) := by simpa using hb i
    by_cases hpos : 0 < c i
    · have hbtrue : b i = true := by rw [hbi]; exact decide_eq_true hpos
      rw [hbtrue]
      have hci0 : (0 : ℝ) ≤ (c i : ℝ) := by exact_mod_cast hpos.le
      have hcRi : (c i : ℝ) ≤ cR i * D := (div_le_iff₀ hDposR).mp (hcR i)
      have hdi : (d i : ℝ) ≤ dR i * D := (div_le_iff₀ hDposR).mp (hd i)
      have hLloD : (Llo : ℝ) ≤ L * D := (div_le_iff₀ hDposR).mp hLlo
      have hLn : (0 : ℝ) ≤ L := le_trans hLlo0 hLlo
      have h0 : (0 : ℝ) ≤ L * D := mul_nonneg hLn hDposR.le
      have s1 : (c i : ℝ) * (Llo : ℝ) ≤ (c i : ℝ) * (L * D) :=
        mul_le_mul_of_nonneg_left hLloD hci0
      have s2 : (c i : ℝ) * (L * D) ≤ (cR i * L) * D ^ 2 :=
        calc (c i : ℝ) * (L * D) ≤ (cR i * D) * (L * D) :=
              mul_le_mul_of_nonneg_right hcRi h0
          _ = (cR i * L) * D ^ 2 := by ring
      have s3 : (d i : ℝ) * D ≤ (dR i) * D ^ 2 :=
        calc (d i : ℝ) * D ≤ (dR i * D) * D := mul_le_mul_of_nonneg_right hdi hDposR.le
          _ = (dR i) * D ^ 2 := by ring
      calc (c i : ℝ) * (Llo : ℝ) + (d i : ℝ) * D
          ≤ (cR i * L) * D ^ 2 + (dR i) * D ^ 2 := add_le_add (le_trans s1 s2) s3
        _ = (cR i * L + dR i) * D ^ 2 := by ring
    · have hbfalse : b i = false := by rw [hbi]; exact decide_eq_false hpos
      rw [hbfalse]
      have hci0 : (c i : ℝ) ≤ 0 := by exact_mod_cast (not_lt.mp hpos)
      have hcr0 : cR i ≤ 0 := hcR0 i hbfalse
      have hcRi : (c i : ℝ) ≤ cR i * D := (div_le_iff₀ hDposR).mp (hcR i)
      have hdi : (d i : ℝ) ≤ dR i * D := (div_le_iff₀ hDposR).mp (hd i)
      have hLhiD : L * D ≤ (Lhi : ℝ) := (le_div_iff₀ hDposR).mp hLhi
      have hLn : (0 : ℝ) ≤ L := le_trans hLlo0 hLlo
      have hLi0 : (0 : ℝ) ≤ (Lhi : ℝ) := le_trans (mul_nonneg hLn hDposR.le) hLhiD
      have h0 : (0 : ℝ) ≤ L * D := mul_nonneg hLn hDposR.le
      have s1 : (c i : ℝ) * (Lhi : ℝ) ≤ (c i : ℝ) * (L * D) :=
        mul_le_mul_of_nonpos_left hLhiD hci0
      have s2 : (c i : ℝ) * (L * D) ≤ (cR i * L) * D ^ 2 :=
        calc (c i : ℝ) * (L * D) ≤ (cR i * D) * (L * D) :=
              mul_le_mul_of_nonneg_right hcRi h0
          _ = (cR i * L) * D ^ 2 := by ring
      have s3 : (d i : ℝ) * D ≤ (dR i) * D ^ 2 :=
        calc (d i : ℝ) * D ≤ (dR i * D) * D := mul_le_mul_of_nonneg_right hdi hDposR.le
          _ = (dR i) * D ^ 2 := by ring
      calc (c i : ℝ) * (Lhi : ℝ) + (d i : ℝ) * D
          ≤ (cR i * L) * D ^ 2 + (dR i) * D ^ 2 := add_le_add (le_trans s1 s2) s3
        _ = (cR i * L + dR i) * D ^ 2 := by ring
  have hsumR : (∑ i, ((c i : ℝ) * (if b i then (Llo : ℝ) else (Lhi : ℝ)) + (d i : ℝ) * D))
      ≤ (∑ i, (cR i * L + dR i)) * D ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => hterm i)
  have hsumZ : ((lsum c d Llo Lhi D : ℤ) : ℝ) - (lamB : ℝ) * D + (rmin : ℝ) * D
      > (T2 : ℝ) * D := by exact_mod_cast hsum
  have hcast : ((lsum c d Llo Lhi D : ℤ) : ℝ)
      = ∑ i, ((c i : ℝ) * (if b i then (Llo : ℝ) else (Lhi : ℝ)) + (d i : ℝ) * D) := by
    rw [lsum]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    have hbi : b i = decide (0 < c i) := by simpa using hb i
    by_cases hpos : 0 < c i
    · have hbt : b i = true := by rw [hbi]; exact decide_eq_true hpos
      simp [hbt, hpos]
    · have hbf : b i = false := by rw [hbi]; exact decide_eq_false hpos
      simp [hbf, hpos]
  rw [hcast] at hsumZ
  -- convert the three division-form hypotheses to multiplicative form (nlinarith does not
  -- consume division; see the "shape" caliber), then combine
  have hlamB' : lamBR * D ≤ (lamB : ℝ) := (le_div_iff₀ hDposR).mp hlamB
  have hrmin' : (rmin : ℝ) ≤ rminR * D := (div_le_iff₀ hDposR).mp hrmin
  have hT2' : T2R * D ≤ (T2 : ℝ) := (le_div_iff₀ hDposR).mp hT2
  have hb1 : T2R * D ^ 2 ≤ (T2 : ℝ) * D := by nlinarith [hT2', hDposR]
  have hb2 : lamBR * D ^ 2 ≤ (lamB : ℝ) * D := by nlinarith [hlamB', hDposR]
  have hb3 : (rmin : ℝ) * D ≤ rminR * D ^ 2 := by nlinarith [hrmin', hDposR]
  have hgoal : T2R * D ^ 2 + lamBR * D ^ 2 - rminR * D ^ 2
      ≤ (T2 : ℝ) * D + (lamB : ℝ) * D - (rmin : ℝ) * D := by linarith
  nlinarith [hsumR, hsumZ, hgoal, hDposR]

/-- The unscaled form, for consumers: the leaf obligation itself. -/
theorem leafCheck_sound_unscaled {n : ℕ} {c d : Fin n → ℤ} {b : Fin n → Bool}
    {Llo Lhi D lamB rmin T2 : ℤ} {cR dR : Fin n → ℝ} {L lamBR rminR T2R : ℝ}
    (h : leafCheck c d b Llo Lhi D lamB rmin T2 = true)
    (hD : (0 : ℝ) < D)
    (hLlo : (Llo : ℝ) / D ≤ L) (hLhi : L ≤ (Lhi : ℝ) / D)
    (hLlo0 : 0 ≤ (Llo : ℝ) / D) (_hLhi0 : 0 ≤ (Lhi : ℝ) / D)
    (hcR : ∀ i, (c i : ℝ) / D ≤ cR i)
    (hcR0 : ∀ i, b i = false → cR i ≤ 0)
    (hd : ∀ i, (d i : ℝ) / D ≤ dR i)
    (hlamB : lamBR ≤ (lamB : ℝ) / D) (hrmin : (rmin : ℝ) / D ≤ rminR)
    (hT2 : T2R ≤ (T2 : ℝ) / D) :
    (∑ i, (cR i * L + dR i)) - lamBR + rminR > T2R := by
  have hscaled := leafCheck_sound h hD hLlo hLhi hLlo0 _hLhi0 hcR hcR0 hd hlamB hrmin hT2
  have hsq : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  nlinarith [hscaled, hsq]

end N11Formalization.LeafAgg

/-! ## 3. Axiom profile (read only when this file has 0 errors) -/

#print axioms N11Formalization.LeafAgg.leafCheck_sound
#print axioms N11Formalization.LeafAgg.leafCheck_sound_unscaled
