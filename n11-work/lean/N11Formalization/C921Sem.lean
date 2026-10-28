/-
  **C921 SEMANTIC PREMISE -- the exact Lean statement of gap (3), plus the consumer wiring.**
  T15 (c921-stat), R267b.  Candidate module: NOT imported by the root; imports concrete
  root modules only (G3LeafChecker + Conditional.RootSpec), never the umbrella.

  WHAT THIS FILE DOES
  -------------------
  1. NAMES the semantic premise of C921 (finite-certificate integrity) -- the gap the
     cone carries as "GAP CARRIED (gap (3)): the semantic identity of the recorded source
     quantities" (G3LeafChecker / G3ArcConstants / G3Batch_* headers):

        `LeafSemBound` : the recorded `energy_lower` -- LITERALLY the quantity that
        `leafBound_of_check` / `leafBound_of_batch` / `leafBound_of_floorData` conclude
        on -- is a lower bound of the canonical oracle energy `V2 = V(U(y))^2` on the
        leaf's domain (DBM box ∩ closed 8-simplex).

     The oracle is encoded MOST CONSERVATIVELY: an OPAQUE function
     `V2 : (Fin 8 → ℝ) → ℝ`.  No SOC primal/dual machinery is invented here; pinning
     `V2` to the real oracle is an explicitly recorded separate obligation.

  2. PROVES the wiring (no mathematics beyond the displayed hypotheses):
        checker pass   +  LeafSemBound           ⇒ oracle lower bound on the leaf,
        (per leaf)     +  P-coverage hypothesis  ⇒ oracle lower bound on the whole simplex,
        oracle global  +  C923 oracle-relaxation + `Rstar ≤ T` pin ⇒ the `hbound` slot,
        `hbound`       +  `hattain`              ⇒ `N11MainStatement (Rstar S)`.

  WHAT THIS FILE DOES *NOT* CLAIM
  -------------------------------
  * it does not PROVE `LeafSemBound` for any leaf (that is gap (3) proper: weak duality
    `V² ≥ E_α`; whole-cell affine cos-minorants `1 − cos z ≥ s·z + v`; β/γ mixtures; the
    LP step `λ ≥ 0, Ay ≤ b, y ∈ simplex ⇒ f0 + c·y ≥ f0 − λᵀb + min_q r_q`);
  * it does not prove P-coverage (tree partition, Σ2^-depth = 1, boundary seams, and the
    120 LOCAL leaves -- the local C919/C920 certificates are a different certificate
    family and are deliberately NOT modeled here);
  * it does not pin `V2` to the SOC oracle, nor `Rstar S` to `T` numerically.

  Discipline: no sorry, no custom axiom, no native_decide, no #eval.  This file prints
  NOTHING (gate = exit 0 / stdout 0 B / stderr 0 B / 0 warnings); the axiom profile is
  printed by the companion probe file `C921Sem-probe.lean` (byte-copy + prints).
-/
import Mathlib
import N11Formalization.G3LeafChecker
import N11Formalization.Conditional.RootSpec

namespace N11Formalization.C921Sem

open N11Formalization.LeafAgg          -- leafCheck, lsum
open N11Formalization.G3LeafChecker    -- leafBound_of_check / _batch / _floorData, ...
open N11Formalization.G3ArcConstants   -- scaleD, arcLlo, arcLhi, thresh, threshSq, arc_hyp_*

/-! ## 1. Objects: shape simplex, leaf domain, recorded energy lower  -/

/-- The closed 8-dimensional shape simplex: `y ≥ 0` and `∑ y = 1`.
(source caliber: FIXED-SWITCH-SOC-REDUCTION -- `y` ranges over the CLOSED simplex;
anchors `θ_i = i·L − D·∑_{j<i} y_j`, `L = 2·arcsin(19/50)`, `D = 9L − 2π`.) -/
def InSimplex (y : Fin 8 → ℝ) : Prop := (∀ q, 0 ≤ y q) ∧ ∑ q, y q = 1

/-- One DBM row evaluated at `y`: `(A j) ⬝ y ≤ b j`.  Exact rational rows, real evaluation.
(source caliber: `cosine_dbm_local920.json`; root constraints = exactly the closed
simplex; exact rational Floyd closure only ADDS implied rows.) -/
def DBMRow (a : Fin 8 → ℚ) (bq : ℚ) (y : Fin 8 → ℝ) : Prop :=
  (∑ q, (a q : ℝ) * y q) ≤ (bq : ℝ)

/-- The leaf domain: all DBM rows hold.  The leaf's split history (which sub-box of the
simplex it certifies) is encoded in the pair `(A, b)`. -/
def InLeafDom {m : ℕ} (A : Fin m → Fin 8 → ℚ) (bV : Fin m → ℚ) (y : Fin 8 → ℝ) : Prop :=
  ∀ j, DBMRow (A j) (bV j) y

/-- **The recorded `energy_lower`, in real units.**  LITERALLY the left-hand side of the
`leafBound_of_check` / `leafBound_of_batch` / `leafBound_of_floorData` conclusions:
line coefficients `qc i` (of the arc `L`), line constants `qd i`, the recorded dual value
`lamBR` (= `λᵀb`) and the recorded residual minimum `rminR` (= `min_q r_q`).
No new mathematics: this only gives the checker's output quantity a name. -/
def energyLower {n : ℕ} (L : ℝ) (qc qd : Fin n → ℚ) (lamBR rminR : ℚ) : ℝ :=
  (∑ i, ((qc i : ℝ) * L + (qd i : ℝ))) - (lamBR : ℝ) + (rminR : ℝ)

/-! ## 2. THE C921 SEMANTIC PREMISE (gap (3), given a name -- NOT discharged here)  -/

/-- **C921 SEMANTIC PREMISE, one energy leaf** (= "GAP CARRIED (gap (3))" of
`G3LeafChecker` / `G3ArcConstants` / `G3Batch_*`, named here, still UNPAID).

For every `y` in the leaf's domain (DBM box ∩ closed simplex), the recorded data's
`energy_lower` is a lower bound of the canonical oracle energy `V2`:

    `∀ y ∈ leafDom ∩ simplex,  V2 y ≥ energyLower L qc qd lamBR rminR`.

CALIBER.  object: one `energy` leaf of the P-tree (the 2386 energy leaves);
units: length² (unit disk radius = 1); `V2` and `energyLower` are both length²;
normalization: `y` in the closed 8-simplex; threshold-free (the threshold enters only
through the checker's strict inequality downstream).

Real-math content hidden inside this premise (to be discharged elsewhere, per layer):
  (a) weak duality `V2 y ≥ E_α y` (SOC dual; normalized nonnegative edge weights α);
  (b) whole-cell affine cos-minorants `1 − cos z ≥ s·z + v`, valid on the WHOLE cell
      (no curvature / local-tangent / sampling premise);
  (c) rational β/γ mixtures of fields and minorants (slopes/weights re-derived against
      exact cell + interval trig);
  (d) the LP step `f0 + c·y ≥ f0 − λᵀb + min_q r_q` from `λ ≥ 0`, `Ay ≤ b`, `y ∈ simplex`.
Layer (d) is pure algebra over the recorded data and is formalizable in Lean as a future
obligation; layers (a)–(c) are source-side analysis.  THIS FILE takes the folded premise
as ONE hypothesis -- that folded form is exactly the interface the checker consumers
need.  The premise is a DEFINITIONAL CHOICE of interface; its truth for the real data is
REAL MATHEMATICS, currently outside the kernel. -/
def LeafSemBound (V2 : (Fin 8 → ℝ) → ℝ) {n m : ℕ} (L : ℝ)
    (qc qd : Fin n → ℚ) (lamBR rminR : ℚ)
    (A : Fin m → Fin 8 → ℚ) (bV : Fin m → ℚ) : Prop :=
  ∀ y : Fin 8 → ℝ, InLeafDom A bV y → InSimplex y → V2 y ≥ energyLower L qc qd lamBR rminR

/-! ## 3. The threshold  -/

/-- The leaf threshold `T` as a real: exactly the cone's `G3ArcConstants.thresh` cast.
Numerically `T = 1899919265599193545242591 / 5·10^24 = 3799838531198387090485182 / 10^25`
(same rational; the doubled form is the source doc's `T`, FULL-P-ORACLE-THEOREM L15). -/
def threshR : ℝ := ((thresh : ℚ) : ℝ)

theorem threshR_pos : (0 : ℝ) < threshR := by
  have h : (0 : ℚ) < thresh := by norm_num [thresh]
  show (0 : ℝ) < ((thresh : ℚ) : ℝ)
  exact_mod_cast h

/-! ## 4. The consumer wiring, LEAF level (proved; every hypothesis displayed)  -/

/-- **Wiring, check form.**  The hypothesis list up to `hsem` is EXACTLY
`leafBound_of_check`'s, one-to-one; the conclusion adds the oracle bound on one `y`.
`T2R` is the threshold slot (`thresh²` in the concrete instantiation below). -/
theorem leafOracleLower_of_check
    {V2 : (Fin 8 → ℝ) → ℝ} {n m : ℕ} {c d : Fin n → ℤ} {b : Fin n → Bool}
    {Llo Lhi D lamB rmin T2 : ℤ} {qc qd : Fin n → ℚ} {lamBR rminR T2R : ℚ} {L : ℝ}
    {A : Fin m → Fin 8 → ℚ} {bV : Fin m → ℚ}
    (h : leafCheck c d b Llo Lhi D lamB rmin T2 = true)
    (hD : 0 < D)
    (hLlo : (Llo : ℝ) / (D : ℝ) ≤ L) (hLhi : L ≤ (Lhi : ℝ) / (D : ℝ))
    (hLlo0 : 0 ≤ (Llo : ℝ) / (D : ℝ))
    (hcR : ∀ i, (c i : ℚ) ≤ qc i * D) (hd : ∀ i, (d i : ℚ) ≤ qd i * D)
    (hlamB : lamBR * D ≤ (lamB : ℚ)) (hrmin : (rmin : ℚ) ≤ rminR * D)
    (hT2 : T2R * D ≤ (T2 : ℚ))
    (hsem : LeafSemBound V2 L qc qd lamBR rminR A bV)
    {y : Fin 8 → ℝ} (hy : InLeafDom A bV y) (hyS : InSimplex y) :
    V2 y > (T2R : ℝ) := by
  have h1 : (T2R : ℝ) < energyLower L qc qd lamBR rminR :=
    leafBound_of_check h hD hLlo hLhi hLlo0 hcR hd hlamB hrmin hT2
  have h2 : energyLower L qc qd lamBR rminR ≤ V2 y := hsem y hy hyS
  exact lt_of_lt_of_le h1 h2

/-- **Wiring, batch form.**  The hypothesis list up to `hsem` is EXACTLY
`leafBound_of_batch`'s, one-to-one -- this is the shape the cone's `G3Batch_*` slices
feed (`ok_<leaf> : leafOK' … = true` + block sums + sign table via
`leafCheck_eq_true_of_sum`). -/
theorem leafOracleLower_of_batch
    {V2 : (Fin 8 → ℝ) → ℝ} {n m : ℕ} {c d : Fin n → ℤ} {b : Fin n → Bool}
    {Llo Lhi D lamB rmin T2 : ℤ} {qc qd : Fin n → ℚ} {lamBR rminR T2R : ℚ} {L : ℝ} (S : ℤ)
    {A : Fin m → Fin 8 → ℚ} {bV : Fin m → ℚ}
    (hD : 0 < D) (hLH : Llo ≤ Lhi) (hs : ∀ i, b i = decide (0 < c i))
    (hsum : lsum c d Llo Lhi D = S) (hcmp : S - lamB * D + rmin * D > T2 * D)
    (hLlo : (Llo : ℝ) / (D : ℝ) ≤ L) (hLhi : L ≤ (Lhi : ℝ) / (D : ℝ))
    (hLlo0 : 0 ≤ (Llo : ℝ) / (D : ℝ))
    (hcR : ∀ i, (c i : ℚ) ≤ qc i * D) (hd : ∀ i, (d i : ℚ) ≤ qd i * D)
    (hlamB : lamBR * D ≤ (lamB : ℚ)) (hrmin : (rmin : ℚ) ≤ rminR * D)
    (hT2 : T2R * D ≤ (T2 : ℚ))
    (hsem : LeafSemBound V2 L qc qd lamBR rminR A bV)
    {y : Fin 8 → ℝ} (hy : InLeafDom A bV y) (hyS : InSimplex y) :
    V2 y > (T2R : ℝ) := by
  have h1 : (T2R : ℝ) < energyLower L qc qd lamBR rminR :=
    leafBound_of_batch S hD hLH hs hsum hcmp hLlo hLhi hLlo0 hcR hd hlamB hrmin hT2
  have h2 : energyLower L qc qd lamBR rminR ≤ V2 y := hsem y hy hyS
  exact lt_of_lt_of_le h1 h2

/-- **Wiring, floor-data form, fully instantiated.**  The single hypothesis is EXACTLY
`leafBound_of_floorData`'s; `L` is pinned to the rooted arc `2·arcsin(19/50)` and the
threshold to `thresh²`.  This is the instantiation future per-leaf data files must feed:
floor/ceil-rounded integers passing the kernel check + the semantic premise ⇒ oracle
bound on the leaf, with NO per-leaf proof work beyond the `decide`. -/
theorem leafOracleLower_of_floorData
    {V2 : (Fin 8 → ℝ) → ℝ} {n m : ℕ} {b : Fin n → Bool} {qc qd : Fin n → ℚ}
    {lamBq rminq : ℚ} {A : Fin m → Fin 8 → ℚ} {bV : Fin m → ℚ}
    (h : leafCheck (fun i => ⌊qc i * (scaleD : ℚ)⌋) (fun i => ⌊qd i * (scaleD : ℚ)⌋) b
            arcLlo arcLhi scaleD ⌈lamBq * (scaleD : ℚ)⌉ ⌊rminq * (scaleD : ℚ)⌋ threshSq
          = true)
    (hsem : LeafSemBound V2 (2 * Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ)) qc qd lamBq rminq
      A bV)
    {y : Fin 8 → ℝ} (hy : InLeafDom A bV y) (hyS : InSimplex y) :
    V2 y > ((thresh : ℚ) : ℝ) ^ 2 := by
  have h1 : ((thresh : ℚ) : ℝ) ^ 2 <
      energyLower (2 * Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ)) qc qd lamBq rminq :=
    leafBound_of_floorData h
  have h2 : energyLower (2 * Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ)) qc qd lamBq rminq
      ≤ V2 y := hsem y hy hyS
  exact lt_of_lt_of_le h1 h2

/-! ## 5. The C921 proposition: checker + premise + P-coverage ⇒ global lower bound  -/

/-- **THE C921 GLOBAL LOWER BOUND (named; conditional form).**

Given a family of energy leaves (`ι` indexes them; the real tree contributes its 2386
`energy` leaves; `n` and `m` may vary per leaf) together with
  * `hsem`   -- the C921 semantic premise on EVERY leaf   (gap (3): named, UNPAID),
  * `hlow`   -- the checker chain concludes `energyLower > T2` on every leaf
               (discharged by `leafBound_of_check` / `_batch` / `_floorData` --
               see §4; `hlow`'s type IS those theorems' conclusion),
  * `hcover` -- every simplex point lies in some leaf's domain (P-coverage: the tree
               partition; UNPAID here.  HONEST SCOPE NOTE: the real tree's 120 LOCAL
               leaves certify a different statement (C919/C920 containment balls) and
               are NOT modeled by this hypothesis; composing them in is a separate,
               explicitly-recorded obligation),
the canonical oracle energy exceeds `T2` on the WHOLE closed simplex. -/
theorem globalOracleLower
    {V2 : (Fin 8 → ℝ) → ℝ} {ι : Type} {n : ι → ℕ} {m : ι → ℕ} (L : ℝ) (T2 : ℝ)
    (qc : ∀ ℓ, Fin (n ℓ) → ℚ) (qd : ∀ ℓ, Fin (n ℓ) → ℚ)
    (lamBR : ι → ℚ) (rminR : ι → ℚ)
    (A : ∀ ℓ, Fin (m ℓ) → Fin 8 → ℚ) (bV : ∀ ℓ, Fin (m ℓ) → ℚ)
    (hsem : ∀ ℓ, LeafSemBound V2 L (qc ℓ) (qd ℓ) (lamBR ℓ) (rminR ℓ) (A ℓ) (bV ℓ))
    (hlow : ∀ ℓ, energyLower L (qc ℓ) (qd ℓ) (lamBR ℓ) (rminR ℓ) > T2)
    (hcover : ∀ y : Fin 8 → ℝ, InSimplex y → ∃ ℓ : ι, InLeafDom (A ℓ) (bV ℓ) y) :
    ∀ y : Fin 8 → ℝ, InSimplex y → V2 y > T2 := by
  intro y hyS
  obtain ⟨ℓ, hℓ⟩ := hcover y hyS
  have h1 : T2 < energyLower L (qc ℓ) (qd ℓ) (lamBR ℓ) (rminR ℓ) := hlow ℓ
  have h2 : energyLower L (qc ℓ) (qd ℓ) (lamBR ℓ) (rminR ℓ) ≤ V2 y := hsem ℓ y hℓ hyS
  exact lt_of_lt_of_le h1 h2

/-- The C921 proposition at the cone's arc and threshold: `L = 2·arcsin(19/50)`,
`T2 = thresh²`.  Specialization of `globalOracleLower`; the slot types are exactly the
ones `leafOracleLower_of_floorData` consumes per leaf. -/
theorem c921_global
    {V2 : (Fin 8 → ℝ) → ℝ} {ι : Type} {n : ι → ℕ} {m : ι → ℕ}
    (qc : ∀ ℓ, Fin (n ℓ) → ℚ) (qd : ∀ ℓ, Fin (n ℓ) → ℚ)
    (lamBR : ι → ℚ) (rminR : ι → ℚ)
    (A : ∀ ℓ, Fin (m ℓ) → Fin 8 → ℚ) (bV : ∀ ℓ, Fin (m ℓ) → ℚ)
    (hsem : ∀ ℓ, LeafSemBound V2 (2 * Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ)) (qc ℓ) (qd ℓ)
      (lamBR ℓ) (rminR ℓ) (A ℓ) (bV ℓ))
    (hlow : ∀ ℓ, energyLower (2 * Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ)) (qc ℓ) (qd ℓ)
      (lamBR ℓ) (rminR ℓ) > ((thresh : ℚ) : ℝ) ^ 2)
    (hcover : ∀ y : Fin 8 → ℝ, InSimplex y → ∃ ℓ : ι, InLeafDom (A ℓ) (bV ℓ) y) :
    ∀ y : Fin 8 → ℝ, InSimplex y → V2 y > ((thresh : ℚ) : ℝ) ^ 2 :=
  globalOracleLower _ _ qc qd lamBR rminR A bV hsem hlow hcover

/-! ## 6. The `hbound` bridge (C921 → consumer), conditional on the two NEIGHBOR slots  -/

/-- Schema pin: any C891 spec whose box-hi at `radiusIndex` is ≤ T has `Rstar ≤ T`.
The NUMERIC comparison `boxHiCert 6 ≤ T` itself is a separate `norm_num` obligation on
the actual certificate box (not discharged here). -/
theorem Rstar_le_thresh_of_box {S : C891RootSpec}
    (hbox : (S.boxHi S.radiusIndex : ℝ) ≤ threshR) : Rstar S ≤ threshR :=
  (Rstar_mem_box S).2.trans hbox

/-- **`hbound` of `n11_main_conditional`, assembled from C921 + its two neighbors.**
  * `hc923` -- the C923 oracle-relaxation slot, ONE direction only, SQUARED form:
    every cover of radius `r` yields a simplex point with `V2 ≤ r²`.  UNPAID (C923 card).
    Squared-form note: the source slot reads `V(U(y)) ≤ r`; the squared form is equivalent
    once the future oracle definition carries `V ≥ 0` (a recorded definitional choice).
  * `hRpin` -- the numeric pin `Rstar S ≤ T` (schema lemma `Rstar_le_thresh_of_box` +
    the box comparison).
  * `hglob` -- the C921 global lower bound (`c921_global`). -/
theorem hbound_of_c921 {S : C891RootSpec} {V2 : (Fin 8 → ℝ) → ℝ}
    (hc923 : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      ∃ y : Fin 8 → ℝ, InSimplex y ∧ V2 y ≤ r ^ 2)
    (hRpin : Rstar S ≤ threshR)
    (hglob : ∀ y : Fin 8 → ℝ, InSimplex y → V2 y > threshR ^ 2)
    (r : ℝ) (c : Fin 11 → Point) (hr : 0 ≤ r) (hcov : Covers c r) :
    Rstar S ≤ r := by
  obtain ⟨y, hyS, hV2y⟩ := hc923 r c hr hcov
  have hkey : threshR ^ 2 < r ^ 2 := lt_of_lt_of_le (hglob y hyS) hV2y
  have hTpos : (0 : ℝ) < threshR := threshR_pos
  have hlt : threshR < r := by
    rcases lt_trichotomy threshR r with hlt' | heq | hgt
    · exact hlt'
    · rw [heq] at hkey
      exact absurd hkey (lt_irrefl (r ^ 2))
    · exfalso
      have hge : r ≤ threshR := le_of_lt hgt
      have hprod : (0 : ℝ) ≤ (threshR - r) * (threshR + r) :=
        mul_nonneg (by linarith) (by linarith)
      have hring : threshR ^ 2 - r ^ 2 = (threshR - r) * (threshR + r) := by ring
      have hle : r ^ 2 ≤ threshR ^ 2 := by
        rw [← sub_nonneg, hring]
        exact hprod
      exact absurd hkey (not_lt.mpr hle)
  exact hRpin.trans (le_of_lt hlt)

/-- **Terminal wiring node**: the conditional main theorem, assembled from the C921 side.
`hattain` is C892's slot (unpaid); the remaining three are exactly `hbound_of_c921`'s. -/
theorem n11_main_of_c921 (S : C891RootSpec) {V2 : (Fin 8 → ℝ) → ℝ}
    (hattain : ∃ c : Fin 11 → Point, Covers c (Rstar S))
    (hc923 : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      ∃ y : Fin 8 → ℝ, InSimplex y ∧ V2 y ≤ r ^ 2)
    (hRpin : Rstar S ≤ threshR)
    (hglob : ∀ y : Fin 8 → ℝ, InSimplex y → V2 y > threshR ^ 2) :
    N11MainStatement (Rstar S) :=
  n11_main_conditional S hattain
    (fun r c hr hc => hbound_of_c921 hc923 hRpin hglob r c hr hc)

end N11Formalization.C921Sem
