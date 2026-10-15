import N11Formalization.FlashTenBoundaryTwoCircle
import N11Formalization.SourceExactRoot

/-!
# DSH-TOPO-C1 — ten-boundary exclusion from an explicit per-segment per-disk certificate

**What this file is.** The ten-boundary exclusion (handoff §2C item 1) is the statement that
*no* complete cover of the closed unit disk has exactly ten boundary disks, at the radius the
project actually paid.  `FlashTenBoundary.not_card_boundaryIdx_eq_ten` already proves this
from the **opaque** whole-configuration `Prop` `C450Atom`.  This file **reduces** that opaque
atom to explicit rational segment data plus one per-segment continuum inequality per segment,
and proves the reduction:

```
TenBoundaryCert            (36 segments: eLo, eHi, 8 rational weights each, per-segment per-disk
                            bound, chain condition "0 → 7/50")
   ⟹  C450Atom
   ⟹  ¬ (Fintype.card (BoundaryIdx c r) = 10)        for  Covers c r,  r ≤ 19/50
   ⟹  ¬ (… = 10)                                      for  Covers c r,  r < SourceExactRoot.sourceRadius
```

**Why the reduction is not circular.** Everything except the per-segment bound is proved here:
the hub-offset geometric reduction (`hub_offset_le`), the two-circle capacity
(`two_circle_capacity`), the "10 disks cannot sum below the capacity" step
(`c450_capacity_contradiction`), the finite-index bookkeeping (`Fin.succAbove`, the chain
coverage lemma), and the bridge to the paid root interval
(`SourceExactRoot.sourceRadius_mem_box` + `boxHiCert_six_lt_R0_real`).  What remains unpaid is
*only* `PerDiskArcBound` on each segment: a single-disk, real-variable inequality containing
no cover, no configuration and no combinatorics.

**Scope label: module/standalone.** Not root-integrated (root imports are lead-only). The
non-hub index enumeration is exactly `Fin 10`; repeated centres, coincident centres and centres
outside the disk are all allowed by `Covers`, and nothing here assumes distinctness, symmetry
or general position.

## The unpaid premise, exactly

```lean
PerDiskArcBound W0 W1 e0 e1 :=
  ∀ c h, 1 - 19/50 ≤ ‖c‖ → ‖c‖ ≤ 1 + 19/50 → e0 ≤ ‖h‖ → ‖h‖ ≤ e1 →
    (∫ θ in (0)..(2π), if dist (angPt θ) c ≤ 19/50 then W0.toFun θ else 0)
  + (∫ θ in (0)..(2π), if dist (h + (19/50) • angPt θ) c ≤ 19/50 then W1.toFun θ else 0)
    < (2π W0.a0 + 2π W1.a0) / 10
```

This is precisely the per-disk hypothesis of `c450_capacity_contradiction`, on the ring-centre
domain `‖c‖ ∈ [1-R, 1+R]` and the hub-offset window `[e0, e1]` of one segment.  The source
certificate (`research-2026/solo-20260922/directional_low_cover.json` +
`directional_e_cover.json`, arithmetic cores A/B) asserts it for 36 consecutive segments whose
exact rational weights and endpoints are recorded in
`evidence/dsh/topology/ten-boundary/segments36.leandata.txt`; discharging those 36 inequalities
in the kernel is the whole remaining task (see NOTES.md §7 for the elimination plan).
-/

set_option autoImplicit false
noncomputable section

namespace N11Formalization

open scoped Interval
open MeasureTheory

/-! ## 1. Two cast helpers (used once, to build `TrigDensity` from rational data) -/

/-- `|·|` commutes with the rational cast. -/
theorem abs_cast_le {q : ℚ} : ((|q| : ℚ) : ℝ) = |(q : ℝ)| := by
  rcases le_total 0 q with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by exact_mod_cast h)]
  · rw [abs_of_nonpos h, abs_of_nonpos (by exact_mod_cast h)]
    simp

/-- Nonnegativity of a third-order cosine density transfers from `ℚ` data to `ℝ`. -/
theorem hnonneg_cast {q1 q2 q3 q0 : ℚ} (h : |q1| + |q2| + |q3| ≤ q0) :
    |(q1 : ℝ)| + |(q2 : ℝ)| + |(q3 : ℝ)| ≤ (q0 : ℝ) := by
  have h' : ((|q1| : ℚ) : ℝ) + ((|q2| : ℚ) : ℝ) + ((|q3| : ℚ) : ℝ) ≤ (q0 : ℝ) := by
    exact_mod_cast h
  rwa [abs_cast_le, abs_cast_le, abs_cast_le] at h'

/-- A disk that meets the unit circle has its centre within `1 + r` of the origin. -/
theorem norm_le_one_add_of_meetsCircle {c : Fin 11 → Point} {r : ℝ} {i : Fin 11}
    (h : MeetsCircle c r i) : ‖c i‖ ≤ 1 + r := by
  obtain ⟨x, hx, hd⟩ := h
  have h1 : ‖c i‖ ≤ dist x (c i) + ‖x‖ := by
    calc ‖c i‖ = ‖c i - x + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖c i - x‖ + ‖x‖ := norm_add_le _ _
      _ = dist x (c i) + ‖x‖ := by rw [dist_eq_norm, norm_sub_rev]
  rw [hx] at h1
  linarith

/-! ## 2. The certificate data (rational, proof-free) and the per-segment per-disk bound -/

/-- One segment of the source certificate: a closed `e`-interval plus the eight exact rational
weights `a0 a1 a2 a3` (outer circle `∂D`) and `b0 b1 b2 b3` (hub circle `S(h,R)`). -/
structure TenSeg where
  eLo : ℚ
  eHi : ℚ
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  b0 : ℚ
  b1 : ℚ
  b2 : ℚ
  b3 : ℚ
deriving DecidableEq, Repr

namespace TenSeg

/-- The outer-circle weight function `W0(θ) = a0 + Σ a_k cos (kθ)` as a `TrigDensity`. -/
def W0 (s : TenSeg) (h : |s.a1| + |s.a2| + |s.a3| ≤ s.a0) : TrigDensity :=
  { a0 := (s.a0 : ℝ), a1 := (s.a1 : ℝ), a2 := (s.a2 : ℝ), a3 := (s.a3 : ℝ)
    hnonneg := hnonneg_cast h }

/-- The hub-circle weight function `W1`. -/
def W1 (s : TenSeg) (h : |s.b1| + |s.b2| + |s.b3| ≤ s.b0) : TrigDensity :=
  { a0 := (s.b0 : ℝ), a1 := (s.b1 : ℝ), a2 := (s.b2 : ℝ), a3 := (s.b3 : ℝ)
    hnonneg := hnonneg_cast h }

end TenSeg

/-- **The unpaid premise, one segment.**  For every ring centre `c` with `‖c‖ ∈ [1-R, 1+R]`
(a disk that meets / covers the unit circle) and every hub centre `h` with `‖h‖ ∈ [e0,e1]`,
the weighted arc contribution of that single disk to the two circles is strictly less than
the per-disk share `B/10` of the total demand `B = 2π(a0+b0)`.

`R = 19/50`.  Quantifiers are the source's; no cover hypothesis, no distinctness, no symmetry. -/
def PerDiskArcBound (W0 W1 : TrigDensity) (e0 e1 : ℝ) : Prop :=
  ∀ (c h : Point), 1 - 19 / 50 ≤ ‖c‖ → ‖c‖ ≤ 1 + 19 / 50 → e0 ≤ ‖h‖ → ‖h‖ ≤ e1 →
    ((∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) c ≤ (19 / 50 : ℝ) then W0.toFun θ else 0))
      + (∫ θ in (0)..(2 * Real.pi),
        (if dist (h + (19 / 50 : ℝ) • angPt θ) c ≤ (19 / 50 : ℝ) then W1.toFun θ else 0)))
    < (2 * Real.pi * W0.a0 + 2 * Real.pi * W1.a0) / 10

/-- The per-segment premise in the shape of the rational data: the nonnegativity of the two
weight functions is a premise (a decidable rational comparison), not a field. -/
def TenSeg.PerDisk : TenSeg → Prop
  | s => ∀ (h1 : |s.a1| + |s.a2| + |s.a3| ≤ s.a0) (h2 : |s.b1| + |s.b2| + |s.b3| ≤ s.b0),
      PerDiskArcBound (s.W0 h1) (s.W1 h2) (s.eLo : ℝ) (s.eHi : ℝ)

/-- Consecutiveness ledger: `Chain x l` chains the segments of `l` starting at `x` and returns
the final right endpoint (`none` as soon as two neighbours are not exactly adjacent). -/
def Chain : ℚ → List TenSeg → Option ℚ
  | x, [] => some x
  | x, s :: rest => if s.eLo = x then Chain s.eHi rest else none

/-- **The certificate.**  `segs` is edge-to-edge from `0` to `7/50`, every weight pair is
nonnegative, and every segment carries its per-disk bound. -/
structure TenBoundaryCert where
  segs : List TenSeg
  chain : Chain 0 segs = some (7 / 50)
  nonneg : ∀ s ∈ segs, |s.a1| + |s.a2| + |s.a3| ≤ s.a0 ∧ |s.b1| + |s.b2| + |s.b3| ≤ s.b0
  bound : ∀ s ∈ segs, s.PerDisk

/-! ## 3. The chain lemma: consecutive segments cover `[0, 7/50]` -/

/-- If `Chain x l = some y` and `l` is nonempty, then every real `e ∈ [x,y]` lies in some
segment of `l`.  This is what makes the "36 closed segments cover `[0,7/50]`" check a finite
rational computation instead of a 36-way case split. -/
theorem exists_seg_of_chain : ∀ (l : List TenSeg) (x y : ℚ), Chain x l = some y → l ≠ [] →
    ∀ e : ℝ, (x : ℝ) ≤ e → e ≤ (y : ℝ) → ∃ s ∈ l, (s.eLo : ℝ) ≤ e ∧ e ≤ (s.eHi : ℝ)
  | [], x, y, h, hne => absurd rfl hne
  | s :: rest, x, y, h, _ => by
    intro e hx hy
    by_cases hs : s.eLo = x
    · rw [Chain, if_pos hs] at h
      by_cases he : e ≤ (s.eHi : ℝ)
      · exact ⟨s, List.mem_cons_self, by simpa [hs] using hx, he⟩
      · push_neg at he
        cases rest with
        | nil =>
          have hy' : y = s.eHi := by
            have hsome : some s.eHi = some y := by simpa [Chain] using h
            exact (Option.some.inj hsome).symm
          have hyR : (y : ℝ) = (s.eHi : ℝ) := by rw [hy']
          exfalso; linarith
        | cons t rest' =>
          obtain ⟨s', hs', hlo', hhi'⟩ :=
            exists_seg_of_chain (t :: rest') s.eHi y h (by simp) e (le_of_lt he) hy
          exact ⟨s', List.mem_cons_of_mem s hs', hlo', hhi'⟩
    · rw [Chain, if_neg hs] at h
      exact absurd h (by simp)

/-- The certificate's segs are nonempty (immediate from the chain reaching `7/50 ≠ 0`). -/
theorem TenBoundaryCert.segs_ne_nil (hcert : TenBoundaryCert) : hcert.segs ≠ [] := by
  intro hnil
  have h := hcert.chain
  rw [hnil] at h
  simp only [Chain] at h
  norm_num at h

/-! ## 4. The reduction: certificate ⟹ `C450Atom` -/

/-- **Main reduction.**  The explicit per-segment per-disk certificate implies the opaque
source atom.  Nothing is assumed beyond the certificate data. -/
theorem c450Atom_of_cert (hcert : TenBoundaryCert) : C450Atom := by
  intro c hub hcov htouch harc
  -- (c) hub offset: `‖c hub‖ ≤ 3R - 1 = 7/50`
  have hhub : ‖c hub‖ ≤ 7 / 50 := hub_offset_le htouch hcov
  have hmem : (‖c hub‖ : ℝ) ≤ (((7 : ℚ) / 50 : ℚ) : ℝ) := by
    have hcast : (((7 : ℚ) / 50 : ℚ) : ℝ) = 7 / 50 := by norm_num
    rw [hcast]; exact hhub
  -- pick the segment containing the hub offset `‖c hub‖`
  obtain ⟨s, hs, hslo, hshi⟩ :=
    exists_seg_of_chain hcert.segs 0 (7 / 50) hcert.chain hcert.segs_ne_nil
      (‖c hub‖) (by push_cast; exact norm_nonneg _) hmem
  obtain ⟨hn1, hn2⟩ := hcert.nonneg s hs
  have hW : PerDiskArcBound (s.W0 hn1) (s.W1 hn2) (s.eLo : ℝ) (s.eHi : ℝ) :=
    hcert.bound s hs hn1 hn2
  -- the ten ring disks, indexed by the complement of `hub` in `Fin 11`
  let ring : Fin 10 → Point := fun j => c (hub.succAbove j)
  have hcovD : ∀ x : Point, ‖x‖ ≤ 1 →
      (∃ j : Fin 10, dist x (ring j) ≤ 19 / 50) ∨ dist x (c hub) ≤ 19 / 50 := by
    intro x hx
    obtain ⟨i, hi⟩ := hcov x hx
    by_cases him : i = hub
    · exact Or.inr (by rw [← him]; exact hi)
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq him
      exact Or.inl ⟨j, by simpa [ring, hj] using hi⟩
  have harcD : ∀ θ : ℝ, ∃ j : Fin 10, dist (angPt θ) (ring j) ≤ 19 / 50 := by
    intro θ
    obtain ⟨i, hine, hi⟩ := harc (angPt θ) (norm_angPt θ)
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hine
    exact ⟨j, by simpa [ring, hj] using hi⟩
  -- (e) the per-disk bound, specialised to each ring disk
  have hper10 : ∀ j : Fin 10,
      ((∫ θ in (0)..(2 * Real.pi),
          (if dist (angPt θ) (ring j) ≤ (19 / 50 : ℝ) then (s.W0 hn1).toFun θ else 0))
        + (∫ θ in (0)..(2 * Real.pi),
          (if dist (c hub + (19 / 50 : ℝ) • angPt θ) (ring j) ≤ (19 / 50 : ℝ)
            then (s.W1 hn2).toFun θ else 0)))
      < (2 * Real.pi * (s.W0 hn1).a0 + 2 * Real.pi * (s.W1 hn2).a0) / 10 := by
    intro j
    have hmeet : MeetsCircle c (19 / 50) (hub.succAbove j) :=
      htouch _ (Fin.succAbove_ne hub j)
    have hlo : 1 - 19 / 50 ≤ ‖ring j‖ := by
      simpa [ring] using one_sub_le_norm_of_meetsCircle hmeet
    have hhi : ‖ring j‖ ≤ 1 + 19 / 50 := by
      simpa [ring] using norm_le_one_add_of_meetsCircle hmeet
    exact hW (ring j) (c hub) hlo hhi hslo hshi
  -- (d)+(f): weighted capacity vs per-disk share
  exact c450_capacity_contradiction (s.W0 hn1) (s.W1 hn2) (by norm_num : 0 < 10)
    (by norm_num : (0 : ℝ) < 19 / 50) (by linarith : ‖c hub‖ + 19 / 50 < 1)
    hcovD harcD hper10

/-! ## 5. Consumer shapes -/

/-- **Ten-boundary exclusion, `r ≤ 19/50` form** (verbatim consumer type of
`not_card_boundaryIdx_eq_ten`, now from the explicit certificate). -/
theorem not_card_boundaryIdx_eq_ten_of_cert (hcert : TenBoundaryCert) {c : Fin 11 → Point}
    {r : ℝ} (hr : r ≤ 19 / 50) (hc : Covers c r) : Fintype.card (BoundaryIdx c r) ≠ 10 :=
  not_card_boundaryIdx_eq_ten (c450Atom_of_cert hcert) hr hc

/-- **Exactly nine boundary disks**, `r < 19/50` form. -/
theorem card_boundaryIdx_eq_nine_of_cert (hcert : TenBoundaryCert) {c : Fin 11 → Point}
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 19 / 50) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) = 9 :=
  card_boundaryIdx_eq_nine_of_c450 (c450Atom_of_cert hcert) hr0 hr hc

/-- **Bridge to the paid source-root interval.**  `r < sourceRadius ≤ boxHiCert 6 < 19/50`,
so any cover below the *actual* frozen source radius is excluded at ten boundary disks.
The enclosure `SourceExactRoot.sourceRadius_mem_box` and the strict margin
`boxHiCert_six_lt_R0_real` are both kernel-proved in the project. -/
theorem not_card_boundaryIdx_eq_ten_of_lt_sourceRadius (hcert : TenBoundaryCert)
    {c : Fin 11 → Point} {r : ℝ} (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) ≠ 10 := by
  have h1 : SourceExactRoot.sourceRadius ≤ ((boxHiCert 6 : ℚ) : ℝ) :=
    SourceExactRoot.sourceRadius_mem_box.2
  have h2 : ((boxHiCert 6 : ℚ) : ℝ) < 19 / 50 := boxHiCert_six_lt_R0_real
  exact not_card_boundaryIdx_eq_ten_of_cert hcert (le_of_lt (lt_of_lt_of_le hr (le_trans h1 h2.le))) hc

/-- **Exactly nine boundary disks at the paid source-root interval** — the consumer shape the
nine-boundary/ownership line needs.  No `0 ≤ r` hypothesis: `Covers.nonneg` supplies it. -/
theorem card_boundaryIdx_eq_nine_of_lt_sourceRadius (hcert : TenBoundaryCert)
    {c : Fin 11 → Point} {r : ℝ} (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) = 9 := by
  have h1 : SourceExactRoot.sourceRadius ≤ ((boxHiCert 6 : ℚ) : ℝ) :=
    SourceExactRoot.sourceRadius_mem_box.2
  have h2 : ((boxHiCert 6 : ℚ) : ℝ) < 19 / 50 := boxHiCert_six_lt_R0_real
  have hlt : r < 19 / 50 := lt_of_lt_of_le hr (le_trans h1 h2.le)
  exact card_boundaryIdx_eq_nine_of_cert hcert (Covers.nonneg hc) hlt hc

end N11Formalization

end

#print axioms N11Formalization.abs_cast_le
#print axioms N11Formalization.hnonneg_cast
#print axioms N11Formalization.norm_le_one_add_of_meetsCircle
#print axioms N11Formalization.exists_seg_of_chain
#print axioms N11Formalization.c450Atom_of_cert
#print axioms N11Formalization.not_card_boundaryIdx_eq_ten_of_cert
#print axioms N11Formalization.card_boundaryIdx_eq_nine_of_cert
#print axioms N11Formalization.not_card_boundaryIdx_eq_ten_of_lt_sourceRadius
#print axioms N11Formalization.card_boundaryIdx_eq_nine_of_lt_sourceRadius

-- full theorem types (verbatim, for the evidence pack); `#print` of proof terms is deliberately
-- avoided here because the elaborated `c450Atom_of_cert` term is enormous.
#check @N11Formalization.c450Atom_of_cert
#check @N11Formalization.not_card_boundaryIdx_eq_ten_of_cert
#check @N11Formalization.card_boundaryIdx_eq_nine_of_cert
#check @N11Formalization.not_card_boundaryIdx_eq_ten_of_lt_sourceRadius
#check @N11Formalization.card_boundaryIdx_eq_nine_of_lt_sourceRadius
#check @N11Formalization.TenBoundaryCert
#check @N11Formalization.PerDiskArcBound
#check @N11Formalization.TenSeg.PerDisk
#check @N11Formalization.Chain
#check @N11Formalization.exists_seg_of_chain
