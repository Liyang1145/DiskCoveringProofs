/-
  ProbeA25AuditTreeEmit.lean   (owner: m5b-adversarial-audit)
  Top-level probe; NOT part of the A25 manifest module list.

  ======================== THE ONE QUESTION ========================
  Can `RationalBoxSubdivision.Certificate.split` MECHANICALLY emit, for a single
  face, a tree whose leaves are closed by a rational comparison — i.e. is the
  1015-tree count a BATCH JOB or a WALL?

  ANSWER: MECHANICAL.  `RationalBoxSubdivision.Certificate` is a `Prop`, so an
  emitter cannot return it inside `Option`; the right design is a COMPUTABLE
  `Bool` leaf test plus a bridge theorem from `true` to the `Prop`.  That is what
  `allOK` / `certificate_of_allOK` below do:

    - `allOK p M d B : Bool` is a plain computable `def` (NO `noncomputable`)
      that recursively tests the rational bound `planeDirectUpperQ p 0 0 C ≤ M`
      on every leaf of a depth-`d` midpoint subdivision, and it CHOOSES the split
      coordinate by comparing rational widths.  Nothing in its dependency chain
      (`RatInterval` arithmetic, `maximumQ`, `sinCell`, `sinTQ`) is
      `noncomputable`.
    - `certificate_of_allOK` bridges a `true` result to a genuine
      `Nonempty (Certificate (DirectPlaneLeaf p 0 0 M) B)`, and `allOK_sound`
      then delivers the real ∀-bound over the whole face domain.

  So a batch job can: evaluate `allOK` at increasing depth, and once it returns
  `true`, obtain a machine-generated tree whose soundness is a proved theorem.

  Convergence RATE is measured numerically, not proved here: the ADAPTIVE
  strategy's leaf count grows like `10.2 / excess` (see `tree_adaptive3.log`),
  i.e. O(1/excess) — linear, matching the gradient bound's Lipschitz structure.

  ===================== WHAT THIS DOES NOT SAY =====================
  It does NOT produce a finished class certificate and pays ZERO class credit.
  At the accuracy a real class needs (~0.0026 of slack per factor) the
  extrapolated leaf count is ~3900 per factor and ~3.9e6 across the 1015 factors
  of `SevenFiniteTables`.  Whether that many `Certificate.split` nodes can be
  ELABORATED within the project's heartbeat budget is NOT tested here and remains
  the open risk.  The mechanism question is settled; the budget question is not.
-/
import N11Formalization.SharedMomentFacePlaneDirectCertificate
import N11Formalization.SharedMomentConcreteFace1Data

set_option autoImplicit false
namespace N11Formalization.ProbeA25AuditTreeEmit

open RationalBoxSubdivision SharedMomentFacePlaneDirectCertificate
open SharedMomentFacePlaneCertificate SharedMomentConcreteFace1

/-- A disambiguating alias for the subdivision midpoint: the bare name `midpoint`
is exported both at the root and inside `RationalBoxSubdivision`, so proofs must
not use it unqualified. -/
private abbrev mid2 {I : Type*} (B : Cell I) (i : I) : ℚ := RationalBoxSubdivision.midpoint B i

/-! ## 1. The leaf predicate, and the semantic bridge -/

/-- The leaf we emit against: the DIRECT bound suffices for `q = b = 0`. -/
def LeafOK (p : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2)) : Prop :=
  planeDirectUpperQ p 0 0 B ≤ M

instance (p : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2)) : Decidable (LeafOK p M B) :=
  inferInstanceAs (Decidable (planeDirectUpperQ p 0 0 B ≤ M))

/-- An emitted accept is a legitimate `DirectPlaneLeaf`. -/
theorem leafOK_direct {p : Fin 3 → ℚ} {M : ℚ} {B : Cell (Fin 2)}
    (h : LeafOK p M B) : DirectPlaneLeaf p 0 0 M B := Or.inr h

/-- The leaf test is monotone in the target `M`: a bound valid at `M` stays valid
at any larger `M`.  A batch run may therefore tighten a bound afterwards without
regenerating the tree. -/
theorem leafOK_mono {p : Fin 3 → ℚ} {M M' : ℚ} {B : Cell (Fin 2)}
    (h : LeafOK p M B) (hMM : M ≤ M') : LeafOK p M' B := le_trans h hMM

/-! ## 2. The emitter: a computable `Bool` test -/

/-- The coordinate to split: the one with the larger rational width. -/
def splitCoord (B : Cell (Fin 2)) : Fin 2 :=
  if (B 1).hi - (B 1).lo ≤ (B 0).hi - (B 0).lo then 0 else 1

/-- Does every leaf of a depth-`d` midpoint subdivision pass the rational test?
Computable, and the split coordinate is chosen by a rational comparison. -/
def allOK (p : Fin 3 → ℚ) (M : ℚ) : (d : ℕ) → Cell (Fin 2) → Bool
  | 0, B => decide (LeafOK p M B)
  | d + 1, B =>
      if decide (LeafOK p M B) then true
      else
        let i := splitCoord B
        let t := RationalBoxSubdivision.midpoint B i
        allOK p M d (leftChild B i t) && allOK p M d (rightChild B i t)

/-! ## 3. The bridge: `allOK = true` gives a real `Certificate` -/

/-- **The bridge.**  A `true` result at depth `d` yields a genuine subdivision
certificate.  This is what turns the computable test into a usable tree. -/
theorem certificate_of_allOK {p : Fin 3 → ℚ} {M : ℚ} :
    ∀ (d : ℕ) (B : Cell (Fin 2)) (hB : ∀ i, (B i).lo ≤ (B i).hi),
      allOK p M d B = true →
        Nonempty (Certificate (DirectPlaneLeaf p 0 0 M) B) := by
  intro d
  induction d with
  | zero =>
      intro B hB h
      have hleaf : LeafOK p M B := of_decide_eq_true h
      exact ⟨Certificate.accept (leafOK_direct hleaf)⟩
  | succ d ih =>
      intro B hB h
      by_cases hleaf : LeafOK p M B
      · exact ⟨Certificate.accept (leafOK_direct hleaf)⟩
      · -- the root fails, so both children must pass
        have hdec : decide (LeafOK p M B) = false := decide_eq_false hleaf
        simp only [allOK, hdec, Bool.false_eq_true, if_false] at h
        have hL : allOK p M d (leftChild B (splitCoord B) (RationalBoxSubdivision.midpoint B (splitCoord B))) = true :=
          (Bool.and_eq_true_iff.mp h).1
        have hR : allOK p M d (rightChild B (splitCoord B) (RationalBoxSubdivision.midpoint B (splitCoord B))) = true :=
          (Bool.and_eq_true_iff.mp h).2
        have hlo : (B (splitCoord B)).lo ≤ RationalBoxSubdivision.midpoint B (splitCoord B) := by
          have hh := hB (splitCoord B)
          unfold RationalBoxSubdivision.midpoint
          linarith
        have hhi : RationalBoxSubdivision.midpoint B (splitCoord B) ≤ (B (splitCoord B)).hi := by
          have hh := hB (splitCoord B)
          unfold RationalBoxSubdivision.midpoint
          linarith
        obtain ⟨L⟩ := ih (leftChild B (splitCoord B) (RationalBoxSubdivision.midpoint B (splitCoord B)))
          (by
            intro j
            by_cases hj : j = splitCoord B
            · subst hj
              simpa only [leftChild, Function.update_self] using hlo
            · simpa only [leftChild, Function.update_of_ne hj] using hB j) hL
        obtain ⟨R⟩ := ih (rightChild B (splitCoord B) (RationalBoxSubdivision.midpoint B (splitCoord B)))
          (by
            intro j
            by_cases hj : j = splitCoord B
            · subst hj
              simpa only [rightChild, Function.update_self] using hhi
            · simpa only [rightChild, Function.update_of_ne hj] using hB j) hR
        exact ⟨Certificate.split (splitCoord B) (RationalBoxSubdivision.midpoint B (splitCoord B)) hlo hhi L R⟩

/-! ## 4. Soundness of an emitted tree -/

/-- **Soundness.**  Any machine-generated tree bounds the objective over the whole
admissible face domain, by the proved chain `certificate_sound` →
`direct_plane_leaf_sound` → `plane_upper_of_direct_certificate`.

The coefficient functions are the zero function `0 : Fin 3 → ℚ`, which is what
`emit`'s leaf predicate uses (`planeDirectUpperQ p 0 0 B`). -/
theorem emit_sound {p : Fin 3 → ℚ} {M : ℚ} {B : Cell (Fin 2)}
    (hB : ∀ i, (B i).lo ≤ 0 ∧ RatInterval.piHi ≤ (B i).hi)
    (T : Certificate (DirectPlaneLeaf p 0 0 M) B) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s) = Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      SharedMomentFactorGridCertificate.faceObjective (fun s => (p s : ℝ))
        (fun s => ((0 : Fin 3 → ℚ) s : ℝ)) (fun s => ((0 : Fin 3 → ℚ) s : ℝ)) a y
        ≤ (M : ℝ) :=
  face_upper_of_direct_plane_tree p 0 0 M B hB T

/-- Corollary: an emitted tree at a passing depth really bounds the objective. -/
theorem allOK_sound {p : Fin 3 → ℚ} {M : ℚ} {B : Cell (Fin 2)}
    (hB : ∀ i, (B i).lo ≤ 0 ∧ RatInterval.piHi ≤ (B i).hi)
    {d : ℕ} (h : allOK p M d B = true) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s) = Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      SharedMomentFactorGridCertificate.faceObjective (fun s => (p s : ℝ))
        (fun s => ((0 : Fin 3 → ℚ) s : ℝ)) (fun s => ((0 : Fin 3 → ℚ) s : ℝ)) a y
        ≤ (M : ℝ) := by
  have hvalid : ∀ i, (B i).lo ≤ (B i).hi := by
    intro i
    have h1 := (hB i).1
    have h2 := (hB i).2
    have h3 : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    linarith
  obtain ⟨T⟩ := certificate_of_allOK d B hvalid h
  exact emit_sound hB T

/-! ## 5. Behaviour at depth 0 (the failure mode, exactly characterized) -/

/-- At depth 0 the test passes exactly when the root bound already suffices. -/
theorem allOK_zero (p : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2)) :
    allOK p M 0 B = true ↔ LeafOK p M B := by
  simp only [allOK, decide_eq_true_eq]

end N11Formalization.ProbeA25AuditTreeEmit

#print axioms N11Formalization.ProbeA25AuditTreeEmit.leafOK_direct
#print axioms N11Formalization.ProbeA25AuditTreeEmit.leafOK_mono
#print axioms N11Formalization.ProbeA25AuditTreeEmit.certificate_of_allOK
#print axioms N11Formalization.ProbeA25AuditTreeEmit.emit_sound
#print axioms N11Formalization.ProbeA25AuditTreeEmit.allOK_sound
#print axioms N11Formalization.ProbeA25AuditTreeEmit.allOK_zero
