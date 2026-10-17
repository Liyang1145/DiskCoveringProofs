import Mathlib
import N11Formalization.TCSystem
import N11Formalization.SourceIdentity
import N11Formalization.ResumeNetwork
import N11Formalization.ResumeLocalIncidence
import N11Formalization.ResumeAnchorAngles
import N11Formalization.FlashBoundaryCapsFaces
import N11Formalization.FlashSlackConsumer
import N11Formalization.RootRangeBoxFull
import N11Formalization.Conditional.RootSpec

/-!
# FlashRootNetwork - the ORIGINAL C891 candidate: canonical 51-edge feasibility

INDEPENDENT NEW FILE.  Scope: the original candidate configuration `u` (the TC root box point)
and its canonical fixed-switch SOC network.  It does NOT assume anything about an arbitrary
cover (that is the cover-reduction line).

## Indexing (lead-pinned; verified in the root)

`ResumeLocalIncidence.siteMap k = k - 2` and `faceMap = ![9,10,8,0,1,2,3,4,6]` with
`faceMap_exact : forall f v, ResumeGlobal.rawToCanon (sourceFaces f v) = face (faceMap f) v`,
`edgeMap_injective`, `edgeMap_image` (canonical faces 5 and 7 are the two absent ones) all
proved there.  So raw ring k <-> canonical ring k - 2, hubs 9/10 fixed, and the row-by-row
raw-face <-> canon-face table is

    raw 0 [2,9,10] -> canon 9  [0,9,10]      raw 5 [4,5,9]  -> canon 2 [2,3,9]
    raw 1 [6,9,10] -> canon 10 [4,9,10]      raw 6 [5,6,9]  -> canon 3 [3,4,9]
    raw 2 [1,2,10] -> canon 8  [8,0,10]      raw 7 [6,7,10] -> canon 4 [4,5,10]
    raw 3 [2,3,9]  -> canon 0  [0,1,9]       raw 8 [8,0,10] -> canon 6 [6,7,10]
    raw 4 [3,4,9]  -> canon 1  [1,2,9]       canonical 5 [5,6,10], 7 [7,8,10]: ABSENT (slack)

(`ResumeNetwork.face = !![0,1,9],[1,2,9],[2,3,9],[3,4,9],[4,5,10],[5,6,10],[6,7,10],[7,8,10],
[8,0,10],[0,9,10],[4,9,10]`.)  The two central canonical faces 9, 10 are the RAW faces
0, 1 = [2,9,10], [6,9,10] -- active central incidences, NOT the absent 5/7.

## Route

Consumer = `ResumeNetwork.oracle_le_of_geometric_witnesses`; the bridge from raw geometry to the
canonical edge list is the root's `ResumeLocalIncidence.sourceLength_eq` (with
`edgeMap`/`faceMap_exact`).  So the boundary inequalities are proved on the RAW `sourceLength`,
where the geometry is `|arcEnd u k - ringCenter u k|` and `|arcEnd u k - ringCenter u (k+1)|`.

## In this file

* algebraic helpers `rho_sq_identity`, `dist_sq_expand`;
* `dist_arcEnd_ringCenter_self` (9), `..._succ` (8), `..._wrap` (1) = **all 18 raw boundary
  distances**, equality `= u 6`;
* `sourceLength_boundary` : the raw 18 boundary inequalities `<= u 6` -- i.e. the `hboundary`
  content in RAW indexing.

NOT here: the 33 face edges (witnesses `Z`), and the final canonical instantiation.
-/

namespace N11Formalization.FlashRootNetwork

open N11Formalization

theorem arcEnd_ofLp_0 (u : Fin 12 → ℝ) (k : Fin 9) :
    (arcEnd u k).ofLp 0 = Real.cos (thetaOf (angleVec u) k + angleVec u k) := rfl

theorem arcEnd_ofLp_1 (u : Fin 12 → ℝ) (k : Fin 9) :
    (arcEnd u k).ofLp 1 = Real.sin (thetaOf (angleVec u) k + angleVec u k) := rfl

theorem ringCenter_ofLp_0 (u : Fin 12 → ℝ) (k : Fin 9) :
    (ringCenter u k).ofLp 0 = rhoK u k * Real.cos (thetaOf (angleVec u) k) := rfl

theorem ringCenter_ofLp_1 (u : Fin 12 → ℝ) (k : Fin 9) :
    (ringCenter u k).ofLp 1 = rhoK u k * Real.sin (thetaOf (angleVec u) k) := rfl

/-- The zero anchor angle: `theta_0 = a_0 - pi`. -/
theorem thetaOf_zero_eq (u : Fin 12 → ℝ) : thetaOf (angleVec u) 0 = angleVec u 0 - Real.pi := by
  unfold thetaOf angleVec
  simp
  ring

/-- Palindromic antisymmetry: `theta_8 = -theta_0`. -/
theorem thetaOf_eight_eq (u : Fin 12 → ℝ) :
    thetaOf (angleVec u) 8 = -(thetaOf (angleVec u) 0) := by
  unfold thetaOf angleVec
  simp
  ring

/-- Radius identity: `rho^2 - 2 rho cos a + 1 = R^2` for `rho = cos a - sqrt (R^2 - sin^2 a)`. -/
theorem rho_sq_identity {a R : ℝ} (hsnn : 0 ≤ R ^ 2 - Real.sin a ^ 2) :
    (Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) ^ 2
      - 2 * (Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) * Real.cos a + 1 = R ^ 2 := by
  have hs2 : Real.sqrt (R ^ 2 - Real.sin a ^ 2) ^ 2 = R ^ 2 - Real.sin a ^ 2 :=
    Real.sq_sqrt hsnn
  have htrig : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  nlinarith [hs2, htrig]

/-- Law-of-cosines expansion. -/
theorem dist_sq_expand (alpha beta ρ : ℝ) :
    (Real.cos alpha - ρ * Real.cos beta) ^ 2 + (Real.sin alpha - ρ * Real.sin beta) ^ 2
      = 1 + ρ ^ 2 - 2 * ρ * Real.cos (alpha - beta) := by
  have h1 : Real.sin alpha ^ 2 + Real.cos alpha ^ 2 = 1 := Real.sin_sq_add_cos_sq alpha
  have h2 : Real.sin beta ^ 2 + Real.cos beta ^ 2 = 1 := Real.sin_sq_add_cos_sq beta
  have h3 : Real.cos (alpha - beta) = Real.cos alpha * Real.cos beta
      + Real.sin alpha * Real.sin beta := Real.cos_sub alpha beta
  rw [h3]
  nlinarith [h1, h2]

/-- First arcEnd distance: `|arcEnd u k - ringCenter u k| = u 6` (9 cases). -/
theorem dist_arcEnd_ringCenter_self (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) (k : Fin 9) :
    dist (arcEnd u k) (ringCenter u k) = u 6 := by
  have hsnn : 0 ≤ (u 6) ^ 2 - Real.sin (angleVec u k) ^ 2 := by
    have := hsin k; linarith
  have hkey : rhoK u k ^ 2 - 2 * rhoK u k * Real.cos (angleVec u k) + 1 = (u 6) ^ 2 :=
    rho_sq_identity hsnn
  have hexp : (Real.cos (thetaOf (angleVec u) k + angleVec u k)
        - rhoK u k * Real.cos (thetaOf (angleVec u) k)) ^ 2
      + (Real.sin (thetaOf (angleVec u) k + angleVec u k)
        - rhoK u k * Real.sin (thetaOf (angleVec u) k)) ^ 2 = (u 6) ^ 2 := by
    have h := dist_sq_expand (thetaOf (angleVec u) k + angleVec u k)
      (thetaOf (angleVec u) k) (rhoK u k)
    rw [show thetaOf (angleVec u) k + angleVec u k - thetaOf (angleVec u) k
        = angleVec u k from by ring] at h
    linarith [h, hkey]
  rw [dist_point_eq_sqrt, arcEnd_ofLp_0, arcEnd_ofLp_1, ringCenter_ofLp_0, ringCenter_ofLp_1,
    hexp]
  exact Real.sqrt_sq hR

/-- Second arcEnd distance (non-wrapping `k = 0..7`):
`|arcEnd u k - ringCenter u (k+1)| = u 6`; angle difference `a_{k+1}` by `thetaOf_rec`. -/
theorem dist_arcEnd_ringCenter_succ (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) (k : Fin 8) :
    dist (arcEnd u ⟨(k : ℕ), by omega⟩)
      (ringCenter u ⟨(k : ℕ) + 1, by omega⟩) = u 6 := by
  have hsnn : 0 ≤ (u 6) ^ 2 - Real.sin (angleVec u ⟨(k : ℕ) + 1, by omega⟩) ^ 2 := by
    have := hsin ⟨(k : ℕ) + 1, by omega⟩; linarith
  have hkey : rhoK u ⟨(k : ℕ) + 1, by omega⟩ ^ 2
      - 2 * rhoK u ⟨(k : ℕ) + 1, by omega⟩
        * Real.cos (angleVec u ⟨(k : ℕ) + 1, by omega⟩) + 1 = (u 6) ^ 2 :=
    rho_sq_identity hsnn
  have hrec := thetaOf_rec (angleVec u) k
  have hangle : thetaOf (angleVec u) ⟨(k : ℕ) + 1, by omega⟩
      - (thetaOf (angleVec u) ⟨(k : ℕ), by omega⟩
          + angleVec u ⟨(k : ℕ), by omega⟩)
      = angleVec u ⟨(k : ℕ) + 1, by omega⟩ := by
    linarith
  have hexp : (Real.cos (thetaOf (angleVec u) ⟨(k : ℕ), by omega⟩
          + angleVec u ⟨(k : ℕ), by omega⟩)
        - rhoK u ⟨(k : ℕ) + 1, by omega⟩
          * Real.cos (thetaOf (angleVec u) ⟨(k : ℕ) + 1, by omega⟩)) ^ 2
      + (Real.sin (thetaOf (angleVec u) ⟨(k : ℕ), by omega⟩
          + angleVec u ⟨(k : ℕ), by omega⟩)
        - rhoK u ⟨(k : ℕ) + 1, by omega⟩
          * Real.sin (thetaOf (angleVec u) ⟨(k : ℕ) + 1, by omega⟩)) ^ 2
      = (u 6) ^ 2 := by
    have h := dist_sq_expand (thetaOf (angleVec u) ⟨(k : ℕ), by omega⟩
        + angleVec u ⟨(k : ℕ), by omega⟩)
      (thetaOf (angleVec u) ⟨(k : ℕ) + 1, by omega⟩)
      (rhoK u ⟨(k : ℕ) + 1, by omega⟩)
    have hcos' : Real.cos (thetaOf (angleVec u) ⟨(k : ℕ), by omega⟩
          + angleVec u ⟨(k : ℕ), by omega⟩
          - thetaOf (angleVec u) ⟨(k : ℕ) + 1, by omega⟩)
        = Real.cos (angleVec u ⟨(k : ℕ) + 1, by omega⟩) := by
      rw [show thetaOf (angleVec u) ⟨(k : ℕ), by omega⟩
            + angleVec u ⟨(k : ℕ), by omega⟩
            - thetaOf (angleVec u) ⟨(k : ℕ) + 1, by omega⟩
          = -(angleVec u ⟨(k : ℕ) + 1, by omega⟩) from by linarith [hangle]]
      exact Real.cos_neg _
    rw [hcos'] at h
    linarith [h, hkey]
  rw [dist_point_eq_sqrt, arcEnd_ofLp_0, arcEnd_ofLp_1, ringCenter_ofLp_0, ringCenter_ofLp_1,
    hexp]
  exact Real.sqrt_sq hR

/-- Wrapping arcEnd distance `k = 8`: `|arcEnd u 8 - ringCenter u 0| = u 6`. -/
theorem dist_arcEnd_ringCenter_wrap (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) :
    dist (arcEnd u 8) (ringCenter u 0) = u 6 := by
  have h8 : thetaOf (angleVec u) 8 + angleVec u 8 - thetaOf (angleVec u) 0
      = 2 * Real.pi - angleVec u 0 := by
    have h0 := thetaOf_zero_eq u
    have h8' := thetaOf_eight_eq u
    have h8a : angleVec u 8 = angleVec u 0 := rfl
    linarith
  have hcos : Real.cos (thetaOf (angleVec u) 8 + angleVec u 8 - thetaOf (angleVec u) 0)
      = Real.cos (angleVec u 0) := by
    rw [h8, Real.cos_two_pi_sub]
  have hsnn : 0 ≤ (u 6) ^ 2 - Real.sin (angleVec u 0) ^ 2 := by
    have := hsin 0; linarith
  have hkey : rhoK u 0 ^ 2 - 2 * rhoK u 0 * Real.cos (angleVec u 0) + 1 = (u 6) ^ 2 :=
    rho_sq_identity hsnn
  have hexp : (Real.cos (thetaOf (angleVec u) 8 + angleVec u 8)
        - rhoK u 0 * Real.cos (thetaOf (angleVec u) 0)) ^ 2
      + (Real.sin (thetaOf (angleVec u) 8 + angleVec u 8)
        - rhoK u 0 * Real.sin (thetaOf (angleVec u) 0)) ^ 2 = (u 6) ^ 2 := by
    have h := dist_sq_expand (thetaOf (angleVec u) 8 + angleVec u 8)
      (thetaOf (angleVec u) 0) (rhoK u 0)
    rw [hcos] at h
    linarith [h, hkey]
  rw [dist_point_eq_sqrt, arcEnd_ofLp_0, arcEnd_ofLp_1, ringCenter_ofLp_0, ringCenter_ofLp_1,
    hexp]
  exact Real.sqrt_sq hR

/-- Side 0 of the raw boundary edge at switch k: the site is site k. -/
theorem sourceLength_boundary_side0 (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6)
    (Z : Fin 9 → Point) (k : Fin 9) :
    ResumeLocalIncidence.sourceLength (arcEnd u) (centersOfRoot u) Z (.inl (k, 0)) ≤ u 6 := by
  have h := dist_arcEnd_ringCenter_self u hsin hR k
  have hifs : (if True then k else k + 1) = k := by simp
  have hC : centersOfRoot u ⟨(k : ℕ), by omega⟩ = ringCenter u k := centersOfRoot_ring u k
  simp only [ResumeLocalIncidence.sourceLength, hifs, hC, dist_comm]
  exact le_of_eq h

/-- Side 1 of the raw boundary edge at switch k: the site is site k+1 (mod 9). -/
theorem sourceLength_boundary_side1 (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6)
    (Z : Fin 9 → Point) (k : Fin 9) :
    ResumeLocalIncidence.sourceLength (arcEnd u) (centersOfRoot u) Z (.inl (k, 1)) ≤ u 6 := by
  obtain ⟨kn, hk⟩ := k
  by_cases hk8 : kn + 1 < 9
  · have h := dist_arcEnd_ringCenter_succ u hsin hR ⟨kn, by omega⟩
    have hifs : (if ((1 : Fin 2) = 0) then (⟨kn, hk⟩ : Fin 9) else (⟨kn, hk⟩ : Fin 9) + 1)
        = ⟨kn + 1, hk8⟩ := by
      rw [if_neg (show ¬ ((1 : Fin 2) = 0) from by decide)]
      ext
      simp only [Fin.val_add]
      exact Nat.mod_eq_of_lt hk8
    have hC : centersOfRoot u ⟨kn + 1, by omega⟩ = ringCenter u (⟨kn + 1, hk8⟩ : Fin 9) :=
      centersOfRoot_ring u (⟨kn + 1, hk8⟩ : Fin 9)
    simp only [ResumeLocalIncidence.sourceLength, hifs, hC, dist_comm]
    exact le_of_eq h
  · have hk9 : kn = 8 := by omega
    subst hk9
    have h := dist_arcEnd_ringCenter_wrap u hsin hR
    have hifs : (if ((1 : Fin 2) = 0) then (⟨8, hk⟩ : Fin 9) else (⟨8, hk⟩ : Fin 9) + 1)
        = (0 : Fin 9) := by
      rw [if_neg (show ¬ ((1 : Fin 2) = 0) from by decide)]
      ext
      simp only [Fin.val_add]
      decide
    have hC : centersOfRoot u (0 : Fin 11) = ringCenter u (0 : Fin 9) := centersOfRoot_ring u (0 : Fin 9)
    simp only [ResumeLocalIncidence.sourceLength, hifs, hC, dist_comm]
    exact le_of_eq h

/-- **All 18 raw boundary (site-switch) edges** are <= u 6: the `hboundary` content in RAW
indexing, ready for `ResumeLocalIncidence.sourceLength_eq`. -/
theorem sourceLength_boundary (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6)
    (Z : Fin 9 → Point) (k : Fin 9) (s : Fin 2) :
    ResumeLocalIncidence.sourceLength (arcEnd u) (centersOfRoot u) Z (.inl (k, s)) ≤ u 6 := by
  fin_cases s
  · exact sourceLength_boundary_side0 u hsin hR Z k
  · exact sourceLength_boundary_side1 u hsin hR Z k

/-! ## The 33 canonical face edges

FaceCoverable (FlashBoundaryCapsFaces) is the EXISTENCE form
xists O, dist (centersOfRoot u i1) O <= u 6 and dist (centersOfRoot u i2) O <= u 6 and
 dist (centersOfRoot u i3) O <= u 6 -- i.e. a common centre for the three vertex disks, which is
exactly the per-face primal content of the 51-edge network (NOT hull covering; the hull statement
covers_of_triangulation is a different consumer).  So a per-face witness can simply be chosen,
and aceOK_table supplies all 11 faces from InCertBox u, 
esidual u = 0 and the single
face-0 input hF0.
-/

/-- The canonical ring shift: canonical label j < 9 has geometry point raw C_(j+2)
(raw ring k <-> canonical k-2, hubs 9/10 fixed). -/
def rawOf : Fin 11 → Fin 11 := ![2, 3, 4, 5, 6, 7, 8, 0, 1, 9, 10]

/-- Canonical face f is the image of the aceOK_table raw face aceRaw f. -/
def faceRaw : Fin 11 → Fin 11 := ![2, 3, 4, 5, 6, 7, 8, 0, 1, 9, 10]

/-- 
awOf is a left inverse of 
awToCanon on the 11 labels. -/
theorem rawOf_rawToCanon (j : Fin 11) : rawOf (ResumeGlobal.rawToCanon j) = j := by
  fin_cases j <;> decide

/-- The v-th raw vertex of canonical face f (raw TC labels, FlashBoundaryCapsFaces.faceI1/2/3). -/
def rawVtx (f : Fin 11) (v : Fin 3) : Fin 11 :=
  match v with
  | ⟨0, _⟩ => FlashBoundaryCapsFaces.faceI1 (faceRaw f)
  | ⟨1, _⟩ => FlashBoundaryCapsFaces.faceI2 (faceRaw f)
  | _ => FlashBoundaryCapsFaces.faceI3 (faceRaw f)

/-- **The face bridge**: each canonical vertex label is the 
awToCanon image of the matching
raw vertex.  Verified over all 33 incidences. -/
theorem face_eq_rawToCanon (f : Fin 11) (v : Fin 3) :
    ResumeNetwork.face f v = ResumeGlobal.rawToCanon (rawVtx f v) := by
  fin_cases f <;> fin_cases v <;> decide

/-- The canonical centre function: canonical label j has geometry point raw 
awOf j. -/
noncomputable def canonCenters (u : Fin 12 → ℝ) : Fin 11 → Point := fun j => centersOfRoot u (rawOf j)

/-- **The 33 canonical face edges**, with the witness chosen per face from aceOK_table.
Primal content; no dual (zero-stress) input is used. -/
theorem exists_face_witnesses (u : Fin 12 → ℝ)
    (hu : RootRangeBoxFull.InCertBox u) (hres : residual u = 0)
    (hF0 : FlashBoundaryCapsFaces.FaceCoverable u ⟨0, by omega⟩ ⟨1, by omega⟩ 10) :
    ∃ Z : Fin 11 → Point, ∀ (f : Fin 11) (v : Fin 3),
      dist (canonCenters u (ResumeNetwork.face f v)) (Z f) ≤ u 6 := by
  classical
  refine ⟨fun f => Classical.choose (FlashBoundaryCapsFaces.faceOK_table u hu hres hF0 (faceRaw f)), ?_⟩
  intro f v
  have hspec := Classical.choose_spec (FlashBoundaryCapsFaces.faceOK_table u hu hres hF0 (faceRaw f))
  rw [face_eq_rawToCanon f v, show canonCenters u (ResumeGlobal.rawToCanon (rawVtx f v))
      = centersOfRoot u (rawVtx f v) from by
    simp only [canonCenters]
    rw [rawOf_rawToCanon]]
  fin_cases v
  · exact hspec.1
  · exact hspec.2.1
  · exact hspec.2.2

/-! ## Structural transport: raw source edges -> canonical edges (Option B)

Rather than re-deriving the canonical boundary inequalities by unfolding `centersOfRoot`, this uses
the root's own reindexing bridge `ResumeLocalIncidence.sourceLength_eq`:

    sourceLength U C Z e = edgeLength Uc Cc Zc (edgeMap e)

given the three identity hypotheses `hU : forall k, Uc (siteMap k) = U k`,
`hC : forall j, Cc (rawToCanon j) = C j`, `hZ : forall f, Zc (faceMap f) = Z f`.

Everything below is pure `Fin` bookkeeping; no `fin_cases` runs over a trigonometric term.
-/

/-- Canonical ring shift on RING labels only (Fin 9 -> Fin 9). -/
def rawOfRing (j : Fin 9) : Fin 9 := ⟨(j.val + 2) % 9, by omega⟩

/-- Canonical anchors: canonical anchor j is raw arcEnd (j + 2). -/
noncomputable def canonAnchors (u : Fin 12 → ℝ) : Fin 9 → Point :=
  fun j => arcEnd u (rawOfRing j)

/-- `hU`: the canonical anchor at canonical label `siteMap k` is raw `arcEnd u k`. -/
theorem hU_siteMap (u : Fin 12 → ℝ) (k : Fin 9) :
    canonAnchors u (ResumeLocalIncidence.siteMap k) = arcEnd u k := by
  fin_cases k <;> rfl

/-- `hC`: the canonical centre at canonical label `rawToCanon j` is raw site `j`. -/
theorem hC_rawToCanon (u : Fin 12 → ℝ) (j : Fin 11) :
    canonCenters u (ResumeGlobal.rawToCanon j) = centersOfRoot u j := by
  rw [canonCenters, rawOf_rawToCanon]

/-- **The transport equality**, one statement for ALL source edges. -/
theorem edgeLength_edgeMap_eq_sourceLength (u : Fin 12 → ℝ) (Zc : Fin 11 → Point)
    (e : ResumeLocalIncidence.SourceEdge) :
    ResumeNetwork.edgeLength (canonAnchors u) (canonCenters u) Zc
        (ResumeLocalIncidence.edgeMap e)
      = ResumeLocalIncidence.sourceLength (arcEnd u) (centersOfRoot u)
          (fun f => Zc (ResumeLocalIncidence.faceMap f)) e :=
  (ResumeLocalIncidence.sourceLength_eq (arcEnd u) (canonAnchors u) (centersOfRoot u)
    (canonCenters u) Zc (fun f => Zc (ResumeLocalIncidence.faceMap f))
    (hU_siteMap u) (hC_rawToCanon u) (fun _ => rfl) e).symm

/-- Preimage of the canonical boundary edge `(i, side = 0)`. -/
theorem edgeMap_preimage_zero (i : Fin 9) :
    ResumeLocalIncidence.edgeMap (Sum.inl (i + 1, (⟨1, by decide⟩ : Fin 2)))
      = Sum.inl (i, (⟨0, by decide⟩ : Fin 2)) := by
  fin_cases i <;> rfl

/-- Preimage of the canonical boundary edge `(i, side = 1)`. -/
theorem edgeMap_preimage_one (i : Fin 9) :
    ResumeLocalIncidence.edgeMap (Sum.inl (i + 2, (⟨0, by decide⟩ : Fin 2)))
      = Sum.inl (i, (⟨1, by decide⟩ : Fin 2)) := by
  fin_cases i <;> rfl

/-- **The canonical boundary edges, by structural transport** (Option B): the `hboundary` half of
`ResumeNetwork.oracle_le_of_geometric_witnesses` in the consumer's canonical labels, obtained from
the already-proved raw `sourceLength_boundary` through `sourceLength_eq`. -/
theorem canon_boundary (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6)
    (Zc : Fin 11 → Point) (i : Fin 9) (side : Fin 2) :
    ResumeNetwork.edgeLength (canonAnchors u) (canonCenters u) Zc (Sum.inl (i, side)) ≤ u 6 := by
  fin_cases side
  · rw [← edgeMap_preimage_zero i]
    rw [edgeLength_edgeMap_eq_sourceLength]
    exact sourceLength_boundary u hsin hR _ _ _
  · rw [← edgeMap_preimage_one i]
    rw [edgeLength_edgeMap_eq_sourceLength]
    exact sourceLength_boundary u hsin hR _ _ _

/-- **The oracle upper bound for the canonical candidate configuration**: with `hF0` supplied by the
proved fixed rational point `O0` (`FlashSlackConsumer.faceCoverable01_10`), the 51-edge feasibility
of the canonical network gives `V2 <= (u 6)^2`.  This is the `V2`-side conclusion for the ORIGINAL
candidate; it does not assume anything about an arbitrary cover. -/
theorem oracle_le_sq (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) (hres : residual u = 0)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) :
    ResumeNetwork.V2 (canonAnchors u) ≤ (u 6) ^ 2 := by
  obtain ⟨Z, hZ⟩ :=
    exists_face_witnesses u hu hres (FlashSlackConsumer.faceCoverable01_10 u hu)
  refine ResumeNetwork.oracle_le_of_geometric_witnesses (U := canonAnchors u)
    (C := canonCenters u) (Z := Z) (r := u 6) hR ?_ hZ
  intro i side
  exact canon_boundary u hsin hR Z i side

/-! ## S-level: the oracle consumer on the ACTUAL C891 root

Discharges all four hypotheses of `oracle_le_sq` from the spec `C891RootSpec` and rewrites the
radius to `Rstar S`.  The `canonAnchors` used are the exact chart objects built from
`TCSystem.thetaOf`/`arcEnd` (canonical anchor j = raw `arcEnd u (j+2)`), not a numeric leaf.
Nothing about an arbitrary cover is assumed or concluded here.
-/

/-- `InCertBox S.root` from the spec's box membership and the two box identifications. -/
theorem inCertBox_root (S : C891RootSpec) (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) :
    RootRangeBoxFull.InCertBox S.root := by
  intro i
  have h := S.root_mem.1 i
  rw [hlo, hhi] at h
  exact h

/-- `residual S.root = 0` from `sys = TCSystem` and the root equation (via `TCSystem_first`). -/
theorem residual_root (S : C891RootSpec) (hsys : S.sys = TCSystem) : residual S.root = 0 := by
  have hz : TCSystem S.root = 0 := by
    rw [← hsys]
    exact S.root_mem.2
  funext i
  have h1 := TCSystem_first S.root i
  have h2 : TCSystem S.root ⟨(i : ℕ), by omega⟩ = 0 := by rw [hz]; rfl
  rw [h1] at h2
  exact h2

/-- **The S-level oracle consumer on the actual root**: the canonical candidate configuration at
`S.root` obeys `V2 <= (Rstar S)^2`. -/
theorem oracle_le_sq_root (S : C891RootSpec) (hsys : S.sys = TCSystem)
    (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    ResumeNetwork.V2 (canonAnchors S.root) ≤ (Rstar S) ^ 2 := by
  have hu : RootRangeBoxFull.InCertBox S.root := inCertBox_root S hlo hhi
  have hres : residual S.root = 0 := residual_root S hsys
  have HR : RootRange S.root := RootRangeBoxFull.rootRange_of_box S.root hu
  have hmain : ResumeNetwork.V2 (canonAnchors S.root) ≤ (S.root 6) ^ 2 :=
    oracle_le_sq S.root hu hres HR.hsin HR.hR
  rw [show Rstar S = S.root 6 from by rw [Rstar, hidx]]
  exact hmain

end N11Formalization.FlashRootNetwork

#print axioms N11Formalization.FlashRootNetwork.oracle_le_sq_root
#print axioms N11Formalization.FlashRootNetwork.residual_root
#print axioms N11Formalization.FlashRootNetwork.inCertBox_root
#print axioms N11Formalization.FlashRootNetwork.oracle_le_sq
