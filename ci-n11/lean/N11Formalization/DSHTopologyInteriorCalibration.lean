/-
n11-formalization — DSH line C4 groundwork, part 3 (teammate `topo-interior`, task-4).

# DSHTopologyInteriorCalibration — calibrating the interface on the frozen known-answer table

Scope: **local groundwork, standalone**; lead integrates. No `Covers` premise is discharged and
no `Covers → Feasible` implication is claimed (C5, lead-side).

Purpose: prove that the interface of `DSHTopologyInteriorInterface` (`FaceWitness` /
`RawFaceWitness`) is *definitionally the same quantity* as the frozen
`FlashBoundaryCapsFaces.FaceCoverable` used by the root-integrated witness table, under the
frozen centre labeling `FlashRootNetwork.canonCenters u = fun j => centersOfRoot u (rawOf j)`.
This is the "calibrate the new instrument on a known answer" step: without it, `FaceWitness`
would be an unchecked lookalike.

Two directions are proved:

* `faceWitness_canonCenters_iff` — canonical face `f` of the frozen `ResumeNetwork.face` table
  with `C = canonCenters u` and `r = u 6` is exactly `FaceCoverable u (faceI1 n) (faceI2 n)
  (faceI3 n)` with `n = faceRaw f`;
* `rawFaceWitness_canonCenters_iff` — raw source face `g` is exactly `FaceCoverable u` at the
  three frozen `sourceFaces g v`, i.e. the per-face content of the paid source data.
-/
import N11Formalization.DSHTopologyInteriorInterface
import N11Formalization.FlashBoundaryCapsFaces
import N11Formalization.FlashLeafRootNetwork
import N11Formalization.FlashSlackConsumer
import N11Formalization.SourceSharpEnergyCalibration
import N11Formalization.RootRangeBoxFull

set_option autoImplicit false

namespace N11Formalization.DSHTopologyInterior

open N11Formalization ResumeNetwork ResumeLocalIncidence
open FlashBoundaryCapsFaces

/-! ## 0. The canonical face of a source face -/

/-- The canonical face carrying the source face `g`: `face (faceMap g) ·`. -/
abbrev resumeFace (g : Fin 9) (v : Fin 3) : Fin 11 := face (faceMap g) v

/-! ## 1. The center labeling identity used by the calibration -/

/-- The frozen canonical center labeling reads the raw site through `rawOf`, and `rawOf` is a
left inverse of `rawToCanon`; hence on the canonical face vertices it agrees with the raw
vertex labels of the frozen table. -/
theorem canonCenters_face_rawVtx (u : Fin 12 → ℝ) (f : Fin 11) (v : Fin 3) :
    FlashRootNetwork.canonCenters u (face f v) =
      centersOfRoot u (FlashRootNetwork.rawVtx f v) := by
  simp only [FlashRootNetwork.canonCenters]
  rw [FlashRootNetwork.face_eq_rawToCanon, FlashRootNetwork.rawOf_rawToCanon]

/-- Same identity for the frozen source face table. -/
theorem canonCenters_sourceFaces (u : Fin 12 → ℝ) (g : Fin 9) (v : Fin 3) :
    FlashRootNetwork.canonCenters u (resumeFace g v) = centersOfRoot u (sourceFaces g v) := by
  simp only [FlashRootNetwork.canonCenters, resumeFace]
  rw [← ResumeLocalIncidence.faceMap_exact g v, FlashRootNetwork.rawOf_rawToCanon]

/-! ## 2. Calibration of `FaceWitness` against the frozen `FaceCoverable` -/

/-- The three raw vertices of canonical face `f` are the frozen `faceI1/2/3` entries. -/
theorem rawVtx_eq_table (f : Fin 11) :
    FlashRootNetwork.rawVtx f 0 = faceI1 (FlashRootNetwork.faceRaw f) ∧
      FlashRootNetwork.rawVtx f 1 = faceI2 (FlashRootNetwork.faceRaw f) ∧
      FlashRootNetwork.rawVtx f 2 = faceI3 (FlashRootNetwork.faceRaw f) := by
  refine ⟨rfl, rfl, rfl⟩

/-- **Calibration (canonical faces).** The interface's `FaceWitness` at the frozen center
labeling is *exactly* the frozen `FaceCoverable`, for each of the 11 canonical faces. -/
theorem faceWitness_canonCenters_iff (u : Fin 12 → ℝ) (f : Fin 11) :
    FaceWitness (FlashRootNetwork.canonCenters u) f (u 6) ↔
      FlashBoundaryCapsFaces.FaceCoverable u
        (faceI1 (FlashRootNetwork.faceRaw f)) (faceI2 (FlashRootNetwork.faceRaw f))
        (faceI3 (FlashRootNetwork.faceRaw f)) := by
  have h0 := (rawVtx_eq_table f).1
  have h1 := (rawVtx_eq_table f).2.1
  have h2 := (rawVtx_eq_table f).2.2
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_, ?_, ?_⟩
    · simpa [canonCenters_face_rawVtx u f 0, h0] using hz 0
    · simpa [canonCenters_face_rawVtx u f 1, h1] using hz 1
    · simpa [canonCenters_face_rawVtx u f 2, h2] using hz 2
  · rintro ⟨O, h1', h2', h3'⟩
    have key : ∀ v : Fin 3, dist (FlashRootNetwork.canonCenters u (face f v)) O ≤ u 6 := by
      intro v
      fin_cases v
      · simpa [canonCenters_face_rawVtx u f 0, h0] using h1'
      · simpa [canonCenters_face_rawVtx u f 1, h1] using h2'
      · simpa [canonCenters_face_rawVtx u f 2, h2] using h3'
    exact ⟨O, key⟩

/-- **Calibration (raw source faces).** The interface's `RawFaceWitness` at the frozen center
labeling is exactly the frozen `FaceCoverable` at the three frozen `sourceFaces g v`. -/
theorem rawFaceWitness_canonCenters_iff (u : Fin 12 → ℝ) (g : Fin 9) :
    RawFaceWitness (FlashRootNetwork.canonCenters u) g (u 6) ↔
      FlashBoundaryCapsFaces.FaceCoverable u (sourceFaces g 0) (sourceFaces g 1)
        (sourceFaces g 2) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_, ?_, ?_⟩
    · simpa [canonCenters_sourceFaces u g 0, ResumeLocalIncidence.faceMap_exact g 0] using hz 0
    · simpa [canonCenters_sourceFaces u g 1, ResumeLocalIncidence.faceMap_exact g 1] using hz 1
    · simpa [canonCenters_sourceFaces u g 2, ResumeLocalIncidence.faceMap_exact g 2] using hz 2
  · rintro ⟨O, h1, h2, h3⟩
    have key : ∀ v : Fin 3,
        dist (FlashRootNetwork.canonCenters u (ResumeGlobal.rawToCanon (sourceFaces g v))) O ≤ u 6 := by
      intro v
      fin_cases v
      · simpa [canonCenters_sourceFaces u g 0, ResumeLocalIncidence.faceMap_exact g 0] using h1
      · simpa [canonCenters_sourceFaces u g 1, ResumeLocalIncidence.faceMap_exact g 1] using h2
      · simpa [canonCenters_sourceFaces u g 2, ResumeLocalIncidence.faceMap_exact g 2] using h3
    exact ⟨O, key⟩

/-- The interface's canonical-indexed source witnesses are the frozen `FaceCoverable` at the
canonical face of each source face. -/
theorem faceWitness_faceMap_iff (u : Fin 12 → ℝ) (g : Fin 9) :
    FaceWitness (FlashRootNetwork.canonCenters u) (faceMap g) (u 6) ↔
      FlashBoundaryCapsFaces.FaceCoverable u (sourceFaces g 0) (sourceFaces g 1)
        (sourceFaces g 2) :=
  (rawFaceWitness_iff (FlashRootNetwork.canonCenters u) g (u 6)).symm.trans
    (rawFaceWitness_canonCenters_iff u g)

/-! ## 3. Known-answer check: the source configuration satisfies the interface

The frozen paid `faceOK_table` supplies all 11 canonical `FaceCoverable`s from the single
hypothesis `FaceCoverable u 0 1 10`; via the calibration this is a full `FaceWitness` family at
the frozen center labeling — i.e. the interface of part 1 is *inhabited by the known answer*. -/

/-- **Known-answer calibration run.** At `u = SourceExactRoot.sourceRoot` (where the frozen
hypothesis is paid), the interface's 11 canonical `FaceWitness`es all hold at `r = sourceRadius`.
This uses only the frozen paid tables, and is a check that the interface computes the intended
quantity. -/
theorem faceWitnesses_at_source_root :
    ∀ f : Fin 11, FaceWitness (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot) f
      (SourceExactRoot.sourceRoot 6) := by
  intro f
  have hu : RootRangeBoxFull.InCertBox SourceExactRoot.sourceRoot :=
    FlashRootNetwork.inCertBox_root SourceExactRoot.sourceSpec rfl rfl
  have hres : N11Formalization.residual SourceExactRoot.sourceRoot = 0 :=
    FlashRootNetwork.residual_root SourceExactRoot.sourceSpec rfl
  have htab := FlashBoundaryCapsFaces.faceOK_table SourceExactRoot.sourceRoot hu hres
    (FlashSlackConsumer.faceCoverable01_10 SourceExactRoot.sourceRoot hu) (FlashRootNetwork.faceRaw f)
  exact (faceWitness_canonCenters_iff SourceExactRoot.sourceRoot f).2 htab

/-- Consistency: the 9 source-face witnesses at the source root come from the same frozen table. -/
theorem rawFaceWitnesses_at_source_root :
    ∀ g : Fin 9, RawFaceWitness (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot) g
      (SourceExactRoot.sourceRoot 6) :=
  fun g => (rawFaceWitness_iff _ g _).2 (faceWitnesses_at_source_root (faceMap g))

/-! ## 4. Verbatim types and axiom prints -/

#check @N11Formalization.DSHTopologyInterior.canonCenters_face_rawVtx
#check @N11Formalization.DSHTopologyInterior.canonCenters_sourceFaces
#check @N11Formalization.DSHTopologyInterior.rawVtx_eq_table
#check @N11Formalization.DSHTopologyInterior.faceWitness_canonCenters_iff
#check @N11Formalization.DSHTopologyInterior.rawFaceWitness_canonCenters_iff
#check @N11Formalization.DSHTopologyInterior.faceWitness_faceMap_iff
#check @N11Formalization.DSHTopologyInterior.faceWitnesses_at_source_root
#check @N11Formalization.DSHTopologyInterior.rawFaceWitnesses_at_source_root

#print axioms N11Formalization.DSHTopologyInterior.canonCenters_face_rawVtx
#print axioms N11Formalization.DSHTopologyInterior.canonCenters_sourceFaces
#print axioms N11Formalization.DSHTopologyInterior.faceWitness_canonCenters_iff
#print axioms N11Formalization.DSHTopologyInterior.rawFaceWitness_canonCenters_iff
#print axioms N11Formalization.DSHTopologyInterior.faceWitness_faceMap_iff
#print axioms N11Formalization.DSHTopologyInterior.faceWitnesses_at_source_root
#print axioms N11Formalization.DSHTopologyInterior.rawFaceWitnesses_at_source_root

end N11Formalization.DSHTopologyInterior