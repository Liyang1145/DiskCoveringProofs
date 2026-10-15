import N11Formalization.SourceExactRoot
import N11Formalization.ActualMetricClassReduction

/-! Calibration probe (m4, A25 landing 20261013).

Purpose: establish, from a log I actually produced, that the specific `#print` /
`#check` commands used by `ProbeA25CanonicalFiniteRootAudit.lean` DO emit the
driver-required needle strings. Only the needles that cannot already be witnessed
in an existing produced log are calibrated here.

This probe deliberately imports only two already-green A24 modules so it can be
gated BEFORE the A25 root imports land (the full A25 audit probe imports
`N11Formalization` and therefore cannot be gated until the root import set is
final).

Needles calibrated here:
  * `sourceRoot 6`         <- `#print N11Formalization.SourceExactRoot.sourceRadius`
                              prints the definition body `sourceRoot 6`.
                              EMPIRICALLY CONFIRMED (A24 audit log line 1-2).
  * `SevenClassExclusions` <- `#print ...ActualMetricClassReduction.SevenClassExclusions`

Already witnessed in `a25-canonical-finite-gate1.log` (produced 2026-10-08) and
therefore NOT re-calibrated here: `SevenFiniteTables`,
`full_disk_bound_of_finite_class_tables`, `seven_class_exclusions_of_finite`,
`q0_run_exclusion_of_finite`, `q1_run_exclusion_of_finite`.

Sanity the emitted text must satisfy (checked by the pipeline, not by Lean):
the literal ASCII substring `sourceRoot 6` must appear, i.e. the token
`sourceRoot` followed by exactly one space then the character `6`. -/

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA25SourceRootNeedleCalibration

/-- The audited radius is literally coordinate 6 of the C891 root. This is the
statement the acceptance needle `sourceRoot 6` is a proxy for. -/
theorem sourceRadius_is_sourceRoot_six :
    SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl

theorem still_explicit_thirteen_way_class_dependency :
    ActualMetricClassReduction.SevenClassExclusions →
      Nonempty ActualMetricClassReduction.SevenClassExclusions := fun h => ⟨h⟩

end N11Formalization.ProbeA25SourceRootNeedleCalibration

#print N11Formalization.SourceExactRoot.sourceRadius
#print N11Formalization.ActualMetricClassReduction.SevenClassExclusions
#check @N11Formalization.ProbeA25SourceRootNeedleCalibration.sourceRadius_is_sourceRoot_six
#check @N11Formalization.ProbeA25SourceRootNeedleCalibration.still_explicit_thirteen_way_class_dependency
#print axioms N11Formalization.ProbeA25SourceRootNeedleCalibration.sourceRadius_is_sourceRoot_six
#print axioms N11Formalization.ProbeA25SourceRootNeedleCalibration.still_explicit_thirteen_way_class_dependency
