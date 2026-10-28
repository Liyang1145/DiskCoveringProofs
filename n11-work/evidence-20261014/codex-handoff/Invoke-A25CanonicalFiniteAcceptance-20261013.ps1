param(
 [string]$Tag='a25-canonical-finite-certificates-20261013',
 [switch]$SkipStaging,
 [switch]$SkipGuard,
 [switch]$AcceptanceOnly
)
$ErrorActionPreference='Stop'
# A25 landing driver, 20261013.
#
# Structure follows Invoke-A25CanonicalFiniteAcceptance-20261008.ps1, with three
# deliberate changes, each justified:
#
# (1) EXTRAS LIST CORRECTED 28 -> 30. The 2026-10-08 driver omitted
#     CanonicalBalancedFiniteClassCertificate and
#     SharedMomentConcreteSectorGradientControls, both newer than the A24 cut.
#     203 + 30 = 233.
#
# (2) STAGING STEP ADDED. Invoke-A21Manifest-20261007.ps1 discovers evidence with
#     `Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.log.result.json' -File`,
#     which is NON-RECURSIVE and scoped to evidence\codex-handoff\. Fresh gates
#     and builds written by teammates under evidence\a25-landing-20261013\mN\
#     are therefore invisible to it. That shared script must stay byte-identical
#     for all historical acceptances, so Stage-A25ModuleEvidence-20261013.ps1
#     restages the teammate evidence into evidence\codex-handoff\ (copying the
#     result.json + .log + .stderr and rewriting only the JSON's `log` field to
#     point at the copy). Ordering, exit codes and hashes are preserved verbatim.
#
# (3) READINESS GUARD BETWEEN STAGING AND MANIFEST. Invoke-A21Manifest is
#     append-only and THROWS if the tag exists, so a premature run would burn the
#     tag on a red result. Check-A25ManifestReadiness-20261013.ps1 replicates the
#     manifest's rule read-only and reports every red module with its reason and
#     whether that module has evidence under OTHER directories (so a path-scoping
#     bug is distinguishable from a genuinely missing build). The driver stops
#     before the manifest if the guard still shows red, unless -SkipGuard is used.

$extras=@('SharedMomentFactorPermutation','ActualCanonicalFaceCoordinates',
 'ActualCanonicalMomentTransport','ActualSharedMomentSharpConstant',
 'RationalTrigLocalLipschitz','SharedMomentFactorLocalGradientCertificate',
 'SharedMomentFacePlaneCertificate','SharedMomentFacePlaneDirectCertificate',
 'SharedMomentFacePlaneGradientCertificate','SharedMomentFacePlaneRoundedGradientCertificate',
 'MetricSectorRationalCellCertificate','MetricSectorLocalGradientCertificate',
 'SharedMomentFiniteFactorCertificate','SharedMomentEfficientFactorCertificate',
 'ActualCanonicalSharedMomentConsumer','CanonicalSharedMomentFiniteCertificate',
 'CanonicalBalancedGraphOrbits','CanonicalSharedMomentOrbitTransport',
 'SharedMomentConcreteLeafControls','SharedMomentConcreteSwitchBatch',
 'SharedMomentConcreteSectorControls','SharedMomentA25CertificateControls',
 'SharedMomentConcreteFace1Data','SharedMomentConcreteFace1Part0',
 'SharedMomentConcreteFace1Part1','SharedMomentConcreteFace1Part2',
 'SharedMomentConcreteFace1Part3','SharedMomentConcreteFace1Certificate',
 'CanonicalBalancedFiniteClassCertificate','SharedMomentConcreteSectorGradientControls')
$total=203+$extras.Count
if($total -ne 233){throw "Extras list must give 233, got $total"}
$dotted=@($extras|ForEach-Object{"N11Formalization.$_"})

if(!$AcceptanceOnly){
if(!$SkipStaging){
 Write-Output '--- STAGE teammate evidence into codex-handoff (manifest is non-recursive)'
 & (Join-Path $PSScriptRoot 'Stage-A25ModuleEvidence-20261013.ps1') -Modules $dotted -Tag $Tag
}

if(!$SkipGuard){
 Write-Output '--- READINESS GUARD (read-only; catches path-scoping vs missing build)'
 $guardOut=& (Join-Path $PSScriptRoot 'Check-A25ManifestReadiness-20261013.ps1') -Tag $Tag 2>&1
 $guardOut|ForEach-Object{Write-Output $_}
 $line=@($guardOut|Where-Object{$_ -match 'WOULD-BE MANIFEST'})
 if($line -and $line[0] -notmatch "green=233/233"){
   throw "Guard says manifest would NOT be 233/233 ($($line[0])). Refusing to burn append-only tag '$Tag'. See a25-readiness-$Tag.json."
 }
}

& (Join-Path $PSScriptRoot 'Invoke-A21Manifest-20261007.ps1') -Tag $Tag -AssertAllGreen `
 -BaseManifest 'a24-active-interval-certificates-20261008-manifest.json' `
 -ExtraModules $extras -ExpectedTotal $total

# Post-manifest hard assertion: 233/233 and an empty incomplete list.
$mf=Get-Content -LiteralPath (Join-Path $PSScriptRoot "$Tag-manifest.json") -Raw|ConvertFrom-Json
if($mf.modules_green -ne 233 -or $mf.modules_total -ne 233 -or @($mf.incomplete_modules).Count -ne 0){
 throw "Manifest not all-green: $($mf.modules_green)/$($mf.modules_total), incomplete=$(($mf.incomplete_modules) -join ',')"
}
Write-Output "manifest post-check OK: $($mf.modules_green)/$($mf.modules_total), incomplete empty"
}
# end of !$AcceptanceOnly

$project=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..'))
& (Join-Path $PSScriptRoot 'Accept-A9Framework-20261005.ps1') `
 -Manifest (Join-Path $PSScriptRoot "$Tag-manifest.json") `
 -RootPair (Join-Path $project "evidence\resume-lead\root-$Tag-pair.json") `
 -AuditLog (Join-Path $PSScriptRoot 'a25-canonical-finite-root-audit-20261013-gate2.log') `
 -ControlLog (Join-Path $PSScriptRoot 'a25-canonical-finite-controls-20261013-gate2.log') `
 -Tag 'A25-CANONICAL-FINITE-CERTIFICATES-20261013' `
 -PriorAcceptance 'ACCEPTANCE-A24-ACTIVE-INTERVAL-CERTIFICATES-20261008.json' `
 -PriorTotal 203 -ExpectedTotal $total -MinimumSources 1513 `
 -PaidDescription 'Canonical actual face/slot/edge coordinate builders and exact rational coefficient/mask/constant transport; sharp ear arcsine bracket; signed full-cell face/switch and positive-chord sector derivatives; exact pi-plane derivative differences and finite outward radius brackets; flexible closed-root factor trees and seven-class finite-table consumer preserving the original full disk and SAME sourceRoot6; balanced graph orbit and certificate transport reducing eight cuts to two representatives; exact finite-table Q1-balanced exclusion from two representative tables; genuine HOST coefficient switch and face trees and a full-domain sector control, each with finite kernel checks.' `
 -UnpaidDescription '25 C450 source segments; 2076 energy terminals, including 389 without genuine routes; all seven actual Q0/Q1 class exclusions and unconditional SAME sourceRoot6 arbitrary-cover theorem. Concrete individual factor certificates do not pay a class before complete coefficient/mask tables, every factor certificate and strict total are instantiated and checked. HOST complete tree plans and exact total budgets are not Lean evidence. The eight-to-two balanced orbit transport and the two-table balanced finite class certificate still require the representative finite tables to be instantiated.' `
 -AdditionalAuditNeedles @('still_explicit_full_disk_consumer','SevenClassExclusions',
  'q0Coordinates','q1Coordinates','constantCoeffQ_pullback','ear_asin_863314',
  'face_path_hasDerivAt','plane_fixed_radius_difference','face_upper_of_gradient_plane_tree',
  'face_upper_of_rounded_plane_tree','qCell_mem','PositiveCertificate.sound',
  'exclude_q0_ordered','exclude_q1_ordered','SevenFiniteTables',
  'seven_class_exclusions_of_finite','full_disk_bound_of_finite_class_tables',
  'balanced_orbit','balanced_certificates_of_two')
