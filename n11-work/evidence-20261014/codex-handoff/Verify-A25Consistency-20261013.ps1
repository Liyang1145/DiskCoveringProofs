$ErrorActionPreference='Stop'
# Verify-A25Consistency-20261013.ps1
# Read-only consistency audit of the A25 landing, modelled on
# Verify-A25Consistency-20261008.ps1 (which was never run: no A25 acceptance
# existed). Differences, all additive:
#   * acceptance/manifest are the 20261013 artifacts; total 233 (30 extras);
#   * owned-source count is compared to run 1 of the pair and to MinimumSources
#     1513 instead of a hard-coded 1483;
#   * the audit-needle set is the full driver set (base + AdditionalAuditNeedles),
#     not just the five base needles;
#   * output is a fresh append-only 20261013 filename.
$project=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..'))
$outPath=Join-Path $PSScriptRoot 'a25-final-readonly-consistency-20261013.json'
if(Test-Path -LiteralPath $outPath){throw 'Append-only consistency report already exists'}
$acceptance=Get-Content -LiteralPath (Join-Path $PSScriptRoot 'ACCEPTANCE-A25-CANONICAL-FINITE-CERTIFICATES-20261013.json') -Raw|ConvertFrom-Json
$manifest=Get-Content -LiteralPath $acceptance.manifest -Raw|ConvertFrom-Json
$priorManifest=Get-Content -LiteralPath (Join-Path $PSScriptRoot 'a24-active-interval-certificates-20261008-manifest.json') -Raw|ConvertFrom-Json
$priorAcceptance=Get-Content -LiteralPath $acceptance.prior_acceptance -Raw|ConvertFrom-Json
$rootSha=(Get-FileHash -LiteralPath (Join-Path $project 'lean\N11Formalization.lean')).Hash
$total=$acceptance.paid_framework_modules
if($rootSha -ne $acceptance.root_sha256 -or $rootSha -ne $manifest.root_sha256 -or
 $manifest.modules_green -ne $total -or $manifest.modules_total -ne $total -or
 $acceptance.new_modules -ne ($total-203) -or $acceptance.unconditional_n11_complete){throw 'Acceptance/manifest/root mismatch'}
foreach($row in @($priorManifest.modules)+@($manifest.modules)){
 if((Get-FileHash -LiteralPath $row.source).Hash -ne $row.sha256){throw "Source drift: $($row.module)"}
}
foreach($e in $priorAcceptance.evidence){
 if((Get-FileHash -LiteralPath $e.log).Hash -ne $e.log_sha256 -or
   (Get-FileHash -LiteralPath $e.source).Hash -ne $e.source_sha256){throw 'A24 accepted probe evidence drift'}
}
foreach($row in $manifest.modules){
 foreach($log in @($row.standalone_log,$row.module_log)){
  $result=Get-Content -LiteralPath "$log.result.json" -Raw|ConvertFrom-Json
  if($result.exit -ne 0 -or !$result.unchanged){throw "Module evidence failed: $log"}
 }
}
$auditText='';$controlText=''
foreach($e in $acceptance.evidence){
 if((Get-FileHash -LiteralPath $e.log).Hash -ne $e.log_sha256 -or
   (Get-FileHash -LiteralPath $e.source).Hash -ne $e.source_sha256){throw 'Probe evidence drift'}
 $result=Get-Content -LiteralPath ($e.log+'.result.json') -Raw|ConvertFrom-Json
 if($result.exit -ne 0 -or !$result.unchanged -or $result.build -or
   $result.sha256_after -ne $e.source_sha256){throw 'Probe result mismatch'}
 $body=Get-Content -LiteralPath $e.log -Raw
 if($body -match 'sorryAx|native_decide|Lean\.ofReduceBool|error[:(]'){throw 'Forbidden or failing probe'}
 foreach($hit in [regex]::Matches($body,'depends on axioms:\s*\[([^\]]*)\]','Singleline')){
  foreach($axiomName in ($hit.Groups[1].Value -split ',')){
   if($axiomName.Trim() -and $axiomName.Trim() -notin @('propext','Classical.choice','Quot.sound')){throw 'Unpermitted axiom'}
  }
 }
 if($e.log -like '*root-audit*'){$auditText=$body}else{$controlText=$body}
}
foreach($needle in @('SevenClassExclusions','sourceRoot 6','SevenFiniteTables',
 'full_disk_bound_of_finite_class_tables','balanced_certificates_of_two',
 'still_explicit_full_disk_consumer','q0Coordinates','q1Coordinates',
 'constantCoeffQ_pullback','ear_asin_863314','face_path_hasDerivAt',
 'plane_fixed_radius_difference','face_upper_of_gradient_plane_tree',
 'face_upper_of_rounded_plane_tree','qCell_mem','PositiveCertificate.sound',
 'exclude_q0_ordered','exclude_q1_ordered','seven_class_exclusions_of_finite',
 'balanced_orbit')){
 if(!$auditText.Contains($needle)){throw "Missing root interface $needle"}
}
foreach($needle in @('wrong_piLo_prune_discards_boundary','zero_chord_cell_not_positive_certificate',
 'flat_plane_rounded_endpoint_retained','reflection_switch_offset_fails_sector_owner',
 'equal_p_envelope_keeps_pi')){
 if(!$controlText.Contains($needle)){throw "Missing A25 control $needle"}
}
$pair=@(Get-Content -LiteralPath $acceptance.root_pair -Raw|ConvertFrom-Json)
if($pair.Count -ne 2){throw 'Expected two frozen root runs'}
$owned=$pair[0].source_count
if($owned -lt 1513){throw "Owned source count below 1513: $owned"}
foreach($run in $pair){
 if($run.exit -ne 0 -or !$run.unchanged -or $run.changed_sources.Count -or
  $run.root_sha256_before -ne $rootSha -or $run.root_sha256_after -ne $rootSha -or
  $run.source_count -ne $owned){throw 'Root pair mismatch'}
}
foreach($docPath in @((Join-Path $project 'STATUS.md'),(Join-Path $PSScriptRoot 'GOAL.md'),
 (Join-Path $PSScriptRoot 'RECOVERY-20261007.md'),
 (Join-Path $PSScriptRoot 'A25-CANONICAL-FINITE-HANDOFF-20261013.md'))){
 $body=Get-Content -LiteralPath $docPath -Raw
 if(!$body.Contains('A25') -or !$body.Contains($rootSha)){throw "Documentation not current: $docPath"}
}
$counts=$acceptance.unchanged_historical_counts
if($counts.c450_remaining -ne 25 -or $counts.energy_remaining -ne 2076 -or $counts.sharp_paid -ne 120){throw 'Historical counts changed'}
[ordered]@{timestamp=(Get-Date).ToString('o');root_sha256=$rootSha;modules_green=$total;
 prior_module_sources_unchanged=203;new_modules=($total-203);frozen_root_runs=2;owned_lean_sources=$owned;
 root_standard_axiom_reports=[regex]::Matches($auditText,'depends on axioms:').Count;
 control_standard_axiom_reports=[regex]::Matches($controlText,'depends on axioms:').Count;
 accepted_sources_and_evidence_unchanged=$true;documentation_current=$true;
 unconditional_n11_complete=$false;c450_remaining=25;energy_remaining=2076;classes_remaining=7
}|ConvertTo-Json -Depth 5|Set-Content -LiteralPath $outPath -Encoding utf8
Write-Output "A25 final consistency verified: $outPath"
