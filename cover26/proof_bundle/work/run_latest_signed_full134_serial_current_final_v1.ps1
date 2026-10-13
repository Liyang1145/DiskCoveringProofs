param(
    [Parameter(Mandatory=$true)][string]$taskParentCurrent,
    [Parameter(Mandatory=$true)][string]$taskParentFinal,
    [Parameter(Mandatory=$true)][string]$taskFrontier,
    [Parameter(Mandatory=$true)][string]$taskOverlay,
    [Parameter(Mandatory=$true)][string]$taskOverlayReplay,
    [Parameter(Mandatory=$true)][string]$taskNarrative,
    [Parameter(Mandatory=$true)][string]$taskCurrentTarget,
    [Parameter(Mandatory=$true)][string]$taskFinalTarget,
    [Parameter(Mandatory=$true)][string]$taskIdentityControls,
    [Parameter(Mandatory=$true)][string]$taskAccountingControls
)

$ErrorActionPreference = 'Stop'
$taskDependencyFolder = -join ([char[]]@(0x70ED,0x7231,0x5355,0x673A,0x4F46,0x840C,0x65B0))
$taskPython = 'C:/'+$taskDependencyFolder+'/dependencies/python/python.exe'
$taskJoins = Get-CimInstance Win32_Process | Where-Object {
    $_.Name -eq 'python.exe' -and $_.CommandLine -match
    '(audit_stage_catalogue_with_executor_contract|audit_stage_catalogue_with_closed_pool|recheck_current_stage_catalogue_inventory|audit_mixed_curvature_candidate_current|recheck_mixed_curvature_candidate_current|audit_product_candidate_current|recheck_product_candidate_current|audit_latest_signed_full134_candidate_current|recheck_latest_signed_full134_candidate_current)\.py'
}
if ($taskJoins) { throw 'An actual complete-current join or independent final is still live; do not overlap.' }
foreach ($taskFresh in @(
    $taskCurrentTarget,$taskFinalTarget,
    $taskCurrentTarget.Replace('.json','-overlay-semantic-replay.json'),
    $taskCurrentTarget.Replace('.json','-closed-type-pool.json'),
    $taskCurrentTarget.Replace('.json','-closed-receipt-checks.json'),
    $taskCurrentTarget.Replace('.json','-terminal-obligations.json')
)) {
    if (Test-Path -LiteralPath $taskFresh) { throw 'A latest-current output/partial already exists; preserve and inspect.' }
}
foreach ($taskRequired in @(
    $taskParentCurrent,$taskParentFinal,$taskFrontier,"$taskOverlay/VERIFIED.json",
    $taskOverlayReplay,$taskNarrative,$taskIdentityControls,$taskAccountingControls
)) {
    if (-not (Test-Path -LiteralPath $taskRequired)) { throw 'Actual whole geometry/current evidence is incomplete.' }
}
$taskOwn = Get-Content -LiteralPath "$taskOverlay/VERIFIED.json" -Encoding UTF8 -Raw | ConvertFrom-Json
$taskOwnHash = (Get-FileHash -LiteralPath "$taskOverlay/VERIFIED.json" -Algorithm SHA256).Hash.ToLowerInvariant()
$taskPublishedHash = (Get-FileHash -LiteralPath $taskOverlayReplay -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskOwn.schema -ne 'N26-accepted-latest-signed-grown-full134rod-partial-forests-v1' -or
    $taskOwn.verified -ne $true -or $taskOwnHash -cne $taskPublishedHash -or
    $taskOwn.negative_controls_rejected.Count -ne 21 -or
    $taskOwn.actual_latest_root25_v3_and_root28_grown_v9_replayed_not_reset -ne $true -or
    $taskOwn.global_optimality_proved -ne $false) {
    throw 'Require actual ENTIRE own geometry and SAME-main publication,not compile/fixtures/arithmetic.'
}
$taskIdentity = Get-Content -LiteralPath $taskIdentityControls -Encoding UTF8 -Raw | ConvertFrom-Json
$taskAccounting = Get-Content -LiteralPath $taskAccountingControls -Encoding UTF8 -Raw | ConvertFrom-Json
$taskFinalHash = (Get-FileHash -LiteralPath 'work/recheck_latest_signed_full134_candidate_current.py' -Algorithm SHA256).Hash.ToLowerInvariant()
$taskIdentityHash = (Get-FileHash -LiteralPath 'work/n26_candidate_identity_with_latest_signed_forests.py' -Algorithm SHA256).Hash.ToLowerInvariant()
$taskAccountingHash = (Get-FileHash -LiteralPath 'work/n26_latest_signed_full134_current_accounting.py' -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskIdentity.tested_independent_final_executor_sha256 -cne $taskFinalHash -or
    $taskIdentity.tested_identity_module_sha256 -cne $taskIdentityHash -or
    $taskIdentity.synthetic_invalid_latest_identity_controls_rejected.Count -ne 20 -or
    $taskIdentity.synthetic_invalid_final_acceptance_controls_rejected.Count -ne 16 -or
    $taskIdentity.synthetic_latest_receipt_shapes_NOT_an_actual_geometry_acceptance -ne $true -or
    $taskAccounting.tested_pure_final_accounting_sha256 -cne $taskAccountingHash -or
    $taskAccounting.actual_invalid_root_history_ledger_count_and_scope_controls_rejected.Count -ne 21 -or
    $taskIdentity.new_geometric_payments -ne 0 -or $taskAccounting.new_geometric_payments -ne 0) {
    throw 'Latest identity/final/root-history controls are absent or stale;do not use old v1 final controls.'
}
# The actual admission also identifies the genuinely current candidate owner.
# An owned8-bound25-root receipt cannot be relabelled as a mixed16-root receipt.
& $taskPython work/audit_latest_signed_full134_candidate_current.py --parent-audit $taskParentCurrent --parent-digest-recheck $taskParentFinal --frontier $taskFrontier --overlay $taskOverlay --overlay-replay $taskOverlayReplay --narrative $taskNarrative --identity-regression $taskIdentityControls --accounting-regression $taskAccountingControls --output $taskCurrentTarget
if ($LASTEXITCODE -ne 0) { throw 'Actual ENTIRE latest-current adoption failed;preserve all partial evidence.' }
& $taskPython work/recheck_latest_signed_full134_candidate_current.py --current-audit $taskCurrentTarget --overlay $taskOverlay --overlay-replay $taskOverlayReplay --report $taskFinalTarget
if ($LASTEXITCODE -ne 0) { throw 'Actual independent final failed;latest current is not formally completed.' }
Write-Output 'Actual latest-current and independent final pair completed;global n26 proof remains pending.'
