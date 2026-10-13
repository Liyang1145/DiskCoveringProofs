param(
    [Parameter(Mandatory=$true)][string]$taskSource,
    [Parameter(Mandatory=$true)][string]$taskSourceReplay,
    [Parameter(Mandatory=$true)][string]$taskFormalCurrent,
    [Parameter(Mandatory=$true)][string]$taskFormalFinal,
    [Parameter(Mandatory=$true)][string]$taskCandidateOwnerCurrent,
    [Parameter(Mandatory=$true)][string]$taskCandidateOwnerFinal
)

$ErrorActionPreference = 'Stop'
$taskDependencyFolder = -join ([char[]]@(0x70ED,0x7231,0x5355,0x673A,0x4F46,0x840C,0x65B0))
$taskPython = 'C:/'+$taskDependencyFolder+'/dependencies/python/python.exe'
$taskBundle = 'outputs/n26-current-candidate-latest-signed-grown-full134rod-forests-v1'
$taskPublication = 'outputs/n26-current-candidate-latest-signed-grown-full134rod-forests-published-replay-v1.json'
$taskGrown = 'outputs/n26-candidate-root28-grown-full134rod-intersection-forest-diagnosis-v9.json'
$taskGrownControls = 'outputs/n26-candidate-root28-grown-full134rod-intersection-independent-controls-v1.json'
$taskGuardPath = 'outputs/n26-latest-signed-grown-full134rod-geometry-ownership-retention-role-controls-v1.json'
foreach ($taskFresh in @($taskBundle,$taskPublication)) {
    if (Test-Path -LiteralPath $taskFresh) {
        throw 'A complete latest geometry target/partial already exists. Preserve it; do not restart.'
    }
}
foreach ($taskRequired in @($taskGrown,$taskGrownControls,$taskGuardPath)) {
    if (-not (Test-Path -LiteralPath $taskRequired)) {
        throw 'Actual grown-v9 production, automatic tests or own geometry guards incomplete.'
    }
}
$taskRootWorkers = Get-CimInstance Win32_Process | Where-Object {
    $_.Name -eq 'python.exe' -and $_.CommandLine -match
    '(continue_checked_root28_grown_full134rod_intersections|test_checked_root28_grown_full134rod_intersections)\.py'
}
if ($taskRootWorkers) {
    throw 'Original grown-v9 producer/automatic tester is still live. Do not overlap or substitute v8.'
}
$taskGuard = Get-Content -LiteralPath $taskGuardPath -Encoding UTF8 -Raw | ConvertFrom-Json
$taskExecutorHash = (Get-FileHash -LiteralPath 'work/verify_latest_candidate_signed_full134rod_forests.py' -Algorithm SHA256).Hash.ToLowerInvariant()
$taskTestHash = (Get-FileHash -LiteralPath 'work/test_latest_signed_full134_geometry_contracts.py' -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskGuard.tested_own_full_geometry_executor_sha256 -cne $taskExecutorHash -or
    $taskGuard.executed_test_sha256 -cne $taskTestHash -or
    $taskGuard.actual_ownership_unpaid_scope_retention_and_producer_role_guards_rejected.Count -ne 31 -or
    $taskGuard.actual_v8_was_REJECTED_as_grown_v9_NOT_used_to_replace_it -ne $true -or
    $taskGuard.ENTIRE_source_model_history_and_latest_forest_geometry_acceptance_NOT_executed -ne $true -or
    $taskGuard.new_geometric_payments -ne 0) {
    throw 'Actual geometry ownership/retention/role controls are missing or stale.'
}
& $taskPython work/build_latest_candidate_signed_full134rod_forests.py --source $taskSource --source-replay $taskSourceReplay --formal-current $taskFormalCurrent --formal-final $taskFormalFinal --candidate-owner-current $taskCandidateOwnerCurrent --candidate-owner-final $taskCandidateOwnerFinal --arithmetic-proof-time-source outputs/n26-current-candidate-owned-forest-v8 --root25-diagnosis outputs/n26-candidate-root25-checked-support-cost-forest-diagnosis-v3.json --root25-controls outputs/n26-candidate-root25-checked-support-cost-independent-controls-v3.json --root25-seed outputs/n26-candidate-root25-preserved-support-cost-forest-diagnosis-v2.json --root28-v8 outputs/n26-candidate-root28-checked-support-cost-forest-diagnosis-v8.json --root28-v8-controls outputs/n26-candidate-root28-checked-support-cost-independent-controls-v4.json --root28-grown-diagnosis $taskGrown --root28-grown-controls $taskGrownControls --interface-contract-controls $taskGuardPath --output $taskBundle
if ($LASTEXITCODE -ne 0) { throw 'Fresh BOTH-latest-forest geometry freeze failed. Preserve any partials.' }
& $taskPython "$taskBundle/verify_latest_candidate_signed_full134rod_forests.py" --input $taskBundle --report "$taskBundle/VERIFIED.json"
if ($LASTEXITCODE -ne 0) { throw 'ENTIRE actual latest source/model/history/forest geometry acceptance failed.' }
& $taskPython "$taskBundle/verify_latest_candidate_signed_full134rod_forests.py" --input $taskBundle --report $taskPublication
if ($LASTEXITCODE -ne 0) { throw 'Actual SAME frozen latest-forest main publication failed.' }
$taskOwnHash = (Get-FileHash -LiteralPath "$taskBundle/VERIFIED.json" -Algorithm SHA256).Hash.ToLowerInvariant()
$taskPublishedHash = (Get-FileHash -LiteralPath $taskPublication -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskOwnHash -cne $taskPublishedHash) {
    throw 'Actual complete latest-forest acceptance/publication bytes differ; inspect before adoption.'
}
Write-Output 'Actual own geometry chain completed. SERIAL latest-current composition and independent final STILL REQUIRED.'
