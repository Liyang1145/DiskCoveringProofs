param(
    [Parameter(Mandatory=$true)][string]$taskCurrentAuditPath,
    [Parameter(Mandatory=$true)][string]$taskCurrentFinalPath
)

$ErrorActionPreference = 'Stop'
$taskDependencyFolder = -join ([char[]]@(0x70ED,0x7231,0x5355,0x673A,0x4F46,0x840C,0x65B0))
$taskPython = 'C:/'+$taskDependencyFolder+'/dependencies/python/python.exe'
$taskLatest = 'outputs/n26-candidate-root28-checked-support-cost-forest-diagnosis-v8.json'
$taskLatestControls = 'outputs/n26-candidate-root28-checked-support-cost-independent-controls-v4.json'
$taskDiagnosis = 'outputs/n26-candidate-root28-preserved-full134rod-intersection-forest-diagnosis-v9.json'
$taskReport = 'outputs/n26-candidate-root28-preserved-full134rod-intersection-independent-controls-v1.json'
$taskInputGuardPath = 'outputs/n26-full134rod-intersection-input-binding-guards-v1.json'
if ((Test-Path -LiteralPath $taskDiagnosis) -or (Test-Path -LiteralPath $taskReport)) {
    throw 'A successor artifact already exists. Preserve it and inspect; do not restart.'
}
if ((Test-Path -LiteralPath 'outputs/n26-candidate-root28-grown-full134rod-intersection-forest-diagnosis-v9.json') -or
    (Test-Path -LiteralPath 'outputs/n26-candidate-root28-grown-full134rod-intersection-independent-controls-v1.json')) {
    throw 'A grown successor history exists. Do not discard it by starting the narrow branch from v8.'
}
if (-not (Test-Path -LiteralPath $taskLatest) -or -not (Test-Path -LiteralPath $taskLatestControls)) {
    throw 'Actual latest v8 producer and automatic independent controls have not both completed.'
}
$taskOriginalJobs = Get-CimInstance Win32_Process | Where-Object {
    $_.Name -eq 'python.exe' -and $_.CommandLine -match
    '(continue_checked_support_cost_forest|test_checked_support_cost_continuation)\.py'
}
if ($taskOriginalJobs) {
    throw 'The original v8 producer/control session is still live. Do not overlap or reset it.'
}
$taskInputGuard = Get-Content -LiteralPath $taskInputGuardPath -Encoding UTF8 -Raw | ConvertFrom-Json
$taskProducerHash = (Get-FileHash -LiteralPath 'work/continue_checked_root28_full134rod_intersections.py' -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskInputGuard.schema -ne 'N26-independent-full134rod-intersection-input-binding-guards-v1' -or
    $taskInputGuard.tested_unexecuted_successor_producer_sha256 -cne $taskProducerHash -or
    $taskInputGuard.actual_bundle_VERIFIED_files_bound_not_directory_paths -ne $true -or
    $taskInputGuard.actual_input_guards_rejected.Count -ne 3 -or
    $taskInputGuard.new_geometric_payments -ne 0) {
    throw 'The actual directory-file binding and old-fixture rejection guards are missing or stale.'
}
$taskFinal = Get-Content -LiteralPath $taskCurrentFinalPath -Encoding UTF8 -Raw | ConvertFrom-Json
$taskAuditHash = (Get-FileHash -LiteralPath $taskCurrentAuditPath -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskFinal.schema -ne 'N26-independent-final-current-inventory-rehash-v1' -or
    $taskFinal.all_current_file_digests_rehashed -ne $true -or
    $taskFinal.current_audit_sha256 -cne $taskAuditHash -or
    $taskFinal.global_lower_bound_proved -ne $false -or
    $taskFinal.global_optimality_proved -ne $false) {
    throw 'Choose the actually completed newest formal current audit and matching independent final.'
}
$taskBoundArgs = @(
    '--resource', 'outputs/n26-original-candidate-arithmetic-context-v1',
    '--resource-replay', 'outputs/n26-original-candidate-arithmetic-context-published-replay-v1.json',
    '--current-audit', $taskCurrentAuditPath,
    '--ancestor-current-audit', 'outputs/n26-twenty-third-conditional-current-audit-v23-sparse-v1-strict-with-owned8-scope.json',
    '--source', 'outputs/n26-current-candidate-owned-forest-v8',
    '--seed', 'outputs/n26-candidate-root28-support-cost-refined-forest-diagnosis-v7.json',
    '--seed-controls', 'outputs/n26-candidate-root28-support-cost-refined-independent-controls-v3.json',
    '--policy-controls', 'outputs/n26-support-cost-root-tight-split-independent-policy-controls-v1.json',
    '--ancestor-seed', 'outputs/n26-candidate-root28-checked-extended-robust-support-forest-diagnosis-v6.json',
    '--old-full-diagnosis', 'outputs/n26-candidate-full134rod-supplemental-leaf-energy-diagnosis-v1.json',
    '--old-full-controls', 'outputs/n26-full134rod-supplemental-independent-arithmetic-controls-v1.json',
    '--prior-diagnosis', 'outputs/n26-candidate-newest-full134rod-robust-descendant-energy-diagnosis-v1.json',
    '--prior-controls', 'outputs/n26-newest-full134rod-robust-descendant-independent-controls-v1.json',
    '--correlated-diagnosis', 'outputs/n26-candidate-full134rod-correlated-supplemental-leaf-diagnosis-v1.json',
    '--correlated-controls', 'outputs/n26-full134rod-correlated-supplemental-independent-controls-v1.json',
    '--old-minimax-diagnosis', 'outputs/n26-candidate-full134rod-minimax-relaxation-diagnosis-v1.json',
    '--old-minimax-controls', 'outputs/n26-full134rod-minimax-relaxation-independent-controls-v1.json',
    '--balanced-diagnosis', 'outputs/n26-candidate-balanced-full134rod-minimax-diagnosis-v1.json',
    '--balanced-controls', 'outputs/n26-balanced-full134rod-minimax-independent-controls-v1.json',
    '--neighborhood-diagnosis', 'outputs/n26-candidate-balanced-full134rod-proper-neighborhood-diagnosis-v1.json',
    '--neighborhood-controls', 'outputs/n26-balanced-full134rod-proper-neighborhood-independent-controls-v1.json',
    '--mode-controls', 'outputs/n26-mixed-old92-full134rod-forest-mode-independent-controls-v1.json',
    '--partition-controls', 'outputs/n26-preserved-closed-subbox-partition-independent-controls-v1.json',
    '--latest-forest', $taskLatest, '--latest-controls', $taskLatestControls
)
& $taskPython work/continue_checked_root28_full134rod_intersections.py @taskBoundArgs --max-targets 64 --report $taskDiagnosis
if ($LASTEXITCODE -ne 0) {
    throw 'Actual v8 preserved full134rod continuation failed. Independent controls not started.'
}
& $taskPython work/test_checked_root28_full134rod_intersections.py @taskBoundArgs --diagnosis $taskDiagnosis --report $taskReport
if ($LASTEXITCODE -ne 0) {
    throw 'Actual newest mixed intersection controls failed. Preserve all evidence; no geometry admission.'
}
