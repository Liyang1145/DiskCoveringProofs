param(
    [Parameter(Mandatory=$true)][string]$taskCurrentAuditPath,
    [Parameter(Mandatory=$true)][string]$taskCurrentFinalPath
)

$ErrorActionPreference = 'Stop'
$taskDependencyFolder = -join ([char[]]@(0x70ED,0x7231,0x5355,0x673A,0x4F46,0x840C,0x65B0))
$taskPython = 'C:/'+$taskDependencyFolder+'/dependencies/python/python.exe'
$taskLatest = 'outputs/n26-candidate-root28-checked-support-cost-forest-diagnosis-v8.json'
$taskLatestControls = 'outputs/n26-candidate-root28-checked-support-cost-independent-controls-v4.json'
$taskDiagnosis = 'outputs/n26-candidate-root28-grown-full134rod-intersection-forest-diagnosis-v9.json'
$taskReport = 'outputs/n26-candidate-root28-grown-full134rod-intersection-independent-controls-v1.json'
$taskNarrowDiagnosis = 'outputs/n26-candidate-root28-preserved-full134rod-intersection-forest-diagnosis-v9.json'
$taskNarrowReport = 'outputs/n26-candidate-root28-preserved-full134rod-intersection-independent-controls-v1.json'
$taskFixturePath = 'outputs/n26-grown-full134rod-intersection-OLD-fixture-independent-controls-v1.json'
foreach ($taskExisting in @($taskDiagnosis,$taskReport,$taskNarrowDiagnosis,$taskNarrowReport)) {
    if (Test-Path -LiteralPath $taskExisting) {
        throw 'A new successor or narrower history already exists. Preserve it; do not reset from v8.'
    }
}
if (-not (Test-Path -LiteralPath $taskLatest) -or -not (Test-Path -LiteralPath $taskLatestControls)) {
    throw 'Original latest v8 and its automatic actual independent controls are not both complete.'
}
$taskLiveWorkers = Get-CimInstance Win32_Process | Where-Object {
    $_.Name -eq 'python.exe' -and $_.CommandLine -match
    '(continue_checked_support_cost_forest|test_checked_support_cost_continuation|continue_checked_root28_full134rod_intersections|test_checked_root28_full134rod_intersections|continue_checked_root28_grown_full134rod_intersections|test_checked_root28_grown_full134rod_intersections)\.py'
}
if ($taskLiveWorkers) {
    throw 'An original or newer root28 producer/control worker is still live. Do not overlap or reset it.'
}
$taskFinal = Get-Content -LiteralPath $taskCurrentFinalPath -Encoding UTF8 -Raw | ConvertFrom-Json
$taskAuditHash = (Get-FileHash -LiteralPath $taskCurrentAuditPath -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskFinal.schema -ne 'N26-independent-final-current-inventory-rehash-v1' -or
    $taskFinal.all_current_file_digests_rehashed -ne $true -or
    $taskFinal.current_audit_sha256 -cne $taskAuditHash -or
    $taskFinal.global_lower_bound_proved -ne $false -or
    $taskFinal.global_optimality_proved -ne $false) {
    throw 'Supply the genuinely newest completed formal audit and matching actual independent final.'
}
$taskFixture = Get-Content -LiteralPath $taskFixturePath -Encoding UTF8 -Raw | ConvertFrom-Json
$taskProducerHash = (Get-FileHash -LiteralPath 'work/continue_checked_root28_grown_full134rod_intersections.py' -Algorithm SHA256).Hash.ToLowerInvariant()
$taskTesterHash = (Get-FileHash -LiteralPath 'work/test_checked_root28_grown_full134rod_intersections.py' -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskFixture.schema -ne 'N26-independent-grown-full134rod-intersection-OLD-forest-fixture-controls-v1' -or
    $taskFixture.tested_distinct_grown_interface_sha256 -cne $taskProducerHash -or
    $taskFixture.tested_own_independent_arithmetic_checker_sha256 -cne $taskTesterHash -or
    $taskFixture.fixture_is_NOT_latest_v8_successor_or_current_source_history_geometry_acceptance -ne $true -or
    $taskFixture.actual_grown_operator_OLD_fixture_guards_rejected.Count -ne 9 -or
    $taskFixture.new_geometric_payments -ne 0) {
    throw 'Actual grown operator fixture controls are missing or stale; they do not replace latest-v8 controls.'
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
    '--latest-forest', $taskLatest, '--latest-controls', $taskLatestControls,
    '--grown-diagnosis', 'outputs/n26-candidate-source-root-grown-full134rod-regions-diagnosis-v1.json',
    '--grown-controls', 'outputs/n26-source-root-grown-full134rod-regions-independent-controls-v1.json',
    '--grown-selection-controls', 'outputs/n26-grown-full134rod-region-selection-independent-controls-v1.json',
    '--grown-current-audit', 'outputs/n26-twenty-fourth-conditional-current-audit-v24-sparse-v1-strict-with-owned8-scope.json'
)
& $taskPython work/continue_checked_root28_grown_full134rod_intersections.py @taskBoundArgs --max-targets 4096 --report $taskDiagnosis
if ($LASTEXITCODE -ne 0) {
    throw 'Actual newest grown-region continuation failed. Preserve evidence; controls not started.'
}
& $taskPython work/test_checked_root28_grown_full134rod_intersections.py @taskBoundArgs --diagnosis $taskDiagnosis --report $taskReport
if ($LASTEXITCODE -ne 0) {
    throw 'Actual newest grown-region independent controls failed. No geometric admission or payments.'
}
