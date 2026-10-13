param(
    [Parameter(Mandatory=$true)][string]$taskCurrentAudit,
    [Parameter(Mandatory=$true)][string]$taskCurrentFinal
)

$ErrorActionPreference = 'Stop'
$taskDependencyFolder = -join ([char[]]@(0x70ED,0x7231,0x5355,0x673A,0x4F46,0x840C,0x65B0))
$taskPython = 'C:/'+$taskDependencyFolder+'/dependencies/python/python.exe'
$taskSource = 'outputs/n26-current-candidate-owned-forest-v8'
$taskDiagnosis = 'outputs/n26-candidate-root21-fresh-checked-positive-support-forest-diagnosis-v1.json'
$taskControls = 'outputs/n26-candidate-root21-fresh-checked-positive-support-independent-controls-v1.json'
$taskSupportData = 'outputs/n26-candidate-root28-checked-extended-robust-support-forest-diagnosis-v6.json'
$taskSupportControls = 'outputs/n26-candidate-root28-checked-robust-forest-independent-arithmetic-controls-v2.json'
foreach ($taskTarget in @($taskDiagnosis,$taskControls)) {
    if (Test-Path -LiteralPath $taskTarget) {
        throw 'A root21 history/control target already exists. Preserve it;never reset a newer partial tree.'
    }
}
$taskWorkers = Get-CimInstance Win32_Process | Where-Object {
    $_.Name -eq 'python.exe' -and $_.CommandLine -and
    ($_.CommandLine -match 'root21' -or
     ($_.CommandLine -match 'propose_fresh_checked_positive_support_forest\.py' -and
      $_.CommandLine -match '--index\s+21'))
}
if ($taskWorkers) { throw 'An actual root21 producer/control worker is live;do not overlap.' }
$taskCurrent = Get-Content -LiteralPath $taskCurrentAudit -Encoding UTF8 -Raw | ConvertFrom-Json
$taskFinal = Get-Content -LiteralPath $taskCurrentFinal -Encoding UTF8 -Raw | ConvertFrom-Json
$taskCurrentHash = (Get-FileHash -LiteralPath $taskCurrentAudit -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskFinal.current_audit_sha256 -cne $taskCurrentHash -or
    $taskFinal.all_current_file_digests_rehashed -ne $true -or
    $taskFinal.current_file_digests_rechecked -ne @($taskCurrent.files.PSObject.Properties | ForEach-Object { $_.Name }).Count -or
    $taskFinal.candidate_angle_unresolved_closed_boxes -ne $taskCurrent.candidate_angle_unresolved_closed_boxes -or
    $taskCurrent.global_lower_bound_proved -ne $false -or
    $taskCurrent.global_optimality_proved -ne $false) {
    throw 'Supply an actually completed formal current/final pair,not an unfinished enumeration layer.'
}
$taskPending = Get-Content -LiteralPath "$taskSource/PENDING-ANGLES.json" -Encoding UTF8 -Raw | ConvertFrom-Json
$taskProposal = Get-Content -LiteralPath "$taskSource/PROPOSAL.json" -Encoding UTF8 -Raw | ConvertFrom-Json
$taskHistory = Get-Content -LiteralPath "$taskSource/SOURCE-ROOT-HISTORY.json" -Encoding UTF8 -Raw | ConvertFrom-Json
$taskRoots = @($taskPending | Where-Object { $_.index -eq 21 })
$taskAttempted = @($taskProposal.forests | ForEach-Object { $_.source_OPEN_index })
$taskAttempted += @($taskHistory | ForEach-Object { $_.source_OPEN_index })
if ($taskRoots.Count -ne 1 -or $taskAttempted -contains 21) {
    throw 'Root21 is not a fresh actual source root or already has accepted history;do not reset it.'
}
& $taskPython work/propose_fresh_checked_positive_support_forest.py --resource outputs/n26-original-candidate-arithmetic-context-v1 --resource-replay outputs/n26-original-candidate-arithmetic-context-published-replay-v1.json --current-audit $taskCurrentAudit --source $taskSource --support-diagnosis $taskSupportData --support-controls $taskSupportControls --index 21 --checks 1023 --depth 384 --existing-support-tries 6 --max-supports 256 --rounds 2 --iterations 220 --report $taskDiagnosis
if ($LASTEXITCODE -ne 0) {
    throw 'Actual root21 fresh arithmetic producer failed;preserve partial evidence. Independent tests not started.'
}
& $taskPython work/test_fresh_checked_positive_support_forest_arithmetic.py --resource outputs/n26-original-candidate-arithmetic-context-v1 --resource-replay outputs/n26-original-candidate-arithmetic-context-published-replay-v1.json --source $taskSource --support-diagnosis $taskSupportData --support-controls $taskSupportControls --diagnosis $taskDiagnosis --report $taskControls
if ($LASTEXITCODE -ne 0) {
    throw 'Actual entire root21 independent arithmetic controls failed. No current geometry/payment claimed.'
}
Write-Output 'Actual root21 arithmetic and independent controls completed;full current source/model/history geometry admission STILL REQUIRED.'
