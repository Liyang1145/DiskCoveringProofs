param(
    [Parameter(Mandatory = $true)]
    [string]$PythonExecutable,
    [Parameter(Mandatory = $true)]
    [int]$PredecessorProcessId,
    [Parameter(Mandatory = $true)]
    [string]$PredecessorStartUtc
)
$ErrorActionPreference = 'Stop'
$taskWorkspace = 'C:/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$taskPredecessor = [System.Diagnostics.Process]::GetProcessById($PredecessorProcessId)
$taskPredecessorHandle = $taskPredecessor.Handle
$taskObservedStart = $taskPredecessor.StartTime.ToUniversalTime().ToString('o')
$taskPredecessorInfo = Get-CimInstance Win32_Process -Filter "ProcessId=$PredecessorProcessId"
if ($taskPredecessor.HasExited -or $taskObservedStart -ne $PredecessorStartUtc -or
    $taskPredecessorInfo.CommandLine -notmatch 'test_latest918_joint_origin_stress_batch\.py') {
    throw 'Exact live fresh-batch independent checker was not identified; no arithmetic join started.'
}
$taskBatchPath = Join-Path $taskWorkspace 'outputs/n26-latest918-joint-origin-fresh-stress-batch-diagnostic-v1.json'
$taskControlsPath = Join-Path $taskWorkspace 'outputs/n26-latest918-joint-origin-fresh-stress-batch-independent-controls-v1.json'
$taskJoinPath = Join-Path $taskWorkspace 'outputs/n26-root25-latest910-checked-joint-origin-batch-composition-v1.json'
$taskFinalPath = Join-Path $taskWorkspace 'outputs/n26-root25-latest910-checked-joint-origin-batch-independent-controls-v1.json'
$taskProducerPath = Join-Path $taskWorkspace 'work/compose_latest918_joint_origin_stress_batch.py'
$taskTesterPath = Join-Path $taskWorkspace 'work/test_latest918_joint_origin_batch_composition.py'
$taskProducerSha = (Get-FileHash -LiteralPath $taskProducerPath -Algorithm SHA256).Hash
$taskTesterSha = (Get-FileHash -LiteralPath $taskTesterPath -Algorithm SHA256).Hash
if (Test-Path -LiteralPath $taskJoinPath) { throw 'Existing arithmetic composition must not be repeated.' }
if (Test-Path -LiteralPath $taskFinalPath) { throw 'Existing independent arithmetic composition must not be repeated.' }
[pscustomobject]@{
    ExactLiveFreshBatchCheckerHandleAcquired = $true
    PredecessorProcessId = $PredecessorProcessId
    PredecessorStartUtc = $taskObservedStart
    ArithmeticJoinStarted = $false
    FormalGeometryAdmission = $false
} | ConvertTo-Json -Compress
while (-not $taskPredecessor.WaitForExit(30000)) {
    # An observation timeout is not failure and never triggers a restart.
}
if ($taskPredecessor.ExitCode -ne 0) {
    throw 'Actual fresh-batch independent checker failed; no arithmetic join started.'
}
foreach ($taskRequired in @($taskBatchPath, $taskControlsPath)) {
    if (-not (Test-Path -LiteralPath $taskRequired)) {
        throw 'Successful checker lacks an actual completed batch/control pair.'
    }
}
$taskBatchSha = (Get-FileHash -LiteralPath $taskBatchPath -Algorithm SHA256).Hash.ToLowerInvariant()
$taskControlsSha = (Get-FileHash -LiteralPath $taskControlsPath -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskBatchSha -ne '2d17d01e3db16cbc99c91f7af50c47ae3679180ce5910495cceb997717ad4606') {
    throw 'Actual completed fresh eight-leaf batch changed.'
}
$taskControls = Get-Content -LiteralPath $taskControlsPath -Raw -Encoding UTF8 | ConvertFrom-Json
if ($taskControls.diagnosis_sha256 -ne $taskBatchSha -or
    $taskControls.prospective_arithmetic_remaining_OPEN_after_independent_join -ne 910 -or
    @($taskControls.actual_new_strict_whole_leaf_indices).Count -ne 8) {
    throw 'Actual independent checker does not bind the expected eight complete two-owner exclusions.'
}
if ((Get-FileHash -LiteralPath $taskProducerPath -Algorithm SHA256).Hash -ne $taskProducerSha -or
    (Get-FileHash -LiteralPath $taskTesterPath -Algorithm SHA256).Hash -ne $taskTesterSha) {
    throw 'Queued arithmetic composition executor changed.'
}
Set-Location -LiteralPath $taskWorkspace
& $PythonExecutable -u $taskProducerPath --batch-sha256 $taskBatchSha --controls-sha256 $taskControlsSha --report $taskJoinPath
if ($LASTEXITCODE -ne 0) { throw 'Fresh arithmetic composition failed; preserve its failure.' }
$taskJoinSha = (Get-FileHash -LiteralPath $taskJoinPath -Algorithm SHA256).Hash.ToLowerInvariant()
Write-Output "ACTUAL fresh checked arithmetic primary SHA256 $taskJoinSha"
& $PythonExecutable -u $taskTesterPath --batch-sha256 $taskBatchSha --controls-sha256 $taskControlsSha `
    --diagnosis $taskJoinPath --diagnosis-sha256 $taskJoinSha --report $taskFinalPath
if ($LASTEXITCODE -ne 0) { throw 'Independent composition failed; do not repeat its completed primary.' }
Write-Output 'ACTUAL latest910 arithmetic composition AND independent controls terminal0; no current/global geometry adoption.'
