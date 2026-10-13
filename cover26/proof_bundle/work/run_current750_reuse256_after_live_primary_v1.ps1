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
    $taskPredecessorInfo.CommandLine -notmatch 'probe_current_physical_support_reuse\.py.*--expected-open 750.*--limit 256') {
    throw 'Exact live CURRENT750 reuse256 primary was not identified; no downstream phase started.'
}
$taskParentArguments = @(
    '--seed', 'outputs/n26-root25-latest-physical128-donor-composition-v1.json',
    '--seed-sha256', 'cdcf4af2f24410908ce9bd59f82d521d4d62927e3fa97f631dc1d191ae59d0d2',
    '--seed-controls', 'outputs/n26-root25-latest-physical128-donor-independent-controls-v1.json',
    '--seed-controls-sha256', '8003d10ab61c9cea417f658f1946d1cd5f2578ec905f3cf6e15e33b0698a6275',
    '--expected-open', '750'
)
$taskBatchPath = Join-Path $taskWorkspace 'outputs/n26-current750-physical-support-reuse256-diagnostic-v1.json'
$taskControlsPath = Join-Path $taskWorkspace 'outputs/n26-current750-physical-support-reuse256-independent-controls-v1.json'
$taskJoinPath = Join-Path $taskWorkspace 'outputs/n26-root25-current750-physical-reuse256-composition-v1.json'
$taskFinalPath = Join-Path $taskWorkspace 'outputs/n26-root25-current750-physical-reuse256-independent-controls-v1.json'
$taskTester = Join-Path $taskWorkspace 'work/test_current_physical_support_reuse.py'
$taskComposer = Join-Path $taskWorkspace 'work/compose_current_physical_support_reuse.py'
$taskJoinTester = Join-Path $taskWorkspace 'work/test_current_physical_reuse_composition.py'
$taskExecutorHashes = @{}
foreach ($taskExecutor in @($taskTester, $taskComposer, $taskJoinTester)) {
    $taskExecutorHashes[$taskExecutor] = (Get-FileHash -LiteralPath $taskExecutor -Algorithm SHA256).Hash
}
foreach ($taskDestination in @($taskControlsPath, $taskJoinPath, $taskFinalPath)) {
    if (Test-Path -LiteralPath $taskDestination) { throw 'Existing successful downstream phase must not be repeated.' }
}
[pscustomobject]@{
    ExactLiveCurrent750Reuse256PrimaryHandleAcquired = $true
    PredecessorProcessId = $PredecessorProcessId
    PredecessorStartUtc = $taskObservedStart
    IndependentPhaseStarted = $false
    ArithmeticCompositionStarted = $false
    FormalGeometryAdmission = $false
} | ConvertTo-Json -Compress
while (-not $taskPredecessor.WaitForExit(30000)) {
    # Observation timeout is not failure and never restarts the exact primary.
}
if ($taskPredecessor.ExitCode -ne 0) {
    throw 'CURRENT reuse256 primary failed; preserve checkpoints; no independent phase started.'
}
if (-not (Test-Path -LiteralPath $taskBatchPath)) {
    throw 'Successful CURRENT reuse256 primary lacks its actual completed report.'
}
foreach ($taskExecutor in @($taskTester, $taskComposer, $taskJoinTester)) {
    if ((Get-FileHash -LiteralPath $taskExecutor -Algorithm SHA256).Hash -ne $taskExecutorHashes[$taskExecutor]) {
        throw 'Queued CURRENT reuse256 downstream executor changed.'
    }
}
Set-Location -LiteralPath $taskWorkspace
$taskBatchSha = (Get-FileHash -LiteralPath $taskBatchPath -Algorithm SHA256).Hash.ToLowerInvariant()
Write-Output "ACTUAL completed CURRENT750 reuse256 primary SHA256 $taskBatchSha"
& $PythonExecutable -u $taskTester @taskParentArguments --diagnosis $taskBatchPath --diagnosis-sha256 $taskBatchSha --report $taskControlsPath
if ($LASTEXITCODE -ne 0) { throw 'Independent CURRENT256 math failed; do not repeat completed primary.' }
$taskControlsSha = (Get-FileHash -LiteralPath $taskControlsPath -Algorithm SHA256).Hash.ToLowerInvariant()
Write-Output "ACTUAL completed CURRENT750 reuse256 independent controls SHA256 $taskControlsSha"
$taskBatchArguments = @(
    '--batch', $taskBatchPath, '--batch-sha256', $taskBatchSha,
    '--batch-controls', $taskControlsPath, '--batch-controls-sha256', $taskControlsSha
)
& $PythonExecutable -u $taskComposer @taskParentArguments @taskBatchArguments --report $taskJoinPath
if ($LASTEXITCODE -ne 0) { throw 'CURRENT256 arithmetic join failed; preserve completed batch/math pair.' }
$taskJoinSha = (Get-FileHash -LiteralPath $taskJoinPath -Algorithm SHA256).Hash.ToLowerInvariant()
Write-Output "ACTUAL completed CURRENT750 reuse256 arithmetic join SHA256 $taskJoinSha"
& $PythonExecutable -u $taskJoinTester @taskParentArguments @taskBatchArguments `
    --diagnosis $taskJoinPath --diagnosis-sha256 $taskJoinSha --report $taskFinalPath
if ($LASTEXITCODE -ne 0) { throw 'Independent CURRENT256 join failed; do not repeat completed composer.' }
Write-Output 'ACTUAL CURRENT750 reuse256 batch/math AND arithmetic composition/independent controls terminal0; no current/global geometry adoption.'
