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
    $taskPredecessorInfo.CommandLine -notmatch 'probe_latest878_physical_donor_sweep\.py.*--limit 128') {
    throw 'Exact live physical128 primary was not identified; no checking or join started.'
}
$taskBatchPath = Join-Path $taskWorkspace 'outputs/n26-latest878-physical-donor-whole-leaf-sweep-diagnostic-v1.json'
$taskControlsPath = Join-Path $taskWorkspace 'outputs/n26-latest878-physical-donor-whole-leaf-sweep-independent-controls-v1.json'
$taskJoinPath = Join-Path $taskWorkspace 'outputs/n26-root25-latest-physical128-donor-composition-v1.json'
$taskFinalPath = Join-Path $taskWorkspace 'outputs/n26-root25-latest-physical128-donor-independent-controls-v1.json'
$taskBatchTester = Join-Path $taskWorkspace 'work/test_latest878_physical_donor_sweep.py'
$taskJoinProducer = Join-Path $taskWorkspace 'work/compose_latest878_physical_donor_sweep.py'
$taskJoinTester = Join-Path $taskWorkspace 'work/test_latest878_physical_donor_composition.py'
$taskExecutorHashes = @{}
foreach ($taskExecutor in @($taskBatchTester, $taskJoinProducer, $taskJoinTester)) {
    $taskExecutorHashes[$taskExecutor] = (Get-FileHash -LiteralPath $taskExecutor -Algorithm SHA256).Hash
}
foreach ($taskDestination in @($taskControlsPath, $taskJoinPath, $taskFinalPath)) {
    if (Test-Path -LiteralPath $taskDestination) { throw 'Existing completed downstream phase must not be repeated.' }
}
[pscustomobject]@{
    ExactLivePhysical128PrimaryHandleAcquired = $true
    PredecessorProcessId = $PredecessorProcessId
    PredecessorStartUtc = $taskObservedStart
    IndependentPhaseStarted = $false
    ArithmeticCompositionStarted = $false
    FormalGeometryAdmission = $false
} | ConvertTo-Json -Compress
while (-not $taskPredecessor.WaitForExit(30000)) {
    # An observation timeout never restarts the live exact predecessor.
}
if ($taskPredecessor.ExitCode -ne 0) {
    throw 'Physical128 primary failed; preserve all checkpoints; no independent phase started.'
}
if (-not (Test-Path -LiteralPath $taskBatchPath)) {
    throw 'Successful primary lacks its actual completed batch report.'
}
foreach ($taskExecutor in @($taskBatchTester, $taskJoinProducer, $taskJoinTester)) {
    if ((Get-FileHash -LiteralPath $taskExecutor -Algorithm SHA256).Hash -ne $taskExecutorHashes[$taskExecutor]) {
        throw 'Queued physical128 downstream executor changed.'
    }
}
Set-Location -LiteralPath $taskWorkspace
$taskBatchSha = (Get-FileHash -LiteralPath $taskBatchPath -Algorithm SHA256).Hash.ToLowerInvariant()
Write-Output "ACTUAL completed physical128 primary SHA256 $taskBatchSha"
& $PythonExecutable -u $taskBatchTester --diagnosis $taskBatchPath --diagnosis-sha256 $taskBatchSha --report $taskControlsPath
if ($LASTEXITCODE -ne 0) { throw 'Independent physical128 math failed; do not repeat completed primary.' }
$taskControlsSha = (Get-FileHash -LiteralPath $taskControlsPath -Algorithm SHA256).Hash.ToLowerInvariant()
Write-Output "ACTUAL completed physical128 independent controls SHA256 $taskControlsSha"
& $PythonExecutable -u $taskJoinProducer --batch-sha256 $taskBatchSha --controls-sha256 $taskControlsSha --report $taskJoinPath
if ($LASTEXITCODE -ne 0) { throw 'Physical128 arithmetic join failed; do not repeat completed batch/math controls.' }
$taskJoinSha = (Get-FileHash -LiteralPath $taskJoinPath -Algorithm SHA256).Hash.ToLowerInvariant()
Write-Output "ACTUAL completed physical128 arithmetic join SHA256 $taskJoinSha"
& $PythonExecutable -u $taskJoinTester --batch-sha256 $taskBatchSha --controls-sha256 $taskControlsSha `
    --diagnosis $taskJoinPath --diagnosis-sha256 $taskJoinSha --report $taskFinalPath
if ($LASTEXITCODE -ne 0) { throw 'Independent arithmetic join failed; do not repeat its completed producer.' }
Write-Output 'ACTUAL physical128 batch/math controls AND arithmetic composition/independent controls terminal0; no current/global geometry adoption.'
