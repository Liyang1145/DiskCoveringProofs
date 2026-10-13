param(
    [Parameter(Mandatory=$true)][int]$ProducerProcessId,
    [Parameter(Mandatory=$true)][string]$ProducerStartUtc,
    [Parameter(Mandatory=$true)][string]$PythonExecutable
)
$ErrorActionPreference = 'Stop'
$taskBatch = 'outputs/n26-current530-expanded-physical-reuse256-diagnostic-v2.json'
$taskControls = 'outputs/n26-current530-expanded-physical-reuse256-independent-controls-v2.json'
$taskJoin = 'outputs/n26-root25-current530-expanded-reuse256-composition-v2.json'
$taskFinal = 'outputs/n26-root25-current530-expanded-reuse256-independent-controls-v2.json'
foreach ($taskOutput in @($taskControls,$taskJoin,$taskFinal)) {
    if (Test-Path -LiteralPath $taskOutput) { throw 'Preserve completed/failed expanded outputs; do not repeat.' }
}
$taskProducer = [System.Diagnostics.Process]::GetProcessById($ProducerProcessId)
if ($taskProducer.StartTime.ToUniversalTime().ToString('o') -cne $ProducerStartUtc) {
    throw 'Expanded primary PID reused or exact producer start identity changed.'
}
$taskProducerHandle = $taskProducer.Handle
while (-not $taskProducer.WaitForExit(30000)) {
    $taskProducer.Refresh()
}
if ($taskProducer.ExitCode -ne 0) { throw 'Actual expanded primary failed; independent math not started.' }
if (-not (Test-Path -LiteralPath $taskBatch)) { throw 'Actual expanded primary exited without its diagnosis.' }
$taskContext = @(
    '--seed','outputs/n26-root25-current538-failed-joint-physical-composition-v1.json',
    '--seed-sha256','de2a583077d85c25483f893d0593d6e8878ebaaf78aade3268feea1507542a47',
    '--seed-controls','outputs/n26-root25-current538-failed-joint-physical-independent-controls-v1.json',
    '--seed-controls-sha256','81610c12be15e48a470c42a31b553c093e8474ac5cde19408c23ee8a00e07683',
    '--expected-open','530','--expected-supports','27'
)
$taskBatchDigest = (Get-FileHash -LiteralPath $taskBatch -Algorithm SHA256).Hash.ToLowerInvariant()
& $PythonExecutable -u work/test_expanded_current_physical_support_reuse_v2.py @taskContext --diagnosis $taskBatch --diagnosis-sha256 $taskBatchDigest --report $taskControls
if ($LASTEXITCODE -ne 0) { throw 'Actual expanded independent math failed; preserve primary and failures.' }
$taskControlsDigest = (Get-FileHash -LiteralPath $taskControls -Algorithm SHA256).Hash.ToLowerInvariant()
$taskJoinContext = @(
    '--batch',$taskBatch,'--batch-sha256',$taskBatchDigest,
    '--batch-controls',$taskControls,'--batch-controls-sha256',$taskControlsDigest
)
& $PythonExecutable -u work/compose_expanded_current_physical_support_reuse_v2.py @taskContext @taskJoinContext --report $taskJoin
if ($LASTEXITCODE -ne 0) { throw 'Actual expanded arithmetic join failed; do not adopt a new OPEN count.' }
$taskJoinDigest = (Get-FileHash -LiteralPath $taskJoin -Algorithm SHA256).Hash.ToLowerInvariant()
& $PythonExecutable -u work/test_expanded_current_physical_reuse_composition_v2.py @taskContext @taskJoinContext --diagnosis $taskJoin --diagnosis-sha256 $taskJoinDigest --report $taskFinal
if ($LASTEXITCODE -ne 0) { throw 'Actual expanded independent join failed; new OPEN count is not paired.' }
Write-Output 'Expanded whole math and independent arithmetic retention complete; geometry/global proof remains pending.'
