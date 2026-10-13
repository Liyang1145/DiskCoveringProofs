param(
    [Parameter(Mandatory=$true)][int]$ProducerProcessId,
    [Parameter(Mandatory=$true)][string]$ProducerStartUtc,
    [Parameter(Mandatory=$true)][string]$PythonExecutable
)
$ErrorActionPreference = 'Stop'
$taskProgram = 'work/n26_selected_current_physical_reuse_v1.py'
$taskBatch = 'outputs/n26-current347-untried274-physical-reuse-diagnostic-v1.json'
$taskControls = 'outputs/n26-current347-untried274-physical-reuse-independent-controls-v1.json'
$taskJoin = 'outputs/n26-root25-current347-untried274-physical-composition-v1.json'
$taskFinal = 'outputs/n26-root25-current347-untried274-physical-independent-controls-v1.json'
foreach ($taskOutput in @($taskControls,$taskJoin,$taskFinal)) {
    if (Test-Path -LiteralPath $taskOutput) { throw 'Preserve actual untried outputs; never repeat completed/failed actions.' }
}
$taskProducer = [System.Diagnostics.Process]::GetProcessById($ProducerProcessId)
if ($taskProducer.StartTime.ToUniversalTime().ToString('o') -cne $ProducerStartUtc) {
    throw 'Untried primary PID reused or actual start identity changed.'
}
$taskProducerHandle = $taskProducer.Handle
while (-not $taskProducer.WaitForExit(30000)) { $taskProducer.Refresh() }
if ($taskProducer.ExitCode -ne 0) { throw 'Actual untried primary failed; independent check not started.' }
if (-not (Test-Path -LiteralPath $taskBatch)) { throw 'Untried primary completed without its diagnosis.' }
$taskContext = @(
    '--selection','untried','--parts','16',
    '--seed','outputs/n26-root25-current351-failed77-preserved-diagonal-composition-v1.json',
    '--seed-sha256','4083e23465e71ce6098f3aa48c40c6769ecfabd8ba0ab2665ded903b905f637c',
    '--seed-controls','outputs/n26-root25-current351-failed77-preserved-diagonal-independent-controls-v1.json',
    '--seed-controls-sha256','19aff52c8f9cb65cb16b238950583a3eb2b940e795cbab4aef8218ea7d4cb282',
    '--expected-open','347','--expected-supports','27',
    '--parameter-batch','outputs/n26-current530-expanded-physical-reuse256-diagnostic-v2.json',
    '--parameter-batch-sha256','081ea375f0005fb63900ef0f128bd6d753fe6b1f9702c4efb938cb290069895b',
    '--parameter-controls','outputs/n26-current530-expanded-physical-reuse256-independent-controls-v2.json',
    '--parameter-controls-sha256','3045c12e5fedcc5ee02a06cf886eb82aea84aa57c02582bf58fc0112c24d7d45'
)
$taskBatchDigest = (Get-FileHash -LiteralPath $taskBatch -Algorithm SHA256).Hash.ToLowerInvariant()
& $PythonExecutable -u $taskProgram --action check @taskContext --diagnosis $taskBatch --diagnosis-sha256 $taskBatchDigest --report $taskControls
if ($LASTEXITCODE -ne 0) { throw 'Actual untried independent math failed; preserve all failed trials.' }
$taskBatchData = Get-Content -LiteralPath $taskBatch -Raw -Encoding UTF8 | ConvertFrom-Json
if ($taskBatchData.new_strict_whole_leaf_indices.Count -eq 0) {
    Write-Output 'All untried attempts independently checked; zero new exclusions, no composition and current347 retained.'
    return
}
$taskControlsDigest = (Get-FileHash -LiteralPath $taskControls -Algorithm SHA256).Hash.ToLowerInvariant()
$taskJoinContext = @('--batch',$taskBatch,'--batch-sha256',$taskBatchDigest,
                     '--batch-controls',$taskControls,'--batch-controls-sha256',$taskControlsDigest)
& $PythonExecutable -u $taskProgram --action compose @taskContext @taskJoinContext --report $taskJoin
if ($LASTEXITCODE -ne 0) { throw 'Untried checked composition failed; do not adopt its count.' }
$taskJoinDigest = (Get-FileHash -LiteralPath $taskJoin -Algorithm SHA256).Hash.ToLowerInvariant()
& $PythonExecutable -u $taskProgram --action final @taskContext @taskJoinContext --diagnosis $taskJoin --diagnosis-sha256 $taskJoinDigest --report $taskFinal
if ($LASTEXITCODE -ne 0) { throw 'Untried independent history retention failed; count is not paired.' }
Write-Output 'Untried whole physical math and independent arithmetic retention complete; geometry/global proof still pending.'
