param(
    [Parameter(Mandatory=$true)][int]$ProducerProcessId,
    [Parameter(Mandatory=$true)][string]$ProducerStartUtc,
    [Parameter(Mandatory=$true)][string]$PythonExecutable
)
$ErrorActionPreference = 'Stop'
$taskProgram = 'work/n26_selected_current_physical_reuse_v1.py'
$taskBatch = 'outputs/n26-current351-failed77-preserved-diagonal-refinement-diagnostic-v1.json'
$taskControls = 'outputs/n26-current351-failed77-preserved-diagonal-refinement-independent-controls-v1.json'
$taskJoin = 'outputs/n26-root25-current351-failed77-preserved-diagonal-composition-v1.json'
$taskFinal = 'outputs/n26-root25-current351-failed77-preserved-diagonal-independent-controls-v1.json'
foreach ($taskOutput in @($taskControls,$taskJoin,$taskFinal)) {
    if (Test-Path -LiteralPath $taskOutput) { throw 'Preserve selected outputs; do not repeat completed/failed actions.' }
}
$taskProducer = [System.Diagnostics.Process]::GetProcessById($ProducerProcessId)
if ($taskProducer.StartTime.ToUniversalTime().ToString('o') -cne $ProducerStartUtc) {
    throw 'Selected primary PID reused or exact process identity changed.'
}
$taskProducerHandle = $taskProducer.Handle
while (-not $taskProducer.WaitForExit(30000)) { $taskProducer.Refresh() }
if ($taskProducer.ExitCode -ne 0) { throw 'Actual selected primary failed; independent action not started.' }
if (-not (Test-Path -LiteralPath $taskBatch)) { throw 'Selected primary exited without an actual diagnosis.' }
$taskContext = @(
    '--selection','failed-refine','--parts','32',
    '--seed','outputs/n26-root25-current530-expanded-reuse256-composition-v2.json',
    '--seed-sha256','ba69850bb2c562badbfe38408d166e48548e4d4d6a45b68e85fa6ef9aaba2b61',
    '--seed-controls','outputs/n26-root25-current530-expanded-reuse256-independent-controls-v2.json',
    '--seed-controls-sha256','aa6b1fd08dd52f629e67e20d359af1e9b0b3078bf409cf0baff5d182b70f6599',
    '--expected-open','351','--expected-supports','27',
    '--parameter-batch','outputs/n26-current530-expanded-physical-reuse256-diagnostic-v2.json',
    '--parameter-batch-sha256','081ea375f0005fb63900ef0f128bd6d753fe6b1f9702c4efb938cb290069895b',
    '--parameter-controls','outputs/n26-current530-expanded-physical-reuse256-independent-controls-v2.json',
    '--parameter-controls-sha256','3045c12e5fedcc5ee02a06cf886eb82aea84aa57c02582bf58fc0112c24d7d45'
)
$taskBatchDigest = (Get-FileHash -LiteralPath $taskBatch -Algorithm SHA256).Hash.ToLowerInvariant()
& $PythonExecutable -u $taskProgram --action check @taskContext --diagnosis $taskBatch --diagnosis-sha256 $taskBatchDigest --report $taskControls
if ($LASTEXITCODE -ne 0) { throw 'Selected actual independent math failed; do not compose or repeat the primary.' }
$taskControlsDigest = (Get-FileHash -LiteralPath $taskControls -Algorithm SHA256).Hash.ToLowerInvariant()
$taskJoinContext = @('--batch',$taskBatch,'--batch-sha256',$taskBatchDigest,
                     '--batch-controls',$taskControls,'--batch-controls-sha256',$taskControlsDigest)
& $PythonExecutable -u $taskProgram --action compose @taskContext @taskJoinContext --report $taskJoin
if ($LASTEXITCODE -ne 0) { throw 'Selected arithmetic composition failed; no new count adopted.' }
$taskJoinDigest = (Get-FileHash -LiteralPath $taskJoin -Algorithm SHA256).Hash.ToLowerInvariant()
& $PythonExecutable -u $taskProgram --action final @taskContext @taskJoinContext --diagnosis $taskJoin --diagnosis-sha256 $taskJoinDigest --report $taskFinal
if ($LASTEXITCODE -ne 0) { throw 'Selected actual independent retention failed; composition is not a paired head.' }
Write-Output 'Selected failed77 exact math and independent arithmetic retention complete; latest geometry/global proof remains pending.'
