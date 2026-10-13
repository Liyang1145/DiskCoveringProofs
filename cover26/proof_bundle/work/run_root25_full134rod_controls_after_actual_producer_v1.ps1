param(
    [Parameter(Mandatory=$true)][int]$ProducerProcessId,
    [Parameter(Mandatory=$true)][string]$ProducerStartUtc,
    [string]$PythonExecutable = 'C:/热爱单机但萌新/dependencies/python/python.exe'
)
$ErrorActionPreference = 'Stop'
$taskDiagnosis = 'outputs/n26-candidate-root25-preserved-full134rod-regions-forest-diagnosis-v4.json'
$taskControls = 'outputs/n26-candidate-root25-preserved-full134rod-regions-independent-controls-v1.json'
if (Test-Path -LiteralPath $taskControls) { throw 'Preserve completed or failed root25 controls; do not duplicate.' }
$taskProducer = [System.Diagnostics.Process]::GetProcessById($ProducerProcessId)
if ($taskProducer.StartTime.ToUniversalTime().ToString('o') -cne $ProducerStartUtc) {
    throw 'Root25 producer PID has been reused or names a different actual process.'
}
$taskProducerHandle = $taskProducer.Handle
$taskProducer.WaitForExit()
if ($taskProducer.ExitCode -ne 0) { throw 'Actual root25 arithmetic producer failed; controls not started.' }
if (-not (Test-Path -LiteralPath $taskDiagnosis)) { throw 'Actual root25 producer exited without its original diagnosis.' }
& $PythonExecutable work/test_root25_preserved_full134rod_regions.py --diagnosis $taskDiagnosis --report $taskControls
if ($LASTEXITCODE -ne 0) { throw 'Actual root25 independent arithmetic controls failed. Preserve producer; do not repeat it.' }
Write-Output 'Root25 actual preserved full134rod successor and independent arithmetic controls complete; source geometry/current admission remains required.'
