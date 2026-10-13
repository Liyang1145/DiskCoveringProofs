param(
    [Parameter(Mandatory = $true)]
    [string]$PythonExecutable,
    [Parameter(Mandatory = $true)]
    [int]$PredecessorProcessId,
    [Parameter(Mandatory = $true)]
    [string]$PredecessorStartUtc
)
$ErrorActionPreference = 'Stop'
$workspace = 'C:/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$predecessor = [System.Diagnostics.Process]::GetProcessById($PredecessorProcessId)
$predecessorHandle = $predecessor.Handle
$observedStart = $predecessor.StartTime.ToUniversalTime().ToString('o')
$predecessorInfo = Get-CimInstance Win32_Process -Filter "ProcessId=$PredecessorProcessId"
if ($predecessor.HasExited -or $observedStart -ne $PredecessorStartUtc -or
    $predecessorInfo.CommandLine -notmatch 'run_midarc_source_geometry_after_live_mixed_chain_v1\.ps1') {
    throw 'Exact live midarc source-pair predecessor was not identified. No current started.'
}
[pscustomobject]@{
    ExactLiveMidarcSourcePairHandleAcquired = $true
    PredecessorProcessId = $PredecessorProcessId
    PredecessorStartUtc = $observedStart
    MidarcCurrentAdmissionStarted = $false
    WaitingOnlyForActualCompleteMidarcOwnAndSameMainPublication = $true
} | ConvertTo-Json
while (-not $predecessor.WaitForExit(30000)) {
    # One-shot exact process dependency; never restart on observation timeout.
    # No complete-current executor runs during this wait.
}
if ($predecessor.ExitCode -ne 0) {
    throw 'Actual midarc source-pair predecessor failed. Preserve it; no current admission started.'
}
$ownPath = Join-Path $workspace 'outputs/n26-mixed-after-six-midarc-source-geometry-v1/VERIFIED.json'
$publicationPath = Join-Path $workspace 'outputs/n26-mixed-after-six-midarc-source-geometry-published-replay-v1.json'
foreach ($required in @($ownPath, $publicationPath)) {
    if (-not (Test-Path -LiteralPath $required)) {
        throw 'Successful source predecessor lacks its actual own/publication pair. No current started.'
    }
}
if ((Get-FileHash -LiteralPath $ownPath -Algorithm SHA256).Hash -ne
    (Get-FileHash -LiteralPath $publicationPath -Algorithm SHA256).Hash) {
    throw 'Actual completed midarc own/publication pair differs. No current started.'
}
Set-Location -LiteralPath $workspace
& (Join-Path $workspace 'work/run_midarc_source_serial_current_final_v1.ps1') `
    -PythonExecutable $PythonExecutable
