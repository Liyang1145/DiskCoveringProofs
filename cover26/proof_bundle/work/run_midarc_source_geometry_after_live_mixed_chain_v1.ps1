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
    $predecessorInfo.CommandLine -notmatch 'run_mixed_after_six_after_live_predecessor_v1\.ps1') {
    throw 'Exact live mixed-after-SIX predecessor was not identified. No midarc geometry started.'
}
[pscustomobject]@{
    ExactLiveMixedChainHandleAcquired = $true
    PredecessorProcessId = $PredecessorProcessId
    PredecessorStartUtc = $observedStart
    MidarcBuilderAndGeometryStarted = $false
    WaitingOnlyForThisActualMixedCurrentAndIndependentFinalChain = $true
} | ConvertTo-Json
while (-not $predecessor.WaitForExit(30000)) {
    # One-shot exact process dependency. No source builder, geometry main or
    # complete-current executor runs during this wait; no restart on timeout.
}
if ($predecessor.ExitCode -ne 0) {
    throw 'Actual mixed current/final predecessor failed. Preserve it; no midarc geometry started.'
}
$currentPath = Join-Path $workspace 'outputs/n26-current28-six-target-mixed-candidate-current-v1.json'
$finalPath = Join-Path $workspace 'outputs/n26-current28-six-target-mixed-candidate-independent-final-v1.json'
foreach ($required in @($currentPath, $finalPath)) {
    if (-not (Test-Path -LiteralPath $required)) {
        throw 'Successful mixed predecessor lacks its actual current/final pair. No geometry started.'
    }
}
$currentDigest = (Get-FileHash -LiteralPath $currentPath -Algorithm SHA256).Hash.ToLowerInvariant()
$finalData = Get-Content -LiteralPath $finalPath -Raw | ConvertFrom-Json
if ($finalData.schema -ne 'N26-independent-mixed-after-six-current-final-rehash-v1' -or
    $finalData.current_audit_sha256 -ne $currentDigest -or
    $finalData.all_current_file_digests_rehashed -ne $true -or
    $finalData.candidate_angle_unresolved_closed_boxes -ne 16 -or
    $finalData.Rstar_conditional_frontier_pending_subtrees -ne 5637 -or
    $finalData.global_optimality_proved -ne $false) {
    throw 'Actual completed mixed pair does not match its independent final. No geometry started.'
}
Set-Location -LiteralPath $workspace
& (Join-Path $workspace 'work/run_midarc_source_geometry_serial_pair_v1.ps1') `
    -PythonExecutable $PythonExecutable
