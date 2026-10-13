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
# Open a real process handle NOW, while live. This prevents PID reuse or an
# absent handle from being mistaken for a successful completed predecessor.
$predecessorHandle = $predecessor.Handle
$observedStart = $predecessor.StartTime.ToUniversalTime().ToString('o')
$predecessorInfo = Get-CimInstance Win32_Process -Filter "ProcessId=$PredecessorProcessId"
if ($predecessor.HasExited -or $observedStart -ne $PredecessorStartUtc -or
    $predecessorInfo.CommandLine -notmatch 'run_six_target_serial_current_final_v1\.ps1') {
    throw 'The exact live SIX current/final predecessor was not identified. No admission started.'
}
[pscustomobject]@{
    ExactLivePredecessorHandleAcquired = $true
    PredecessorProcessId = $PredecessorProcessId
    PredecessorStartUtc = $observedStart
    MixedCurrentAdmissionStarted = $false
    WaitingOnlyForThisOneActualSerialChain = $true
} | ConvertTo-Json
while (-not $predecessor.WaitForExit(30000)) {
    # One-shot process dependency, not a restart/poll-by-output-file loop.
    # No geometry/current executor is started during this wait.
}
if ($predecessor.ExitCode -ne 0) {
    throw 'Exact SIX current/final predecessor failed. Preserve it; no mixed admission started.'
}
$currentPath = Join-Path $workspace 'outputs/n26-current28-six-target-supplemental-current-v1.json'
$finalPath = Join-Path $workspace 'outputs/n26-current28-six-target-supplemental-independent-final-v1.json'
foreach ($required in @($currentPath, $finalPath)) {
    if (-not (Test-Path -LiteralPath $required)) {
        throw 'Successful predecessor lacks its actual current/final pair. No mixed admission started.'
    }
}
$currentDigest = (Get-FileHash -LiteralPath $currentPath -Algorithm SHA256).Hash.ToLowerInvariant()
$finalData = Get-Content -LiteralPath $finalPath -Raw | ConvertFrom-Json
if ($finalData.schema -ne 'N26-independent-six-target-source-current-final-rehash-v1' -or
    $finalData.current_audit_sha256 -ne $currentDigest -or
    $finalData.all_current_file_digests_rehashed -ne $true -or
    $finalData.Rstar_conditional_frontier_pending_subtrees -ne 5637 -or
    $finalData.candidate_angle_unresolved_closed_boxes -ne 25 -or
    $finalData.global_optimality_proved -ne $false) {
    throw 'Actual completed SIX pair does not match its independent final. No mixed admission started.'
}
Set-Location -LiteralPath $workspace
& (Join-Path $workspace 'work/run_mixed_after_six_serial_current_final_v1.ps1') `
    -PythonExecutable $PythonExecutable
