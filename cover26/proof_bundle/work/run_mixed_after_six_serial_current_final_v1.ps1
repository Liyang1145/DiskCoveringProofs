param(
    [Parameter(Mandatory = $true)]
    [string]$PythonExecutable
)
$ErrorActionPreference = 'Stop'
$workspace = 'C:/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$parent = Join-Path $workspace 'outputs/n26-current28-six-target-supplemental-current-v1.json'
$parentFinal = Join-Path $workspace 'outputs/n26-current28-six-target-supplemental-independent-final-v1.json'
$frontier = Join-Path $workspace 'outputs/n26-current28-six-target-source-geometry-v1/FRONTIER.json'
$overlay = Join-Path $workspace 'outputs/n26-current-candidate-mixed-curvature-covers-v1'
$publication = Join-Path $workspace 'outputs/n26-current-candidate-mixed-curvature-covers-published-replay-v1.json'
$identityControls = Join-Path $workspace 'outputs/n26-candidate-identity-after-six-target-controls-v1.json'
$accountingControls = Join-Path $workspace 'outputs/n26-mixed-after-six-current-accounting-controls-v1.json'
$narrative = Join-Path $workspace 'work/n26-mixed-after-six-current-admission-and-final-proof.md'
$current = Join-Path $workspace 'outputs/n26-current28-six-target-mixed-candidate-current-v1.json'
$final = Join-Path $workspace 'outputs/n26-current28-six-target-mixed-candidate-independent-final-v1.json'
if (-not (Test-Path -LiteralPath $PythonExecutable)) {
    throw 'Literal interpreter missing.'
}
foreach ($required in @($parent, $parentFinal, $frontier, (Join-Path $overlay 'VERIFIED.json'),
    $publication, $identityControls, $accountingControls, $narrative)) {
    if (-not (Test-Path -LiteralPath $required)) {
        throw 'Actual completed SIX current/final, mixed own/publication or controls missing; no admission started.'
    }
}
foreach ($target in @($current, $final,
    ($current -replace '\.json$', '-overlay-semantic-replay.json'),
    ($current -replace '\.json$', '-closed-type-pool.json'),
    ($current -replace '\.json$', '-closed-receipt-checks.json'),
    ($current -replace '\.json$', '-terminal-obligations.json'))) {
    if (Test-Path -LiteralPath $target) {
        throw 'Current/final/partial output exists; preserve it and do not duplicate completed work.'
    }
}
if ((Get-FileHash -LiteralPath (Join-Path $overlay 'VERIFIED.json') -Algorithm SHA256).Hash -ne
    (Get-FileHash -LiteralPath $publication -Algorithm SHA256).Hash) {
    throw 'Actual mixed own and publication are not byte-identical.'
}
# No current or final is allowed to overlap another complete-current join.
$runningJoins = @(Get-CimInstance Win32_Process | Where-Object {
    $_.Name -eq 'python.exe' -and
    $_.CommandLine -match 'work[\\/](audit|recheck)_[^ ]*current[^ ]*\.py'
})
if ($runningJoins.Count -ne 0) {
    throw 'Another complete-current join/final is live. Keep the serial order.'
}
Set-Location -LiteralPath $workspace
& $PythonExecutable (Join-Path $workspace 'work/audit_mixed_curvature_candidate_after_six_current.py') `
    --parent-audit $parent --parent-final $parentFinal --frontier $frontier `
    --overlay $overlay --overlay-replay $publication --narrative $narrative `
    --identity-regression $identityControls --accounting-regression $accountingControls --output $current
if ($LASTEXITCODE -ne 0) {
    throw 'Actual mixed-after-SIX current failed; preserve all partial evidence.'
}
& $PythonExecutable (Join-Path $workspace 'work/recheck_mixed_curvature_candidate_after_six_current.py') `
    --current-audit $current --overlay $overlay --overlay-replay $publication --report $final
if ($LASTEXITCODE -ne 0) {
    throw 'Actual independent mixed-after-SIX final failed; do not rerun the completed compositor.'
}
[pscustomobject]@{
    ActualMixedAfterSixCurrentAndIndependentFinalCompleted = $true
    ConditionalFrontierRetained = 5637
    NewWholeCandidateRootsLowerBounded = 9
    CandidateWholeRootsRemaining = 16
    GlobalOptimalityProved = $false
    CurrentSHA256 = (Get-FileHash -LiteralPath $current -Algorithm SHA256).Hash.ToLowerInvariant()
    IndependentFinalSHA256 = (Get-FileHash -LiteralPath $final -Algorithm SHA256).Hash.ToLowerInvariant()
} | ConvertTo-Json
