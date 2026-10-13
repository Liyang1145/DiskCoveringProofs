param(
    [Parameter(Mandatory = $true)]
    [string]$PythonExecutable
)
$ErrorActionPreference = 'Stop'
$workspace = 'C:/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$parent = Join-Path $workspace 'outputs/n26-current28-six-target-mixed-candidate-current-v1.json'
$parentFinal = Join-Path $workspace 'outputs/n26-current28-six-target-mixed-candidate-independent-final-v1.json'
$geometry = Join-Path $workspace 'outputs/n26-mixed-after-six-midarc-source-geometry-v1'
$publication = Join-Path $workspace 'outputs/n26-mixed-after-six-midarc-source-geometry-published-replay-v1.json'
$controls = Join-Path $workspace 'outputs/n26-midarc-current-identity-and-accounting-controls-v1.json'
$narrative = Join-Path $workspace 'work/n26-midarc-current-admission-and-final-proof.md'
$current = Join-Path $workspace 'outputs/n26-mixed-after-six-midarc-supplemental-current-v1.json'
$final = Join-Path $workspace 'outputs/n26-mixed-after-six-midarc-independent-final-v1.json'
if (-not (Test-Path -LiteralPath $PythonExecutable)) {
    throw 'Literal interpreter missing.'
}
foreach ($required in @($parent, $parentFinal, (Join-Path $geometry 'VERIFIED.json'),
    $publication, $controls, $narrative)) {
    if (-not (Test-Path -LiteralPath $required)) {
        throw 'Actual completed mixed16-root parent, midarc own/publication or controls missing. No current started.'
    }
}
foreach ($target in @($current, $final,
    ($current -replace '\.json$', '-geometry-semantic-replay.json'),
    ($current -replace '\.json$', '-closed-type-pool.json'),
    ($current -replace '\.json$', '-closed-receipt-checks.json'),
    ($current -replace '\.json$', '-terminal-obligations.json'))) {
    if (Test-Path -LiteralPath $target) {
        throw 'Midarc current/final/partial output exists. Preserve it; do not duplicate a completed step.'
    }
}
if ((Get-FileHash -LiteralPath (Join-Path $geometry 'VERIFIED.json') -Algorithm SHA256).Hash -ne
    (Get-FileHash -LiteralPath $publication -Algorithm SHA256).Hash) {
    throw 'Actual midarc own and publication reports are not byte-identical.'
}
$runningJoins = @(Get-CimInstance Win32_Process | Where-Object {
    $_.Name -eq 'python.exe' -and
    $_.CommandLine -match 'work[\\/](audit|recheck)_[^ ]*current[^ ]*\.py'
})
if ($runningJoins.Count -ne 0) {
    throw 'Another complete-current join/final is live. Keep serial ordering.'
}
Set-Location -LiteralPath $workspace
& $PythonExecutable (Join-Path $workspace 'work/audit_midarc_source_current.py') `
    --parent-audit $parent --parent-final $parentFinal --geometry $geometry `
    --geometry-replay $publication --regression $controls --narrative $narrative --output $current
if ($LASTEXITCODE -ne 0) {
    throw 'Actual midarc current admission failed. Preserve partial evidence.'
}
& $PythonExecutable (Join-Path $workspace 'work/recheck_midarc_source_current.py') `
    --current-audit $current --geometry $geometry --geometry-replay $publication --report $final
if ($LASTEXITCODE -ne 0) {
    throw 'Actual independent midarc final failed. Do not rerun the completed compositor.'
}
[pscustomobject]@{
    ActualMidarcCurrentAndIndependentFinalCompleted = $true
    NewStrictWholePrefixes = 680
    ConditionalFrontier = 4957
    CandidateWholeRootsRetained = 16
    GlobalOptimalityProved = $false
    CurrentSHA256 = (Get-FileHash -LiteralPath $current -Algorithm SHA256).Hash.ToLowerInvariant()
    IndependentFinalSHA256 = (Get-FileHash -LiteralPath $final -Algorithm SHA256).Hash.ToLowerInvariant()
} | ConvertTo-Json
