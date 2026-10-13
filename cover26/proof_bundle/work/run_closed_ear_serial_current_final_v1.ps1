param(
    [Parameter(Mandatory = $true)]
    [string]$PythonExecutable
)
$ErrorActionPreference = 'Stop'
$workspace = 'C:/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$geometry = Join-Path $workspace 'outputs/n26-current28-closed-ear-source-geometry-v1'
$publication = Join-Path $workspace 'outputs/n26-current28-closed-ear-source-geometry-published-replay-v1.json'
$parent = Join-Path $workspace 'outputs/n26-twenty-eighth-conditional-current-audit-v28-sparse-v1-strict-with-owned8-scope.json'
$parentFinal = Join-Path $workspace 'outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json'
$regression = Join-Path $workspace 'outputs/n26-current28-closed-ear-current-accounting-controls-v1.json'
$current = Join-Path $workspace 'outputs/n26-current28-closed-ear-supplemental-current-v1.json'
$final = Join-Path $workspace 'outputs/n26-current28-closed-ear-supplemental-independent-final-v1.json'
$narrative = Join-Path $workspace 'work/n26-closed-ear-current-admission-and-final-proof.md'
if (-not (Test-Path -LiteralPath $PythonExecutable)) {
    throw 'Literal interpreter missing.'
}
foreach ($required in @((Join-Path $geometry 'VERIFIED.json'), $publication, $parent, $parentFinal, $regression)) {
    if (-not (Test-Path -LiteralPath $required)) {
        throw 'Actual completed own/publication/parent/control prerequisites are missing; no current started.'
    }
}
foreach ($target in @($current, $final,
    ($current -replace '\.json$', '-geometry-semantic-replay.json'),
    ($current -replace '\.json$', '-closed-type-pool.json'),
    ($current -replace '\.json$', '-closed-receipt-checks.json'),
    ($current -replace '\.json$', '-terminal-obligations.json'))) {
    if (Test-Path -LiteralPath $target) {
        throw 'A current/final/partial output already exists; preserve it and do not duplicate.'
    }
}
if ((Get-FileHash -LiteralPath (Join-Path $geometry 'VERIFIED.json') -Algorithm SHA256).Hash -ne
    (Get-FileHash -LiteralPath $publication -Algorithm SHA256).Hash) {
    throw 'Actual geometry own and publication are not byte-identical.'
}
Set-Location -LiteralPath $workspace
& $PythonExecutable (Join-Path $workspace 'work/audit_closed_ear_source_current.py') `
    --parent-audit $parent --parent-final $parentFinal --geometry $geometry `
    --geometry-replay $publication --regression $regression --narrative $narrative --output $current
if ($LASTEXITCODE -ne 0) {
    throw 'Actual complete-current admission failed; retain all partial evidence.'
}
& $PythonExecutable (Join-Path $workspace 'work/recheck_closed_ear_source_current.py') `
    --current-audit $current --geometry $geometry --geometry-replay $publication --report $final
if ($LASTEXITCODE -ne 0) {
    throw 'Actual independent final failed; do not adopt or rerun the completed current main.'
}
[pscustomobject]@{
    ActualClosedEarCurrentAndIndependentFinalCompleted = $true
    ConditionalFrontier = 10540
    NewStrictWholePrefixes = 643
    CandidateWholeRootsStill = 25
    GlobalOptimalityProved = $false
    CurrentSHA256 = (Get-FileHash -LiteralPath $current -Algorithm SHA256).Hash.ToLowerInvariant()
    IndependentFinalSHA256 = (Get-FileHash -LiteralPath $final -Algorithm SHA256).Hash.ToLowerInvariant()
} | ConvertTo-Json
