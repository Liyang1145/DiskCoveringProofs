param(
    [Parameter(Mandatory = $true)]
    [string]$PythonExecutable
)
$ErrorActionPreference = 'Stop'
$workspace = 'C:/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$parent = Join-Path $workspace 'outputs/n26-current28-six-target-mixed-candidate-current-v1.json'
$parentFinal = Join-Path $workspace 'outputs/n26-current28-six-target-mixed-candidate-independent-final-v1.json'
$candidate = Join-Path $workspace 'outputs/n26-current-candidate-mixed-curvature-covers-v1'
$candidatePublication = Join-Path $workspace 'outputs/n26-current-candidate-mixed-curvature-covers-published-replay-v1.json'
$bundle = Join-Path $workspace 'outputs/n26-mixed-after-six-midarc-source-geometry-v1'
$publication = Join-Path $workspace 'outputs/n26-mixed-after-six-midarc-source-geometry-published-replay-v1.json'
$own = Join-Path $bundle 'VERIFIED.json'
$checker = Join-Path $bundle 'verify_midarc_source_geometry.py'
if (-not (Test-Path -LiteralPath $PythonExecutable)) {
    throw 'Literal interpreter missing; no new source geometry started.'
}
foreach ($required in @($parent, $parentFinal, (Join-Path $candidate 'VERIFIED.json'),
    $candidatePublication, (Join-Path $workspace 'outputs/n26-midarc-SIX-filtered-source-accounting-controls-v1.json'))) {
    if (-not (Test-Path -LiteralPath $required)) {
        throw 'Actual completed mixed16root current/final or controls missing. No midarc source geometry started.'
    }
}
if ((Test-Path -LiteralPath $bundle) -or (Test-Path -LiteralPath $publication)) {
    throw 'Midarc frozen/partial/accepted evidence exists. Preserve it; do not duplicate any completed step.'
}
Set-Location -LiteralPath $workspace
& $PythonExecutable (Join-Path $workspace 'work/build_midarc_source_geometry.py') `
    --parent-current $parent --parent-final $parentFinal --candidate-source $candidate `
    --candidate-publication $candidatePublication --output $bundle
if ($LASTEXITCODE -ne 0) {
    throw 'Actual midarc bundle preparation failed; preserve all partial evidence.'
}
& $PythonExecutable $checker --input $bundle --report $own
if ($LASTEXITCODE -ne 0) {
    throw 'Actual ENTIRE midarc source geometry OWN failed; preserve its frozen inputs.'
}
& $PythonExecutable $checker --input $bundle --report $publication
if ($LASTEXITCODE -ne 0) {
    throw 'Actual same-main midarc publication failed; do not repeat completed OWN.'
}
if ((Get-FileHash -LiteralPath $own -Algorithm SHA256).Hash -ne
    (Get-FileHash -LiteralPath $publication -Algorithm SHA256).Hash) {
    throw 'Actual midarc own/publication reports are not byte-identical.'
}
[pscustomobject]@{
    ActualMidarcEntireSourceOwnAndSameMainPublicationCompleted = $true
    OldSIXFilteredSource = 5637
    NewWholePrefixObstructions = 680
    AcceptedProspectiveFrontierRequiresCurrentAndFinal = 4957
    ActualCandidateWholeRootsRetained = 16
    CurrentAdmissionAndIndependentFinalStillRequired = $true
    GlobalOptimalityProved = $false
    GeometrySHA256 = (Get-FileHash -LiteralPath $own -Algorithm SHA256).Hash.ToLowerInvariant()
} | ConvertTo-Json
