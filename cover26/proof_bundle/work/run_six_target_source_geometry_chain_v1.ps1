param(
    [Parameter(Mandatory = $true)]
    [string]$PythonExecutable
)
$ErrorActionPreference = 'Stop'
$workspace = 'C:/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$bundle = Join-Path $workspace 'outputs/n26-current28-six-target-source-geometry-v1'
$checker = Join-Path $bundle 'verify_six_target_source_geometry.py'
$own = Join-Path $bundle 'VERIFIED.json'
$publication = Join-Path $workspace 'outputs/n26-current28-six-target-source-geometry-published-replay-v1.json'
if ((Test-Path -LiteralPath $own) -or (Test-Path -LiteralPath $publication)) {
    throw 'A six-target own/publication output already exists; do not duplicate or overwrite it.'
}
if (-not (Test-Path -LiteralPath $PythonExecutable) -or
    -not (Test-Path -LiteralPath $checker) -or
    -not (Test-Path -LiteralPath (Join-Path $bundle 'MANIFEST.json'))) {
    throw 'Literal interpreter or completed frozen six-target bundle is missing.'
}
Set-Location -LiteralPath $workspace
& $PythonExecutable $checker --input $bundle --report $own
if ($LASTEXITCODE -ne 0) {
    throw 'Actual entire-source six-target OWN geometry failed; preserve all partial evidence.'
}
& $PythonExecutable $checker --input $bundle --report $publication
if ($LASTEXITCODE -ne 0) {
    throw 'Actual six-target same-main publication failed; do not repeat the completed OWN.'
}
$ownDigest = (Get-FileHash -LiteralPath $own -Algorithm SHA256).Hash
$publicationDigest = (Get-FileHash -LiteralPath $publication -Algorithm SHA256).Hash
if ($ownDigest -ne $publicationDigest) {
    throw 'Actual six-target own and same-main publication are not byte-identical.'
}
[pscustomobject]@{
    ActualSixTargetOwnAndSameMainPublicationCompleted = $true
    GeometrySHA256 = $ownDigest.ToLowerInvariant()
    FormalFrontierStill = 11183
    AcceptedProspectiveFrontierRequiresCurrentAndFinal = 5637
    CandidateWholeRootsStill = 25
    CurrentAdmissionAndIndependentFinalStillRequired = $true
    GlobalOptimalityProved = $false
} | ConvertTo-Json
