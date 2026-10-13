param(
    [Parameter(Mandatory = $true)]
    [string]$PythonExecutable
)
$ErrorActionPreference = 'Stop'
$workspace = 'C:/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$bundle = Join-Path $workspace 'outputs/n26-current28-closed-ear-source-geometry-v1'
$checker = Join-Path $bundle 'verify_closed_ear_source_geometry.py'
$own = Join-Path $bundle 'VERIFIED.json'
$publication = Join-Path $workspace 'outputs/n26-current28-closed-ear-source-geometry-published-replay-v1.json'
if ((Test-Path -LiteralPath $own) -or (Test-Path -LiteralPath $publication)) {
    throw 'Closed-ear own/publication output exists; preserve it and do not duplicate.'
}
if (-not (Test-Path -LiteralPath $PythonExecutable) -or
    -not (Test-Path -LiteralPath $checker) -or
    -not (Test-Path -LiteralPath (Join-Path $bundle 'MANIFEST.json'))) {
    throw 'The literal interpreter or frozen geometry bundle is missing.'
}
Set-Location -LiteralPath $workspace
& $PythonExecutable $checker --input $bundle --report $own
if ($LASTEXITCODE -ne 0) {
    throw 'Entire-source OWN geometry failed; preserve every partial output.'
}
& $PythonExecutable $checker --input $bundle --report $publication
if ($LASTEXITCODE -ne 0) {
    throw 'SAME-main publication failed; do not repeat the completed OWN step.'
}
$ownDigest = (Get-FileHash -LiteralPath $own -Algorithm SHA256).Hash
$publicationDigest = (Get-FileHash -LiteralPath $publication -Algorithm SHA256).Hash
if ($ownDigest -ne $publicationDigest) {
    throw 'The actual same-main publication differs from its own acceptance.'
}
[pscustomobject]@{
    ClosedEarOwnAndSameMainPublicationCompleted = $true
    GeometryAcceptanceSHA256 = $ownDigest.ToLowerInvariant()
    CurrentJoinAndIndependentFinalStillRequired = $true
    CurrentFrontierStill = 11183
    CandidateWholeRootsStill = 25
} | ConvertTo-Json
