$ErrorActionPreference = 'Stop'
$workspace = 'C:/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$python = 'C:/热爱单机但萌新/dependencies/python/python.exe'
$bundle = Join-Path $workspace 'outputs/n26-current28-closed-ear-source-geometry-v1'
$checker = Join-Path $bundle 'verify_closed_ear_source_geometry.py'
$own = Join-Path $bundle 'VERIFIED.json'
$publication = Join-Path $workspace 'outputs/n26-current28-closed-ear-source-geometry-published-replay-v1.json'
if ((Test-Path -LiteralPath $own) -or (Test-Path -LiteralPath $publication)) {
    throw 'Original closed-ear own/publication chain already has output; do not reset or duplicate.'
}
if (-not (Test-Path -LiteralPath $checker) -or -not (Test-Path -LiteralPath (Join-Path $bundle 'MANIFEST.json'))) {
    throw 'Actual frozen source geometry bundle is incomplete.'
}
Set-Location -LiteralPath $workspace
& $python $checker --input $bundle --report $own
if ($LASTEXITCODE -ne 0) {
    throw 'Original closed-ear entire-source OWN geometry failed; preserve failure and all partial files.'
}
& $python $checker --input $bundle --report $publication
if ($LASTEXITCODE -ne 0) {
    throw 'Original closed-ear SAME-main publication failed; preserve failure and do not restart OWN.'
}
$ownDigest = (Get-FileHash -LiteralPath $own -Algorithm SHA256).Hash
$publicationDigest = (Get-FileHash -LiteralPath $publication -Algorithm SHA256).Hash
if ($ownDigest -ne $publicationDigest) {
    throw 'Actual same geometry main publication differs from its own acceptance.'
}
[pscustomobject]@{
    OriginalClosedEarOwnAndSameMainPublicationCompleted = $true
    GeometryAcceptanceSHA256 = $ownDigest.ToLowerInvariant()
    CurrentJoinAndIndependentFinalStillRequired = $true
    CurrentFrontierStill = 11183
    CandidateWholeRootsStill = 25
} | ConvertTo-Json
