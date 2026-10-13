param(
    [Parameter(Mandatory = $true)]
    [string]$PythonExecutable
)
$ErrorActionPreference = 'Stop'
$workspace = 'C:/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$output = Join-Path $workspace 'outputs/n26-imported-n25-source-premise-v1'
$final = Join-Path $workspace 'outputs/n26-imported-n25-source-premise-independent-final-v1.json'
if (-not (Test-Path -LiteralPath $PythonExecutable)) {
    throw 'Literal interpreter missing.'
}
if ((Test-Path -LiteralPath $output) -or (Test-Path -LiteralPath $final)) {
    throw 'Prior-source admission or partial output exists; preserve it and do not duplicate.'
}
Set-Location -LiteralPath $workspace
& $PythonExecutable (Join-Path $workspace 'work/verify_imported_n25_source_for_n26.py') --output $output
if ($LASTEXITCODE -ne 0) {
    throw 'Full prior-source content admission failed; retain all partial evidence.'
}
& $PythonExecutable (Join-Path $workspace 'work/recheck_imported_n25_source_for_n26.py') `
    --import $output --report $final
if ($LASTEXITCODE -ne 0) {
    throw 'Prior-source independent full final failed; do not repeat the completed admission.'
}
[pscustomobject]@{
    ActualPriorN25FullContentImportAndIndependentFinalCompleted = $true
    ImportedPriorSOURCEProofNotNewReplayOfOldTrees = $true
    GenuineOriginalDisksInN26Scope = 26
    N26GraphGeometryAndCurrentAdmissionStillRequired = $true
    N26GlobalOptimalityProved = $false
    ImportSHA256 = (Get-FileHash -LiteralPath (Join-Path $output 'VERIFIED.json') -Algorithm SHA256).Hash.ToLowerInvariant()
    IndependentFinalSHA256 = (Get-FileHash -LiteralPath $final -Algorithm SHA256).Hash.ToLowerInvariant()
} | ConvertTo-Json
