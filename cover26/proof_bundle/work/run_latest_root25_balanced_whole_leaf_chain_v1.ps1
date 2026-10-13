param(
    [Parameter(Mandatory=$true)][string]$PythonExecutable,
    [Parameter(Mandatory=$true)][string]$Seed,
    [Parameter(Mandatory=$true)][string]$SeedControls,
    [Parameter(Mandatory=$true)][string]$SeedSha256,
    [Parameter(Mandatory=$true)][string]$SeedControlsSha256,
    [Parameter(Mandatory=$true)][string]$Diagnosis,
    [Parameter(Mandatory=$true)][string]$Controls,
    [int]$Limit=256,
    [int]$Parts=8
)
$ErrorActionPreference='Stop'
if ((Test-Path -LiteralPath $Diagnosis) -or (Test-Path -LiteralPath $Controls)) {
    throw 'Preserve old successor/control outputs; use new destinations.'
}
if ((Get-FileHash -LiteralPath $Seed -Algorithm SHA256).Hash.ToLowerInvariant() -ne $SeedSha256 -or
    (Get-FileHash -LiteralPath $SeedControls -Algorithm SHA256).Hash.ToLowerInvariant() -ne $SeedControlsSha256) {
    throw 'Actual completed predecessor pair changed.'
}
& $PythonExecutable -u 'work/continue_latest_root25_balanced_whole_leaf_energy.py' `
    --seed $Seed --seed-controls $SeedControls --seed-sha256 $SeedSha256 `
    --seed-controls-sha256 $SeedControlsSha256 --report $Diagnosis --limit $Limit --parts $Parts
if ($LASTEXITCODE -ne 0) { throw 'New whole-leaf producer failed; preserve evidence and do not start controls.' }
$diagnosisDigest=(Get-FileHash -LiteralPath $Diagnosis -Algorithm SHA256).Hash.ToLowerInvariant()
& $PythonExecutable -u 'work/test_latest_root25_balanced_whole_leaf_energy.py' `
    --seed $Seed --seed-controls $SeedControls --seed-sha256 $SeedSha256 `
    --seed-controls-sha256 $SeedControlsSha256 --diagnosis $Diagnosis `
    --diagnosis-sha256 $diagnosisDigest --report $Controls
if ($LASTEXITCODE -ne 0) { throw 'New independent whole-leaf controls failed; do not adopt this successor.' }
Write-Output 'ACTUAL new whole-leaf producer AND independent controls terminal0. No geometry/current payment.'
