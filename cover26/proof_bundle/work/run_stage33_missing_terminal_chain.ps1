$ErrorActionPreference = 'Stop'
$taskDependencyFolder = -join ([char[]]@(0x70ED,0x7231,0x5355,0x673A,0x4F46,0x840C,0x65B0))
$taskPython = 'C:/'+$taskDependencyFolder+'/dependencies/python/python.exe'
$taskStage = 'outputs/n26-conditional-force-stage-v33-sparse-v1'
$taskStageReplay = 'outputs/n26-conditional-force-stage-published-replay-v33-sparse-v1.json'
$taskCatalog = 'outputs/n26-conditional-terminal-catalog-v33-sparse-native-v1'
$taskCatalogReplay = 'outputs/n26-conditional-terminal-catalog-published-replay-v33-sparse-v1.json'
$taskContract = 'outputs/n26-stage33-sparse-v1-executor-contract-regression-v1.json'
$taskLinuxRoot = '/mnt/c/Users/Administrator/Documents/Codex/2026-10-09/n-26'
foreach ($taskMissingTarget in @($taskCatalog,$taskCatalogReplay,$taskContract)) {
    if (Test-Path -LiteralPath $taskMissingTarget) {
        throw 'A missing-only stage33 target already exists; inspect and preserve partials.'
    }
}
$taskAcceptance = Get-Content -LiteralPath "$taskStage/VERIFIED.json" -Encoding UTF8 -Raw | ConvertFrom-Json
$taskAcceptanceHash = (Get-FileHash -LiteralPath "$taskStage/VERIFIED.json" -Algorithm SHA256).Hash.ToLowerInvariant()
$taskReplayHash = (Get-FileHash -LiteralPath $taskStageReplay -Algorithm SHA256).Hash.ToLowerInvariant()
$taskCheckerHash = (Get-FileHash -LiteralPath "$taskStage/verify_conditional_force_stage_sparse.py" -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskAcceptanceHash -cne 'afaa314368a7bad8c05f3027bc8fe89771a4b96cbc1192ba92e6495fe9fa2a2b' -or
    $taskReplayHash -cne $taskAcceptanceHash -or $taskAcceptance.verified -ne $true -or
    $taskAcceptance.executed_checker_sha256 -cne $taskCheckerHash -or
    $taskAcceptance.source_acceptance_sha256 -cne '1122955835a3e5dec8c35a80be587b49f2d79fee3a66281539c6b4788fe6a4c7' -or
    $taskAcceptance.native_events_independently_replayed -ne 4800 -or
    $taskAcceptance.global_optimality_proved -ne $false) {
    throw 'Actual completed stage33 own acceptance/publication identity changed.'
}
$taskLiveWindows = Get-CimInstance Win32_Process | Where-Object {
    $_.Name -in @('python.exe','wsl.exe') -and $_.CommandLine -and
    ($_.CommandLine -match 'catalog-v33' -or
     ($_.CommandLine -match 'build_terminal_catalog\.py' -and $_.CommandLine -match 'stage-v33'))
}
if ($taskLiveWindows) {
    throw 'An original stage33 catalogue worker is still live; do not overlap.'
}
& 'C:/Windows/System32/wsl.exe' --distribution Ubuntu2204 --user root --exec /usr/bin/python3 "$taskLinuxRoot/work/build_terminal_catalog.py" --source-stage "$taskLinuxRoot/$taskStage" --candidate-control "$taskLinuxRoot/outputs/n26-candidate-transport-control-v1" --output "$taskLinuxRoot/$taskCatalog"
if ($LASTEXITCODE -ne 0) {
    throw 'Missing-only original Linux catalogue failed. Preserve every new partial; publication not started.'
}
& $taskPython "$taskCatalog/verify_terminal_catalog.py" --input $taskCatalog --report $taskCatalogReplay
if ($LASTEXITCODE -ne 0) { throw 'Actual SAME catalogue main publication failed.' }
& $taskPython work/audit_conditional_stage_acceptance_contract.py --known-good-stage $taskStage --suspect-stage outputs/n26-conditional-force-stage-v19-native-v4 --compat-producer work/derive_conditional_stage_compat_acceptance.py --report $taskContract
if ($LASTEXITCODE -ne 0) { throw 'Stage33 actual executor-contract regression failed.' }
& $taskPython work/inspect_completed_sparse_stage_chain.py --stage $taskStage --stage-replay $taskStageReplay --catalog $taskCatalog --catalog-replay $taskCatalogReplay --contract-regression $taskContract --source-stage outputs/n26-conditional-force-stage-v32-sparse-v1
if ($LASTEXITCODE -ne 0) { throw 'Stage33 actual read-only full-chain association failed.' }
