$ErrorActionPreference = 'Stop'
$taskDependencyFolder = -join ([char[]]@(0x70ED,0x7231,0x5355,0x673A,0x4F46,0x840C,0x65B0))
$taskPython = 'C:/'+$taskDependencyFolder+'/dependencies/python/python.exe'
$taskProposal = 'work/n26-conditional-stage-proposals-v32-from-strict-v31.json'
$taskStage = 'outputs/n26-conditional-force-stage-v32-sparse-v1'
$taskCatalog = 'outputs/n26-conditional-terminal-catalog-v32-sparse-native-v1'
$taskLinuxRoot = '/mnt/c/Users/Administrator/Documents/Codex/2026-10-09/n-26'
if (-not (Test-Path -LiteralPath $taskProposal)) {
    throw 'Stage32 actual discovery has not completed; never substitute another proposal.'
}
if ((Test-Path -LiteralPath $taskStage) -or (Test-Path -LiteralPath $taskCatalog)) {
    throw 'Stage32 artifact already exists. Preserve it and inspect; do not restart.'
}
$taskDiscoveryJobs = Get-CimInstance Win32_Process | Where-Object {
    $_.Name -eq 'python.exe' -and $_.CommandLine -match 'propose_force_stage\.py' -and
    $_.CommandLine -match 'proposals-v32-from-strict-v31'
}
if ($taskDiscoveryJobs) {
    throw 'Original stage32 discovery is still live. Require its actual terminal0 before this chain.'
}
& $taskPython work/build_conditional_sparse_stage.py --proposal $taskProposal --source-replay outputs/n26-conditional-force-stage-published-replay-v31-sparse-v1.json --radius-basis outputs/n26-selected-type-sharp-trees-v3 --radius-basis-replay outputs/n26-selected-type-sharp-trees-published-replay-v3.json --control-regression outputs/n26-sparse-stage-control-selector-regression-v1.json --output $taskStage
if ($LASTEXITCODE -ne 0) { throw 'Stage32 fresh build failed; preserve partial artifacts.' }
wsl.exe -d Ubuntu2204 -u root -- /usr/bin/python3 "$taskLinuxRoot/$taskStage/audit_force_forest_native.py" --input "$taskLinuxRoot/$taskStage"
if ($LASTEXITCODE -ne 0) { throw 'Stage32 original Linux native events failed; acceptance not started.' }
& $taskPython "$taskStage/verify_conditional_force_stage_sparse.py" --input $taskStage --area-bundle outputs/n26-multislope-area-lower-v1 --report "$taskStage/VERIFIED.json"
if ($LASTEXITCODE -ne 0) { throw 'Stage32 own sparse acceptance failed; publication not started.' }
& $taskPython "$taskStage/verify_conditional_force_stage_sparse.py" --input $taskStage --area-bundle outputs/n26-multislope-area-lower-v1 --report outputs/n26-conditional-force-stage-published-replay-v32-sparse-v1.json
if ($LASTEXITCODE -ne 0) { throw 'Stage32 actual own-main publication failed; catalogue not started.' }
wsl.exe -d Ubuntu2204 -u root -- /usr/bin/python3 "$taskLinuxRoot/work/build_terminal_catalog.py" --source-stage "$taskLinuxRoot/$taskStage" --candidate-control "$taskLinuxRoot/outputs/n26-candidate-transport-control-v1" --output "$taskLinuxRoot/$taskCatalog"
if ($LASTEXITCODE -ne 0) { throw 'Stage32 original Linux terminal catalogue failed; missing-only recovery required.' }
& $taskPython "$taskCatalog/verify_terminal_catalog.py" --input $taskCatalog --report outputs/n26-conditional-terminal-catalog-published-replay-v32-sparse-v1.json
if ($LASTEXITCODE -ne 0) { throw 'Stage32 actual catalogue publication failed; contract not started.' }
& $taskPython work/audit_conditional_stage_acceptance_contract.py --known-good-stage $taskStage --suspect-stage outputs/n26-conditional-force-stage-v19-native-v4 --compat-producer work/derive_conditional_stage_compat_acceptance.py --report outputs/n26-stage32-sparse-v1-executor-contract-regression-v1.json
if ($LASTEXITCODE -ne 0) { throw 'Stage32 executor-contract regression failed.' }
& $taskPython work/inspect_completed_sparse_stage_chain.py --stage $taskStage --stage-replay outputs/n26-conditional-force-stage-published-replay-v32-sparse-v1.json --catalog $taskCatalog --catalog-replay outputs/n26-conditional-terminal-catalog-published-replay-v32-sparse-v1.json --contract-regression outputs/n26-stage32-sparse-v1-executor-contract-regression-v1.json --source-stage outputs/n26-conditional-force-stage-v31-sparse-v1
if ($LASTEXITCODE -ne 0) { throw 'Stage32 read-only full-chain association failed.' }
