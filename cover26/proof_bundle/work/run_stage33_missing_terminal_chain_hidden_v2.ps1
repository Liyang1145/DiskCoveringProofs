$ErrorActionPreference = 'Stop'
$taskDependencyFolder = -join ([char[]]@(0x70ED,0x7231,0x5355,0x673A,0x4F46,0x840C,0x65B0))
$taskPython = 'C:/'+$taskDependencyFolder+'/dependencies/python/python.exe'
$taskStage = 'outputs/n26-conditional-force-stage-v33-sparse-v1'
$taskStageReplay = 'outputs/n26-conditional-force-stage-published-replay-v33-sparse-v1.json'
$taskCatalog = 'outputs/n26-conditional-terminal-catalog-v33-sparse-native-v1'
$taskCatalogReplay = 'outputs/n26-conditional-terminal-catalog-published-replay-v33-sparse-v1.json'
$taskContract = 'outputs/n26-stage33-sparse-v1-executor-contract-regression-v1.json'
$taskLinuxRoot = '/mnt/c/Users/Administrator/Documents/Codex/2026-10-09/n-26'
$taskReadinessOut = Join-Path (Get-Location) 'work/n26-stage33-linux-readiness-hidden-stdout-v2.log'
$taskReadinessErr = Join-Path (Get-Location) 'work/n26-stage33-linux-readiness-hidden-stderr-v2.log'
$taskCatalogueOut = Join-Path (Get-Location) 'work/n26-stage33-original-linux-catalogue-hidden-stdout-v2.log'
$taskCatalogueErr = Join-Path (Get-Location) 'work/n26-stage33-original-linux-catalogue-hidden-stderr-v2.log'
foreach ($taskTarget in @($taskCatalog,$taskCatalogReplay,$taskContract,$taskReadinessOut,$taskReadinessErr,$taskCatalogueOut,$taskCatalogueErr)) {
    if (Test-Path -LiteralPath $taskTarget) { throw 'Preserve existing missing-only artifacts/logs; inspect before resuming.' }
}
$taskAcceptanceHash = (Get-FileHash -LiteralPath "$taskStage/VERIFIED.json" -Algorithm SHA256).Hash.ToLowerInvariant()
$taskReplayHash = (Get-FileHash -LiteralPath $taskStageReplay -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskAcceptanceHash -cne 'afaa314368a7bad8c05f3027bc8fe89771a4b96cbc1192ba92e6495fe9fa2a2b' -or
    $taskReplayHash -cne $taskAcceptanceHash) { throw 'Actual completed stage33 acceptance/publication changed.' }
$taskWindowsWorkers = Get-CimInstance Win32_Process | Where-Object {
    $_.Name -in @('python.exe','wsl.exe') -and $_.CommandLine -and
    ($_.CommandLine -match 'catalog-v33' -or
     ($_.CommandLine -match 'build_terminal_catalog\.py' -and $_.CommandLine -match 'stage-v33'))
}
if ($taskWindowsWorkers) { throw 'A stage33 catalogue worker is still live; do not overlap.' }
$taskProbeArgs = @('--distribution','Ubuntu2204','--user','root','--exec','/usr/bin/python3',"$taskLinuxRoot/work/inspect_stage33_linux_launch_readonly.py")
$taskProbe = Start-Process -FilePath 'C:/Windows/System32/wsl.exe' -ArgumentList $taskProbeArgs -WindowStyle Hidden -RedirectStandardOutput $taskReadinessOut -RedirectStandardError $taskReadinessErr -PassThru -Wait
Get-Content -LiteralPath $taskReadinessOut -Encoding UTF8
Get-Content -LiteralPath $taskReadinessErr -Encoding UTF8
if ($taskProbe.ExitCode -ne 0) { throw 'Actual read-only Linux readiness failed; catalogue not started.' }
$taskCatalogueArgs = @('--distribution','Ubuntu2204','--user','root','--exec','/usr/bin/python3',"$taskLinuxRoot/work/build_terminal_catalog.py",'--source-stage',"$taskLinuxRoot/$taskStage",'--candidate-control',"$taskLinuxRoot/outputs/n26-candidate-transport-control-v1",'--output',"$taskLinuxRoot/$taskCatalog")
$taskBuild = Start-Process -FilePath 'C:/Windows/System32/wsl.exe' -ArgumentList $taskCatalogueArgs -WindowStyle Hidden -RedirectStandardOutput $taskCatalogueOut -RedirectStandardError $taskCatalogueErr -PassThru -Wait
Get-Content -LiteralPath $taskCatalogueOut -Encoding UTF8
Get-Content -LiteralPath $taskCatalogueErr -Encoding UTF8
if ($taskBuild.ExitCode -ne 0) { throw 'Original Linux catalogue failed; preserve partials and logs.' }
& $taskPython "$taskCatalog/verify_terminal_catalog.py" --input $taskCatalog --report $taskCatalogReplay
if ($LASTEXITCODE -ne 0) { throw 'Actual SAME catalogue-main publication failed.' }
& $taskPython work/audit_conditional_stage_acceptance_contract.py --known-good-stage $taskStage --suspect-stage outputs/n26-conditional-force-stage-v19-native-v4 --compat-producer work/derive_conditional_stage_compat_acceptance.py --report $taskContract
if ($LASTEXITCODE -ne 0) { throw 'Stage33 actual executor-contract regression failed.' }
& $taskPython work/inspect_completed_sparse_stage_chain.py --stage $taskStage --stage-replay $taskStageReplay --catalog $taskCatalog --catalog-replay $taskCatalogReplay --contract-regression $taskContract --source-stage outputs/n26-conditional-force-stage-v32-sparse-v1
if ($LASTEXITCODE -ne 0) { throw 'Stage33 actual full-chain read-only association failed.' }
