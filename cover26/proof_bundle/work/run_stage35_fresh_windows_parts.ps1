param(
    [Parameter(Mandatory=$true)]
    [ValidateSet('build','stage-replays','catalogue-replay-and-contract')]
    [string]$taskPart
)
$ErrorActionPreference = 'Stop'
$taskDependencyFolder = -join ([char[]]@(0x70ED,0x7231,0x5355,0x673A,0x4F46,0x840C,0x65B0))
$taskPython = 'C:/'+$taskDependencyFolder+'/dependencies/python/python.exe'
$taskProposal = 'work/n26-conditional-stage-proposals-v35-from-strict-v34.json'
$taskSource = 'outputs/n26-conditional-force-stage-v34-sparse-v1'
$taskStage = 'outputs/n26-conditional-force-stage-v35-sparse-v1'
$taskCatalog = 'outputs/n26-conditional-terminal-catalog-v35-sparse-native-v1'
$taskStageReplay = 'outputs/n26-conditional-force-stage-published-replay-v35-sparse-v1.json'
$taskCatalogReplay = 'outputs/n26-conditional-terminal-catalog-published-replay-v35-sparse-v1.json'
$taskContract = 'outputs/n26-stage35-sparse-v1-executor-contract-regression-v1.json'

function Assert-TaskAbsent([string[]]$taskPaths) {
    foreach ($taskPath in $taskPaths) {
        if (Test-Path -LiteralPath $taskPath) {
            throw ('Preserve existing stage35 evidence; do not repeat: '+$taskPath)
        }
    }
}

if ($taskPart -eq 'build') {
    if (-not (Test-Path -LiteralPath $taskProposal)) {
        throw 'Actual original stage35 discovery must finish first.'
    }
    $taskDiscoveryJobs = Get-CimInstance Win32_Process | Where-Object {
        $_.Name -eq 'python.exe' -and $_.CommandLine -match 'propose_force_stage\.py' -and
        $_.CommandLine -match 'proposals-v35-from-strict-v34'
    }
    if ($taskDiscoveryJobs) {
        throw 'Original stage35 discovery remains live. Require its actual successful terminal status.'
    }
    Assert-TaskAbsent @($taskStage,$taskCatalog,$taskStageReplay,$taskCatalogReplay,$taskContract)
    & $taskPython work/build_conditional_sparse_stage.py --proposal $taskProposal --source-replay outputs/n26-conditional-force-stage-published-replay-v34-sparse-v1.json --radius-basis outputs/n26-selected-type-sharp-trees-v3 --radius-basis-replay outputs/n26-selected-type-sharp-trees-published-replay-v3.json --control-regression outputs/n26-sparse-stage-control-selector-regression-v1.json --output $taskStage
    if ($LASTEXITCODE -ne 0) {
        throw 'Stage35 fresh original build failed; preserve all partial artifacts.'
    }
    Write-Output 'Stage35 fresh build complete. Actual original Linux native events are still required.'
    return
}

if ($taskPart -eq 'stage-replays') {
    Assert-TaskAbsent @("$taskStage/VERIFIED.json",$taskStageReplay,$taskCatalog,$taskCatalogReplay,$taskContract)
    $taskNative = Get-Content -LiteralPath "$taskStage/NATIVE-VERIFIED.json" -Encoding UTF8 -Raw | ConvertFrom-Json
    $taskTrace = Get-Content -LiteralPath "$taskStage/TRACE.json" -Encoding UTF8 -Raw | ConvertFrom-Json
    if ($taskNative.schema -cne 'N26-force-forest-native-reference-agreement-v1' -or
        $taskNative.verified_implementation_agreement -ne $true -or
        $taskNative.native_events_checked -ne @($taskTrace.events).Count -or
        @($taskNative.runs).Count -ne @($taskTrace.events).Count -or
        $taskNative.geometric_lower_bound_accepted_by_this_report -ne $false) {
        throw 'Actual stage35 original native report/event/scope association failed.'
    }
    & $taskPython "$taskStage/verify_conditional_force_stage_sparse.py" --input $taskStage --area-bundle outputs/n26-multislope-area-lower-v1 --report "$taskStage/VERIFIED.json"
    if ($LASTEXITCODE -ne 0) {
        throw 'Stage35 original own sparse acceptance failed; publication not started.'
    }
    & $taskPython "$taskStage/verify_conditional_force_stage_sparse.py" --input $taskStage --area-bundle outputs/n26-multislope-area-lower-v1 --report $taskStageReplay
    if ($LASTEXITCODE -ne 0) {
        throw 'Stage35 actual same-main publication failed; preserve acceptance and partials.'
    }
    Write-Output 'Stage35 own acceptance and actual same-main publication complete. Actual original Linux catalogue is still required.'
    return
}

Assert-TaskAbsent @($taskCatalogReplay,$taskContract)
if (-not (Test-Path -LiteralPath "$taskCatalog/VERIFIED.json")) {
    throw 'Actual original Linux stage35 catalogue build/acceptance must finish first.'
}
& $taskPython "$taskCatalog/verify_terminal_catalog.py" --input $taskCatalog --report $taskCatalogReplay
if ($LASTEXITCODE -ne 0) {
    throw 'Stage35 actual same catalogue-main publication failed; contract not started.'
}
& $taskPython work/audit_conditional_stage_acceptance_contract.py --known-good-stage $taskStage --suspect-stage outputs/n26-conditional-force-stage-v19-native-v4 --compat-producer work/derive_conditional_stage_compat_acceptance.py --report $taskContract
if ($LASTEXITCODE -ne 0) {
    throw 'Stage35 executor-contract regression failed; preserve actual catalogue evidence.'
}
& $taskPython work/inspect_completed_sparse_stage_chain.py --stage $taskStage --stage-replay $taskStageReplay --catalog $taskCatalog --catalog-replay $taskCatalogReplay --contract-regression $taskContract --source-stage $taskSource
if ($LASTEXITCODE -ne 0) {
    throw 'Stage35 read-only original complete-chain association failed.'
}
