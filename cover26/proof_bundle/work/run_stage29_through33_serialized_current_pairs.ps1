$ErrorActionPreference = 'Stop'
$taskDependencyFolder = -join ([char[]]@(0x70ED,0x7231,0x5355,0x673A,0x4F46,0x840C,0x65B0))
$taskPython = 'C:/'+$taskDependencyFolder+'/dependencies/python/python.exe'
$taskParentAudit = 'outputs/n26-twenty-eighth-conditional-current-audit-v28-sparse-v1-strict-with-owned8-scope.json'
$taskParentFinal = 'outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json'
$taskLiveJoins = Get-CimInstance Win32_Process | Where-Object {
    $_.Name -eq 'python.exe' -and $_.CommandLine -match
    '(audit_stage_catalogue_with_executor_contract|audit_stage_catalogue_with_closed_pool|recheck_current_stage_catalogue_inventory|audit_mixed_curvature_candidate_current|recheck_mixed_curvature_candidate_current|audit_product_candidate_current|recheck_product_candidate_current)\.py'
}
if ($taskLiveJoins) {
    throw 'A complete-current join or independent final is live; do not overlap.'
}
if (-not (Test-Path -LiteralPath $taskParentAudit) -or -not (Test-Path -LiteralPath $taskParentFinal)) {
    throw 'The original stage26-through28 pipeline has not completed its actual parent/final pair.'
}
$taskParent = Get-Content -LiteralPath $taskParentAudit -Encoding UTF8 -Raw | ConvertFrom-Json
$taskFinal = Get-Content -LiteralPath $taskParentFinal -Encoding UTF8 -Raw | ConvertFrom-Json
$taskParentHash = (Get-FileHash -LiteralPath $taskParentAudit -Algorithm SHA256).Hash.ToLowerInvariant()
if ($taskFinal.schema -ne 'N26-independent-final-current-inventory-rehash-v1' -or
    $taskFinal.all_current_file_digests_rehashed -ne $true -or
    $taskFinal.current_audit_sha256 -cne $taskParentHash -or
    $taskFinal.current_file_digests_rechecked -ne @($taskParent.files.PSObject.Properties | ForEach-Object { $_.Name }).Count -or
    $taskFinal.candidate_angle_unresolved_closed_boxes -ne $taskParent.candidate_angle_unresolved_closed_boxes -or
    $taskParent.global_lower_bound_proved -ne $false -or
    $taskParent.global_optimality_proved -ne $false) {
    throw 'Stage28 formal parent/final association failed; no join started.'
}
$taskStagePairs = @(
    @{v=29;word='twenty-ninth';date='20261011'},
    @{v=30;word='thirtieth';date='20261012'},
    @{v=31;word='thirty-first';date='20261012'},
    @{v=32;word='thirty-second';date='20261012'},
    @{v=33;word='thirty-third';date='20261012'}
)
foreach ($taskPair in $taskStagePairs) {
    $taskVersion = $taskPair.v
    $taskStage = 'outputs/n26-conditional-force-stage-v'+$taskVersion+'-sparse-v1'
    $taskStageReplay = 'outputs/n26-conditional-force-stage-published-replay-v'+$taskVersion+'-sparse-v1.json'
    $taskCatalog = 'outputs/n26-conditional-terminal-catalog-v'+$taskVersion+'-sparse-native-v1'
    $taskCatalogReplay = 'outputs/n26-conditional-terminal-catalog-published-replay-v'+$taskVersion+'-sparse-v1.json'
    $taskCurrent = 'outputs/n26-'+$taskPair.word+'-conditional-current-audit-v'+$taskVersion+'-sparse-v1-strict-with-owned8-scope.json'
    $taskFinalTarget = 'outputs/n26-'+$taskPair.word+'-conditional-final-digest-recheck-v'+$taskVersion+'-sparse-v1-strict-with-owned8.json'
    $taskNarrative = 'outputs/n26-'+$taskPair.word+'-strict-executor-enumeration-progress-'+$taskPair.date+'.md'
    $taskContract = 'outputs/n26-stage'+$taskVersion+'-sparse-v1-executor-contract-regression-v1.json'
    foreach ($taskRequired in @("$taskStage/VERIFIED.json",$taskStageReplay,"$taskCatalog/VERIFIED.json",$taskCatalogReplay,$taskNarrative,$taskContract)) {
        if (-not (Test-Path -LiteralPath $taskRequired)) {
            throw ('Stage'+$taskVersion+' standalone evidence is incomplete. Preserve prior completed pairs.')
        }
    }
    foreach ($taskTarget in @(
        $taskCurrent,
        $taskFinalTarget,
        $taskCurrent.Replace('.json','-semantic-core.json'),
        $taskCurrent.Replace('.json','-executor-admission.json'),
        $taskCurrent.Replace('.json','-semantic-core-closed-type-pool.json'),
        $taskCurrent.Replace('.json','-semantic-core-closed-receipt-checks.json'),
        $taskCurrent.Replace('.json','-semantic-core-terminal-obligations.json'),
        $taskCurrent.Replace('.json','-closed-type-pool.json'),
        $taskCurrent.Replace('.json','-closed-receipt-checks.json'),
        $taskCurrent.Replace('.json','-terminal-obligations.json')
    )) {
        if (Test-Path -LiteralPath $taskTarget) {
            throw ('Stage'+$taskVersion+' current/final target or partial output exists. Inspect; do not restart.')
        }
    }
    & $taskPython work/audit_stage_catalogue_with_executor_contract.py --parent-audit $taskParentAudit --parent-digest-recheck $taskParentFinal --stage $taskStage --stage-replay $taskStageReplay --catalog $taskCatalog --catalog-replay $taskCatalogReplay --narrative $taskNarrative --dependency-note outputs/n26-n8-theorem-import-source-review-20261010.md --family-scope outputs/n26-new-scope-v1 --contract-regression $taskContract --output $taskCurrent
    if ($LASTEXITCODE -ne 0) {
        throw ('Stage'+$taskVersion+' strict complete-current failed. Preserve partials; later joins not started.')
    }
    & $taskPython work/recheck_current_stage_catalogue_inventory.py --current-audit $taskCurrent --stage $taskStage --stage-replay $taskStageReplay --catalog $taskCatalog --catalog-replay $taskCatalogReplay --report $taskFinalTarget
    if ($LASTEXITCODE -ne 0) {
        throw ('Stage'+$taskVersion+' independent final failed. Later joins not started.')
    }
    $taskParentAudit = $taskCurrent
    $taskParentFinal = $taskFinalTarget
}
