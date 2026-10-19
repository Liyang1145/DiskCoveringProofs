param([string]$Tag='a25-canonical-finite-certificates-20261013')
$ErrorActionPreference='Stop'
# Check-A25ManifestReadiness-20261013.ps1   (owner: m4, A25 landing)
#
# READ-ONLY. Replicates the exact greenness rule of
# Invoke-A21Manifest-20261007.ps1 -- including its NON-RECURSIVE,
# $PSScriptRoot-scoped evidence discovery -- without writing any manifest.
# Invoke-A21Manifest is append-only and throws if the tag exists, so the real
# manifest must not be burned while any module is still red. This guard answers
# "would the manifest come out 233/233?" first, and if not, names each red
# module along with WHY and whether a result.json for it exists anywhere under
# evidence\ (so a path-scoping bug is distinguishable from a missing build).
#
# Rule (verbatim from Invoke-A21Manifest-20261007.ps1 lines 18-51):
#   reports = *.log.result.json directly in evidence\codex-handoff\
#   gate  g = newest report with !build, file=='N11Formalization/<M>.lean',
#             exit 0, unchanged, sha256_before==sha256_after==CURRENT file hash
#   build b = newest report with build, file=='N11Formalization.<M>', exit 0
#   read gate log text: >=1 'depends on axioms:' report, no axiom outside
#             {propext,Classical.choice,Quot.sound}, and no match of
#             sorryAx|native_decide|Lean.ofReduceBool|error[:(]
#   green = g exists AND b exists AND olean exists AND b.started >= g.started
#           AND audited AND !bad AND root text contains 'import N11Formalization.<M>'

$project=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..'))
$lean=Join-Path $project 'lean'
$lib=Join-Path $lean '.lake\build\lib\lean\N11Formalization'
$root=Join-Path $lean 'N11Formalization.lean'
$rootText=Get-Content -LiteralPath $root -Raw
$allowed=@('propext','Classical.choice','Quot.sound')
$base=Get-Content -LiteralPath (Join-Path $PSScriptRoot 'a24-active-interval-certificates-20261008-manifest.json') -Raw|ConvertFrom-Json
$extras=@('SharedMomentFactorPermutation','ActualCanonicalFaceCoordinates',
 'ActualCanonicalMomentTransport','ActualSharedMomentSharpConstant',
 'RationalTrigLocalLipschitz','SharedMomentFactorLocalGradientCertificate',
 'SharedMomentFacePlaneCertificate','SharedMomentFacePlaneDirectCertificate',
 'SharedMomentFacePlaneGradientCertificate','SharedMomentFacePlaneRoundedGradientCertificate',
 'MetricSectorRationalCellCertificate','MetricSectorLocalGradientCertificate',
 'SharedMomentFiniteFactorCertificate','SharedMomentEfficientFactorCertificate',
 'ActualCanonicalSharedMomentConsumer','CanonicalSharedMomentFiniteCertificate',
 'CanonicalBalancedGraphOrbits','CanonicalSharedMomentOrbitTransport',
 'SharedMomentConcreteLeafControls','SharedMomentConcreteSwitchBatch',
 'SharedMomentConcreteSectorControls','SharedMomentA25CertificateControls',
 'SharedMomentConcreteFace1Data','SharedMomentConcreteFace1Part0',
 'SharedMomentConcreteFace1Part1','SharedMomentConcreteFace1Part2',
 'SharedMomentConcreteFace1Part3','SharedMomentConcreteFace1Certificate',
 'CanonicalBalancedFiniteClassCertificate','SharedMomentConcreteSectorGradientControls')
$names=@($base.modules|ForEach-Object{$_.module})+@($extras|ForEach-Object{"N11Formalization.$_"})
Write-Output "scope check: expected 233, names=$($names.Count), unique=$(@($names|Sort-Object -Unique).Count)"

# --- exactly the manifest's discovery: non-recursive, $PSScriptRoot only
$reports=@(Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.log.result.json' -File|ForEach-Object{
  try{$d=Get-Content -LiteralPath $_.FullName -Raw|ConvertFrom-Json}catch{return}
  [pscustomobject]@{path=$_.FullName;data=$d}
})
Write-Output "visible reports in $PSScriptRoot = $($reports.Count)   (non-recursive)"

# --- every result.json anywhere under evidence\, for the red-module diagnosis.
# This recursive scan is the expensive part of the script, so it is built LAZILY:
# only when at least one module is red does the diagnostic matter. Doing it
# unconditionally made the script take many minutes even in the all-green case.
$everywhereScript={
  $acc=@()
  Get-ChildItem -LiteralPath (Join-Path $project 'evidence') -Recurse -Filter '*.log.result.json' -File -ErrorAction SilentlyContinue|ForEach-Object{
    try{$d=Get-Content -LiteralPath $_.FullName -Raw|ConvertFrom-Json}catch{return}
    $acc+=[pscustomobject]@{path=$_.FullName;data=$d}
  }
  $acc
}

$everywhere=$null
$rows=@()
foreach($module in $names){
  $short=$module -replace '^N11Formalization\.',''
  $file="N11Formalization/$short.lean"
  $src=Join-Path $lean ($file -replace '/','\')
  $sha=$(if(Test-Path -LiteralPath $src){(Get-FileHash -LiteralPath $src -Algorithm SHA256).Hash}else{$null})
  $g=@($reports|Where-Object{!$_.data.build -and ($_.data.file -replace '\\','/') -eq $file -and
    $_.data.exit -eq 0 -and $_.data.unchanged -and $_.data.sha256_before -eq $sha -and
    $_.data.sha256_after -eq $sha}|Sort-Object {$_.data.finished} -Descending|Select-Object -First 1)
  $b=@($reports|Where-Object{$_.data.build -and $_.data.file -eq $module -and $_.data.exit -eq 0}|
    Sort-Object {$_.data.finished} -Descending|Select-Object -First 1)
  $olean=Join-Path $lib "$short.olean"
  $bad=$false;$audited=$false;$reasons=@()
  if($g.Count){
    $text=Get-Content -LiteralPath $g[0].data.log -Raw
    $hits=[regex]::Matches($text,'depends on axioms:\s*\[([^\]]*)\]','Singleline')
    $audited=$hits.Count -gt 0
    foreach($hit in $hits){foreach($a in ($hit.Groups[1].Value -split ',')){
      if($a.Trim() -and $a.Trim() -notin $allowed){$bad=$true}
    }}
    if($text -match 'sorryAx|native_decide|Lean\.ofReduceBool|error[:(]'){$bad=$true}
  } else { $reasons+='no current-hash gate visible' }
  if(!$b.Count){$reasons+='no build visible'}
  if(!(Test-Path -LiteralPath $olean)){$reasons+='no olean'}
  if($g.Count -and $b.Count -and !($b[0].data.started -ge $g[0].data.started)){$reasons+='build.started < gate.started'}
  if($g.Count -and !$audited){$reasons+='gate log has no axiom report'}
  if($bad){$reasons+='gate log has forbidden/unpermitted axiom'}
  if(!$rootText.Contains("import $module")){$reasons+='root import MISSING'}
  $green=($reasons.Count -eq 0)
  # diagnostic: where else does this module have evidence? (lazy, see above)
  if(!$green){
    if($null -eq $everywhere){$everywhere=@(& $everywhereScript)}
    $elsewhere=@($everywhere|Where-Object{
      ($_.data.file -replace '\\','/') -eq $file -or $_.data.file -eq $module
    }|ForEach-Object{$_.path -replace [regex]::Escape((Join-Path $project 'evidence')),'evidence'})
  } else { $elsewhere=@() }
  $rows+=[pscustomobject]@{module=$short;green=$green;why=($reasons -join ', ');
    gate=$(if($g.Count){$g[0].data.log -replace [regex]::Escape($PSScriptRoot),'…'}else{$null});
    build=$(if($b.Count){$b[0].data.log -replace [regex]::Escape($PSScriptRoot),'…'}else{$null});
    other_evidence_dir_count=@($elsewhere|Where-Object{$_ -notlike 'evidence\codex-handoff\*'}).Count}
}
$red=@($rows|Where-Object{!$_.green})
Write-Output ""
Write-Output "WOULD-BE MANIFEST: green=$($rows.Count-$red.Count)/$($rows.Count)  red=$($red.Count)"
if($red.Count){
  Write-Output ""
  Write-Output "RED MODULES (name | reason | evidence under OTHER dirs = path-scoping suspect):"
  $red|Format-Table -AutoSize -Wrap
}
$byReason=@($red|Group-Object why|Sort-Object Count -Descending)
if($byReason.Count){Write-Output ""; Write-Output 'reason histogram:'; $byReason|Select-Object Count,Name|Format-Table -AutoSize}
$rows|ConvertTo-Json -Depth 5|Set-Content -LiteralPath (Join-Path $PSScriptRoot "a25-readiness-$Tag-$(Get-Date -Format 'yyyyMMdd-HHmmss').json") -Encoding utf8
Write-Output "readiness detail -> $(Join-Path $PSScriptRoot "a25-readiness-$Tag-*.json")"