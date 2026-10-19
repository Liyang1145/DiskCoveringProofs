param([Parameter(Mandatory=$true)][string]$Tag,[switch]$AssertAllGreen,
 [string]$BaseManifest='recover-a20-backbone-20261007-manifest.json',
 [string[]]$ExtraModules=@(
 'ActualOrderedMetricGraphs','ActualEarOwnedWidth','MetricAreaMaskedGridDual',
 'ActualEarMaskedGridBridge','MetricAreaMaskedRationalCertificate',
 'ActualSharedMomentData','MetricSectorCompactRegularity','CompactBoxGridCertificate',
 'MetricSectorBoxCertificate','ActualSharedMomentDual','ActualSharedMomentMaskedDual'),
 [int]$ExpectedTotal=187)
$ErrorActionPreference='Stop'
$outPath=Join-Path $PSScriptRoot "$Tag-manifest.json"
if(Test-Path -LiteralPath $outPath){throw "Append-only tag already exists: $Tag"}
$project=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..'))
$base=Get-Content -LiteralPath (Join-Path $PSScriptRoot $BaseManifest) -Raw|ConvertFrom-Json
$names=@($base.modules|ForEach-Object{$_.module})+@($ExtraModules|ForEach-Object{"N11Formalization.$_"})
if($names.Count -ne $ExpectedTotal -or @($names|Sort-Object -Unique).Count -ne $ExpectedTotal){
 throw "Bad$ExpectedTotal-module scope"
}
$reports=@(Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.log.result.json' -File|ForEach-Object{
 @{path=$_.FullName;data=(Get-Content -LiteralPath $_.FullName -Raw|ConvertFrom-Json)}
})
$root=Join-Path $project 'lean\N11Formalization.lean'
$rootText=Get-Content -LiteralPath $root -Raw
$rows=@()
foreach($module in $names){
 $file=($module -replace '\.','/')+'.lean'
 $source=Join-Path (Join-Path $project 'lean') $file
 $sha=(Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash
 # Windows reports may use either path separator for the same source.
 # Preserve historical evidence while comparing canonical relative paths.
 $g=@($reports|Where-Object{!$_.data.build -and ($_.data.file -replace '\\','/') -eq $file -and
   $_.data.exit -eq 0 -and $_.data.unchanged -and $_.data.sha256_before -eq $sha -and
   $_.data.sha256_after -eq $sha}|Sort-Object {$_.data.finished} -Descending|Select-Object -First 1)
 $b=@($reports|Where-Object{$_.data.build -and $_.data.file -eq $module -and $_.data.exit -eq 0}|
   Sort-Object {$_.data.finished} -Descending|Select-Object -First 1)
 $olean=Join-Path $project ("lean\.lake\build\lib\lean\"+($file -replace '\.lean$','.olean'))
 $bad=$false;$audited=$false
 if($g.Count){
   $text=Get-Content -LiteralPath $g[0].data.log -Raw
   $hits=[regex]::Matches($text,'depends on axioms:\s*\[([^\]]*)\]','Singleline')
   $audited=$hits.Count -gt 0
   foreach($hit in $hits){foreach($a in ($hit.Groups[1].Value -split ',')){
     if($a.Trim() -and $a.Trim() -notin @('propext','Classical.choice','Quot.sound')){$bad=$true}
   }}
   if($text -match 'sorryAx|native_decide|Lean\.ofReduceBool|error[:(]'){$bad=$true}
 }
 $green=($g.Count -eq 1 -and $b.Count -eq 1 -and (Test-Path -LiteralPath $olean) -and
   $b[0].data.started -ge $g[0].data.started -and $audited -and !$bad -and
   $rootText.Contains("import $module"))
 $rows+=[ordered]@{module=$module;source=$source;sha256=$sha;module_green=$green;
   standalone_log=$(if($g.Count){$g[0].data.log}else{$null});
   module_log=$(if($b.Count){$b[0].data.log}else{$null});standard_axioms_only=($audited -and !$bad)}
}
$unpaid=@($rows|Where-Object{!$_.module_green})
$out=[ordered]@{tag=$Tag;timestamp=(Get-Date).ToString('o');project=$project;
 root_sha256=(Get-FileHash -LiteralPath $root).Hash;modules_total=$ExpectedTotal;
 modules_green=($ExpectedTotal-$unpaid.Count);modules=$rows;incomplete_modules=@($unpaid|ForEach-Object{$_.module});
 scope='Actual framework MODULE evidence; root acceptance separate; n11 INCOMPLETE'}
$out|ConvertTo-Json -Depth 8|Set-Content -LiteralPath $outPath -Encoding utf8
Write-Output "manifest=$outPath module-green=$($out.modules_green)/$ExpectedTotal"
if($AssertAllGreen -and $unpaid.Count){throw 'Unverified modules remain'}
