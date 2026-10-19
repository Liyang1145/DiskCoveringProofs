param([string]$Tag='dbm-tree-20260930')
$ErrorActionPreference='Stop'
$p=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..'))
$root=Join-Path $p 'lean\N11Formalization.lean'
function Get-OwnedLeanSources {
  $leanPath=Join-Path $p 'lean'
  Get-ChildItem -LiteralPath $leanPath -Filter '*.lean' -File
  foreach($dir in Get-ChildItem -LiteralPath $leanPath -Directory){
    if($dir.Name -ne '.lake'){Get-ChildItem -LiteralPath $dir.FullName -Recurse -Filter '*.lean' -File}
  }
}
$mutex=[Threading.Mutex]::new($false,'Local\N11Formalization_LeanSerial_20260929')
$held=$false
try {
  try {$held=$mutex.WaitOne(600000)} catch [Threading.AbandonedMutexException]{$held=$true}
  if(!$held){throw 'Root pair serial mutex wait exceeded 10min'}
  $rows=@()
  # All owned Lean sources: library modules AND top-level root/probes.
  # Do not scan .lake/packages: these are external dependency sources.
  $coneFiles=@(Get-OwnedLeanSources)
  $before=@{};foreach($f in $coneFiles){$before[$f.FullName]=(Get-FileHash $f.FullName).Hash}
  $rootBefore=(Get-FileHash $root).Hash
  foreach($i in 1..2){
    $log=Join-Path $PSScriptRoot ("root-$Tag-run$i.log")
    $start=(Get-Date).ToString('o')
    & pwsh -NoProfile -File (Join-Path $p 'verify.ps1') 1> $log 2> "$log.stderr"
    $code=$LASTEXITCODE
    $changed=@();foreach($f in $coneFiles){
      if(!(Test-Path -LiteralPath $f.FullName)){$changed+=("deleted:"+$f.FullName)}
      elseif($before[$f.FullName] -ne (Get-FileHash -LiteralPath $f.FullName).Hash){$changed+=$f.FullName}
    }
    $afterFiles=@(Get-OwnedLeanSources)
    foreach($f in $afterFiles){if(!$before.ContainsKey($f.FullName)){$changed+=("added:"+$f.FullName)}}
    $rootAfter=(Get-FileHash $root).Hash
    $txt=Get-Content $log -Raw
    $mods=@([regex]::Matches($txt,'(?:Built|Replayed) (N11Formalization(?:\.[A-Za-z0-9_]+)*)')|ForEach-Object{$_.Groups[1].Value}|Sort-Object -Unique)
    $r=[ordered]@{run=$i;started=$start;finished=(Get-Date).ToString('o');exit=$code;root_sha256_before=$rootBefore;root_sha256_after=$rootAfter;source_scope='all owned Lean sources below lean excluding .lake dependencies/build artifacts';source_count=$coneFiles.Count;unchanged=($rootBefore -eq $rootAfter -and $changed.Count -eq 0);changed_sources=$changed;reported_modules=$mods;log=$log}
    $r|ConvertTo-Json -Depth 6|Set-Content "$log.result.json"
    $rows+=$r
    ConvertTo-Json -InputObject @($rows) -Depth 8|Set-Content (Join-Path $PSScriptRoot "root-$Tag-pair.json")
    if($code -ne 0 -or $changed.Count -gt 0 -or $rootBefore -ne $rootAfter){throw "Root run$i failed or source drift; inspect $log"}
    Write-Output "Root run$i exit0, unchanged all Lean sources"
  }
} finally {if($held){$mutex.ReleaseMutex()};$mutex.Dispose()}
