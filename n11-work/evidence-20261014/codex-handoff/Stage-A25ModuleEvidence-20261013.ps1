param(
 [Parameter(Mandatory=$true)][string[]]$Modules,
 [string]$Tag='a25-canonical-finite-certificates-20261013',
 [switch]$WhatIfOnly
)
$ErrorActionPreference='Stop'
# Stage-A25ModuleEvidence-20261013.ps1   (owner: m4, A25 landing)
#
# WHY THIS EXISTS. Invoke-A21Manifest-20261007.ps1 discovers evidence with
#   Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.log.result.json' -File
# i.e. NON-RECURSIVE and scoped to evidence\codex-handoff\. Every green
# gate/build a teammate wrote into evidence\a25-landing-20261013\mN\ is therefore
# INVISIBLE to the manifest. That script is shared by every historical acceptance
# and must stay byte-identical, so instead of editing it we restage the evidence
# into evidence\codex-handoff\ here.
#
# WHAT IT DOES. For each module (FULL dotted name, as the manifest uses):
#   * candidate gate  = newest non-build result.json in the m-dirs with exit 0,
#                       file == 'N11Formalization/<M>.lean', unchanged, and
#                       sha256_before == sha256_after == CURRENT source hash
#                       (so a stale gate can never be promoted);
#   * candidate build = newest build result.json in the m-dirs with exit 0 and
#                       file == 'N11Formalization.<M>';
#   * copy the result.json + its .log + its .stderr into codex-handoff under a
#     fresh uniquely-named file and rewrite ONLY the JSON's `log` field to point
#     at the copy. Every other field is preserved verbatim, then re-read and
#     asserted.
#
# RULE-3 PAIRING GUARD. The manifest independently picks the newest gate and the
# newest build VISIBLE in codex-handoff and requires build.started >=
# gate.started. Naively staging a fresh gate can therefore REGRESS a module that
# was already green (newer gate, older visible build). So a candidate gate is
# staged only if some build at least as new will be visible after this run --
# either already present or staged in the same run. A candidate build is staged
# only if it is not older than the gate the manifest will pick. Regressions are
# reported, never silently introduced.
#
# APPEND-ONLY. Staged names embed origin timestamps plus a collision counter; the
# mapping file is stamped per run. Nothing existing is ever overwritten.
#
# This script only COPIES. It never invents a green result: if a teammate has not
# produced the build, the module stays red and the guard reports it.

$project=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..'))
$incoming=Join-Path $project 'evidence\a25-landing-20261013'
$dest=$PSScriptRoot
$lean=Join-Path $project 'lean'
$lib=Join-Path $lean '.lake\build\lib\lean\N11Formalization'
$runStamp=(Get-Date).ToString('yyyyMMdd-HHmmss')
$mapPath=Join-Path $dest "a25-staged-evidence-map-$Tag-$runStamp.json"
if(Test-Path -LiteralPath $mapPath){throw "Append-only staging map already exists: $mapPath"}
if(!(Test-Path -LiteralPath $incoming)){throw "No incoming evidence dir: $incoming"}

function Read-Reports([string]$root,[switch]$Recurse){
  $opt=@{LiteralPath=$root;Filter='*.log.result.json';File=$true;ErrorAction='SilentlyContinue'}
  if($Recurse){$opt.Recurse=$true}
  Get-ChildItem @opt|ForEach-Object{
    try{$d=Get-Content -LiteralPath $_.FullName -Raw|ConvertFrom-Json}catch{return}
    [pscustomobject]@{path=$_.FullName;data=$d}
  }
}

$raw=@(Read-Reports $incoming -Recurse)
$already=@(Read-Reports $dest)
Write-Output "incoming result.json parsed=$($raw.Count) (under $incoming)"
Write-Output "already-visible reports in codex-handoff=$($already.Count)"

function Get-Newest($set,[bool]$isBuild,[string]$module,[string]$rel,[string]$sha){
  $wantFile=$(if($isBuild){$module}else{$rel})
  $c=@($set|Where-Object{
    $_.data.build -eq $isBuild -and $_.data.exit -eq 0 -and
    (($_.data.file -replace '\\','/')) -eq $wantFile})
  if(!$isBuild){
    $c=@($c|Where-Object{$_.data.unchanged -and $_.data.sha256_before -eq $sha -and $_.data.sha256_after -eq $sha})
  }
  @($c|Sort-Object {$_.data.finished})|Select-Object -Last 1
}

$map=@();$readout=@()
foreach($module in $Modules){
  $short=$module -replace '^N11Formalization\.',''
  $rel="N11Formalization/$short.lean"
  $src=Join-Path $lean ($rel -replace '/','\')
  $sha=$(if(Test-Path -LiteralPath $src){(Get-FileHash -LiteralPath $src -Algorithm SHA256).Hash}else{$null})
  $notes=@()
  if(!$sha){$notes+='NO SOURCE FILE'}

  $cGate =@(Get-Newest $raw   $false $module $rel $sha)
  $cBuild=@(Get-Newest $raw   $true  $module $rel $sha)
  $vGate =@(Get-Newest $already $false $module $rel $sha)
  $vBuild=@(Get-Newest $already $true  $module $rel $sha)

  # the newest build that will be visible after this run
  $buildStarts=@()
  if($cBuild.Count){$buildStarts+=[datetime]$cBuild[0].data.started}
  if($vBuild.Count){$buildStarts+=[datetime]$vBuild[0].data.started}
  $newestBuildStart=$(if($buildStarts.Count){($buildStarts|Sort-Object)[-1]}else{$null})

  foreach($kind in @('gate','build')){
    $isBuild=($kind -eq 'build')
    $c=$(if($isBuild){$cBuild}else{$cGate})
    if(!$c.Count){$notes+="no $kind in m-dirs";continue}
    if($isBuild){
      if($vGate.Count -and ([datetime]$c[0].data.started -lt [datetime]$vGate[0].data.started)){
        $notes+='build NOT staged: older than the gate the manifest will pick';continue}
    } else {
      if($newestBuildStart -eq $null -or $newestBuildStart -lt [datetime]$c[0].data.started){
        $notes+='gate NOT staged: rule3 would break (no build at least as new)';continue}
    }
    $stamp=(($c[0].data.finished) -replace '[^0-9]','')
    if($stamp.Length -gt 14){$stamp=$stamp.Substring(0,14)}
    $staged=Join-Path $dest "a25stg-$short-$kind-$stamp.log"
    # IDEMPOTENCE. Staging is re-run right before the manifest (and may be re-run
    # by hand), so re-staging the SAME evidence must REUSE the existing copy
    # rather than multiply it. Deliberately implemented as a deterministic-path
    # check (not a scan over $already) so that re-running cannot throw. Nothing is
    # ever overwritten: a genuine difference falls through to a fresh unique name.
    $reuseOk=$false
    if((Test-Path -LiteralPath "$staged.result.json") -and (Test-Path -LiteralPath $staged)){
      $prev=Get-Content -LiteralPath "$staged.result.json" -Raw|ConvertFrom-Json
      $reuseOk=([bool]$prev.build -eq $isBuild) -and
               ("$($prev.finished)" -eq "$($c[0].data.finished)") -and
               ("$($prev.sha256_before)" -eq "$($c[0].data.sha256_before)")
    }
    if($reuseOk){
      $notes+="$kind already staged (reused)"
      $map+=[ordered]@{module=$module;kind=$kind;staged_log=$staged;staged_result_json="$staged.result.json";
        origin_result_json=$c[0].resultPath;origin_log=$c[0].data.log;started=$c[0].data.started;
        finished=$c[0].data.finished;sha256_before=$c[0].data.sha256_before;sha256_current=$sha;
        source_hash_matches=($c[0].data.sha256_before -eq $sha);reused=$true;dry_run=$false}
      continue
    }
    if(Test-Path -LiteralPath $staged){$staged=Join-Path $dest "a25stg-$short-$kind-$stamp-$($map.Count).log"}
    if(Test-Path -LiteralPath $staged){$notes+="staged collision $kind";continue}
    $originLog=$c[0].data.log
    if($WhatIfOnly){
      $notes+="$kind WOULD stage <- $($c[0].resultPath)"
      $map+=[ordered]@{module=$module;kind=$kind;staged_log=$staged;origin_result_json=$c[0].resultPath;
        origin_finished=$c[0].data.finished;sha256_before=$c[0].data.sha256_before;sha256_current=$sha;dry_run=$true}
      continue
    }
    if(!(Test-Path -LiteralPath $originLog)){$notes+="$kind ORIGIN LOG MISSING: $originLog";continue}
    # NO-REGRESSION AUDIT CHECK. A staged gate replaces whatever the manifest
    # would otherwise pick, so it must itself pass the rule-5 audit: at least one
    # 'depends on axioms:' report, no axiom outside the allowed three, and none of
    # sorryAx|native_decide|Lean.ofReduceBool|error[:(]. Otherwise staging would
    # turn a currently-green module red; skip it and say so.
    if(!$isBuild){
      $txt=Get-Content -LiteralPath $originLog -Raw
      $hits=[regex]::Matches($txt,'depends on axioms:\s*\[([^\]]*)\]','Singleline')
      $badAxiom=$false
      foreach($hit in $hits){foreach($a in ($hit.Groups[1].Value -split ',')){
        $x=$a.Trim(); if($x -and $x -notin @('propext','Classical.choice','Quot.sound')){$badAxiom=$true}}}
      if(!$hits.Count){$notes+='gate NOT staged: log has no axiom report (rule 5)';continue}
      if($badAxiom){$notes+='gate NOT staged: log has an unpermitted axiom (rule 5)';continue}
      if($txt -match 'sorryAx|native_decide|Lean\.ofReduceBool|error[:(]'){
        $notes+='gate NOT staged: log matches forbidden pattern (rule 5)';continue}
    }
    Copy-Item -LiteralPath $originLog -Destination $staged
    if(Test-Path -LiteralPath "$originLog.stderr"){Copy-Item -LiteralPath "$originLog.stderr" -Destination "$staged.stderr"}
    $d=$c[0].data
    $d.log=$staged
    $d|ConvertTo-Json -Depth 6|Set-Content -LiteralPath "$staged.result.json" -Encoding utf8
    $chk=Get-Content -LiteralPath "$staged.result.json" -Raw|ConvertFrom-Json
    if($chk.log -ne $staged){throw "Staged JSON log field wrong for $module/$kind"}
    if($chk.file -ne $d.file -or $chk.build -ne $d.build -or $chk.exit -ne $d.exit -or
       "$($chk.started)" -ne "$($d.started)" -or "$($chk.finished)" -ne "$($d.finished)" -or
       $chk.sha256_before -ne $d.sha256_before -or $chk.sha256_after -ne $d.sha256_after -or
       $chk.unchanged -ne $d.unchanged){throw "Staged JSON field drift for $module/$kind"}
    $map+=[ordered]@{module=$module;kind=$kind;staged_log=$staged;staged_result_json="$staged.result.json";
      origin_result_json=$c[0].resultPath;origin_log=$originLog;started=$d.started;finished=$d.finished;
      sha256_before=$d.sha256_before;sha256_current=$sha;source_hash_matches=($d.sha256_before -eq $sha);dry_run=$false}
  }
  $gs=@($map|Where-Object{$_.module -eq $module -and $_.kind -eq 'gate'})
  $bs=@($map|Where-Object{$_.module -eq $module -and $_.kind -eq 'build'})
  $readout+=[pscustomobject]@{module=$short;source=[bool]$sha;gate=($gs.Count -gt 0);build=($bs.Count -gt 0);
    olean=(Test-Path -LiteralPath (Join-Path $lib "$short.olean"));notes=($notes -join '; ')}
}
if(!$WhatIfOnly){
  $map|ConvertTo-Json -Depth 6|Set-Content -LiteralPath $mapPath -Encoding utf8
  Write-Output "staged map=$mapPath entries=$($map.Count)"
}
$readout|Format-Table -AutoSize
Write-Output "STAGED-READY: $(@($readout|Where-Object{$_.source -and $_.gate -and $_.build -and $_.olean}).Count)/$($Modules.Count)"