param(
  [Parameter(Mandatory=$true)][string]$List,   # one module name per line
  [Parameter(Mandatory=$true)][string]$Tag,    # log subdirectory tag
  [string]$Root = 'E:\ai4math2\research-2026\n11-formalization'
)
# Serial module-builder for emitted energy packets.
# Every Lean invocation goes through the canonical mutex wrapper
# (Invoke-LeanSerial20261013.ps1). Never launches unlocked.
$ErrorActionPreference = 'Continue'
$wrapper = Join-Path $Root 'evidence\resume-lead\Invoke-LeanSerial20261013.ps1'
$outdir  = Join-Path $Root ("evidence\energy-emit-20261028\logs\" + $Tag)
New-Item -ItemType Directory -Force $outdir | Out-Null
$progress = Join-Path $outdir 'progress.txt'
$mods = Get-Content $List | Where-Object { $_.Trim() -ne '' } | ForEach-Object { $_.Trim() }
foreach ($m in $mods) {
  $leaf = ($m -split '\.')[-1]
  $log  = Join-Path $outdir ("build-" + $leaf + ".log")
  $res  = "$log.result.json"
  if (Test-Path $res) {
    $r = Get-Content $res -Raw | ConvertFrom-Json
    if ($r.exit -eq 0) { "skip $m already exit=0" | Add-Content $progress; continue }
  }
  $t0 = Get-Date
  "start $m $($t0.ToString('o'))" | Add-Content $progress
  & $wrapper -File $m -Log $log -Build -MutexWaitSeconds 5400 | Out-Null
  $code = $null
  if (Test-Path $res) { $code = (Get-Content $res -Raw | ConvertFrom-Json).exit }
  $dt = [int]((Get-Date) - $t0).TotalSeconds
  "end   $m exit=$code ${dt}s $((Get-Date).ToString('o'))" | Add-Content $progress
}
"ALL DONE $((Get-Date).ToString('o'))" | Add-Content $progress
