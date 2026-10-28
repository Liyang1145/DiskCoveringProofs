param(
  [string]$Root = 'E:\ai4math2\research-2026\n11-formalization',
  [int]$WaitMinutes = 180,
  [string]$Py = 'C:\Users\UserX\.dsh\dsh-runtimes\dsh-primary-runtime\dependencies\python\python.exe'
)
# Unattended stage-2 close-out. Runs ONLY when every rest1182 H module is green.
#   1. wait for the build driver's "ALL DONE" marker
#   2. abort (and report) if any module log says exit != 0
#   3. build Paid16GeneralNext1182, then EnergyTerminalBatchB13{,Main}
#   4. append the stage-2 root import (idempotent, hash-guarded) and rebuild the root
#   5. gate ProbeEnergyRest1182.lean
# Every Lean call goes through the canonical mutex wrapper.
$ErrorActionPreference = 'Continue'
$d       = Join-Path $Root 'evidence\energy-emit-20261028'
$logdir  = Join-Path $d 'logs'
$wrapper = Join-Path $Root 'evidence\resume-lead\Invoke-LeanSerial20261013.ps1'
$prog    = Join-Path $logdir 'rest1182H\progress.txt'
$status  = Join-Path $d 'stage2-closeout-status.json'
$steps   = @()

function Note($m) { Write-Output $m; "`"$(Get-Date -Format o)`" $m" | Add-Content (Join-Path $d 'stage2-closeout.log') }

# ---- 1. wait -------------------------------------------------------------
$deadline = (Get-Date).AddMinutes($WaitMinutes)
while ((Get-Date) -lt $deadline) {
  if ((Test-Path $prog) -and ((Get-Content $prog -Raw) -match 'ALL DONE')) { break }
  Start-Sleep 30
}
if (-not ((Get-Content $prog -Raw) -match 'ALL DONE')) { Note 'TIMEOUT waiting for rest1182 build driver'; exit 2 }
Note 'build driver finished'

# ---- 2. per-module gate ------------------------------------------------
$bad = @()
foreach ($k in 26..82) {
  $res = Join-Path $logdir ("rest1182H\build-Paid16GeneralH{0:D2}.log.result.json" -f $k)
  if (-not (Test-Path $res)) { $bad += "H${k}:missing"; continue }
  $j = Get-Content $res -Raw | ConvertFrom-Json
  if ($j.exit -ne 0) { $bad += "H${k}:exit$($j.exit)" }
}
if ($bad.Count -gt 0) { Note ("ABORT, non-green modules: " + ($bad -join ',')); exit 3 }
Note '57/57 rest1182 H modules exit 0'

# ---- 3. aggregate + dispatch ------------------------------------------
$dummy = @()
Set-Content (Join-Path $d 'agg1182-list.txt')  'N11Formalization.Paid16GeneralNext1182' -NoNewline
Set-Content (Join-Path $d 'b13-list.txt') @('N11Formalization.EnergyTerminalBatchB13','N11Formalization.EnergyTerminalBatchB13Main') -NoNewline
& pwsh -NoProfile -ExecutionPolicy Bypass -File (Join-Path $d 'build-modules.ps1') -List (Join-Path $d 'agg1182-list.txt') -Tag 'agg1182' | Out-Null
$agg = Join-Path $logdir 'agg1182\build-Paid16GeneralNext1182.log.result.json'
if (-not (Test-Path $agg) -or ((Get-Content $agg -Raw | ConvertFrom-Json).exit -ne 0)) { Note 'ABORT: aggregate not green'; exit 4 }
Note 'aggregate Paid16GeneralNext1182 green'

& pwsh -NoProfile -ExecutionPolicy Bypass -File (Join-Path $d 'build-modules.ps1') -List (Join-Path $d 'b13-list.txt') -Tag 'b13' | Out-Null
foreach ($m in @('EnergyTerminalBatchB13','EnergyTerminalBatchB13Main')) {
  $r = Join-Path $logdir ("b13\build-" + $m + ".log.result.json")
  if (-not (Test-Path $r) -or ((Get-Content $r -Raw | ConvertFrom-Json).exit -ne 0)) { Note ("ABORT: $m not green"); exit 5 }
}
Note 'dispatch EnergyTerminalBatchB13{,Main} green'

# ---- 4. root import + rebuild -----------------------------------------
$cur = (Get-FileHash -LiteralPath (Join-Path $Root 'lean\N11Formalization.lean') -Algorithm SHA256).Hash
& $Py (Join-Path $d 'patch_root.py') $cur 'N11Formalization.EnergyTerminalBatchB13Main' (Join-Path $d 'root-import-stage2.txt') | Out-Null
$new = (Get-FileHash -LiteralPath (Join-Path $Root 'lean\N11Formalization.lean') -Algorithm SHA256).Hash
Note ("root import appended: " + $cur + " -> " + $new)
& pwsh -NoProfile -ExecutionPolicy Bypass -File (Join-Path $d 'build-modules.ps1') -List (Join-Path $d 'root-list.txt') -Tag 'root2' | Out-Null
$rr = Join-Path $logdir 'root2\build-N11Formalization.log.result.json'
if (-not (Test-Path $rr) -or ((Get-Content $rr -Raw | ConvertFrom-Json).exit -ne 0)) { Note 'ABORT: root build not green'; exit 6 }
Note 'root build green'

# ---- 5. probe ----------------------------------------------------------
& $wrapper -File 'ProbeEnergyRest1182.lean' -Log (Join-Path $logdir 'probe-stage2.log') -MutexWaitSeconds 5400 | Out-Null
$pr = Join-Path $logdir 'probe-stage2.log.result.json'
$pj = Get-Content $pr -Raw | ConvertFrom-Json
Note ("probe exit=" + $pj.exit)
[ordered]@{ rootBefore = $cur; rootAfter = $new; probeExit = $pj.exit
            probeUnchanged = $pj.unchanged; finished = (Get-Date).ToString('o') } |
  ConvertTo-Json | Set-Content -Encoding utf8 $status
Note ("DONE, status -> " + $status)