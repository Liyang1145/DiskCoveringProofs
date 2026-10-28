# C450 BATCH v2 (task-9) — resume-capable, with OLEAN VERIFICATION.
#
# FIX OVER v1. In v1, GateModule read `$LASTEXITCODE` after calling the wrapper.
# If the wrapper THROWS (e.g. "N11 serial lock wait exceeded 5400 s"), a PowerShell
# `throw` does NOT update `$LASTEXITCODE` — it retains the value from the previous
# native command, typically 0. v1 would therefore have recorded exit=0 (GREEN) for a
# module that was never built. That is a silent false-positive in evidence.
#
# v2 fixes it two ways:
#   (1) the wrapper's own .result.json (written ONLY on a completed run) is the
#       source of truth for exit status; absent/stale file => NOT green;
#   (2) an independent post-gate check that the module's olean exists AND is newer
#       than the module source. No olean => not green, regardless of exit codes.
#
# RESUMABLE: modules whose gate log from THIS batch already exists with exit=0 and a
# present, fresh olean are skipped. Failed gate logs are never overwritten or deleted.
$ErrorActionPreference = 'Continue'
$W = 'E:\ai4math2\research-2026\n11-formalization'
$E = "$W\evidence\c450-emit-20261014"
$wrapper = "$W\evidence\resume-lead\Invoke-LeanSerial20261013.ps1"
$logs = "$E\logs"
$objdir = "$W\lean\.lake\build\lib\lean\N11Formalization"
[IO.Directory]::CreateDirectory($logs) | Out-Null

$stamp = Get-Date -Format 'yyyyMMdd-HHmmss'
$prog = "$E\batchv2-progress-$stamp.txt"
$jsonOut = "$E\batchv2-results-$stamp.json"
function Log($m) { "$((Get-Date).ToString('yyyy-MM-dd HH:mm:ss')) $m" | Add-Content -Encoding utf8 $prog; Write-Output $m }

Log "=== C450 BATCH v2 START $stamp ==="
$results = @()

# ---- emission is already complete and verified for indices 13..35 ----
$missingFiles = 0
foreach ($k in 13..35) {
  $mn = $k + 1
  foreach ($suf in @('Data','Segment')) {
    if (-not (Test-Path "$W\lean\N11Formalization\C450Source${mn}${suf}.lean")) { $missingFiles++ }
  }
  if ((Get-ChildItem "$W\lean\N11Formalization" -Filter "C450Source${mn}GroupedC*.lean" | Measure-Object).Count -ne 32) { $missingFiles++ }
}
if ($missingFiles -gt 0) { Log "ABORT: $missingFiles emitted-file groups missing"; exit 1 }
Log "emission verified: 23 segments x 34 files present"

function OleanFresh($leaf) {
  $ol = Join-Path $objdir "$leaf.olean"
  $src = "$W\lean\N11Formalization\$leaf.lean"
  if (-not (Test-Path $ol)) { return $false }
  if (-not (Test-Path $src)) { return $false }
  return ((Get-Item $ol).LastWriteTime -ge (Get-Item $src).LastWriteTime)
}

function GateModule($mod, $k) {
  $leaf = ($mod -split '\.')[-1]
  # resume: an existing GREEN log for this leaf from any batch run
  $prior = Get-ChildItem $logs -Filter "batch*-$leaf-*.log.result.json" -ErrorAction SilentlyContinue |
           Sort-Object LastWriteTime -Descending | Select-Object -First 1
  if ($prior) {
    $pj = Get-Content $prior.FullName -Raw | ConvertFrom-Json
    if ($pj.exit -eq 0 -and (OleanFresh $leaf)) {
      return @{ module=$mod; exit=0; log=$pj.log; realErrors=0; fatal=$false; reused=$true }
    }
  }
  $log = Join-Path $logs "batch2-$leaf-$stamp.log"
  # MUTEX CONTENTION IS MECHANICAL, NOT MATHEMATICAL. A peer legitimately holding the
  # single global Lean mutex makes the wrapper throw "N11 serial lock wait exceeded".
  # For an unattended multi-hour run in a shared workspace we RETRY with backoff
  # rather than declaring a fatal error. Other throws are surfaced immediately.
  $attempt = 0
  $maxAttempts = 8
  $code = $null
  while ($attempt -lt $maxAttempts -and $null -eq $code) {
    $attempt++
    $useLog = if ($attempt -eq 1) { $log } else { Join-Path $logs "batch2-$leaf-$stamp-att$attempt.log" }
    $threw = $false; $msg = ''
    try { & $wrapper -File $mod -Log $useLog -Build -MutexWaitSeconds 5400 | Out-Null }
    catch { $threw = $true; $msg = $_.Exception.Message }
    $log = $useLog
    if (Test-Path "$useLog.result.json") {
      $code = (Get-Content "$useLog.result.json" -Raw | ConvertFrom-Json).exit
      break
    }
    $lockWait = $threw -and ($msg -match 'serial lock wait')
    if ($lockWait) {
      Log "MUTEX WAIT $leaf (attempt $attempt/$maxAttempts) - peer holds the global mutex; backing off 120s"
      Start-Sleep -Seconds 120
      continue
    }
    # no result.json and not a lock wait -> genuine wrapper/system problem
    return @{ module=$mod; exit=-1; log=$useLog; realErrors=-1; fatal=$true
              note=$(if($threw){"wrapper threw: $msg"}else{'no result.json'}) }
  }
  if ($null -eq $code) {
    return @{ module=$mod; exit=-1; log=$log; realErrors=-1; fatal=$true
              note="mutex wait exhausted after $maxAttempts attempts" }
  }
  if ($code -ne 0) {
    $txt = Get-Content $log -Raw -ErrorAction SilentlyContinue
    $readFail = (($txt -split "`n") | Where-Object { $_ -match 'failed to read file' }).Count
    if ($readFail -gt 0) {
      Log "RETRY $leaf (mathlib read failure, $readFail lines)"
      $log2 = Join-Path $logs "batch2-$leaf-$stamp-retry.log"
      try { & $wrapper -File $mod -Log $log2 -Build -MutexWaitSeconds 5400 | Out-Null }
      catch { Log "WRAPPER THREW on retry for $leaf" }
      if (Test-Path "$log2.result.json") {
        $code = (Get-Content "$log2.result.json" -Raw | ConvertFrom-Json).exit
        $log = $log2
      }
    }
  }
  # INDEPENDENT olean check regardless of exit code
  if ($code -eq 0 -and -not (OleanFresh $leaf)) {
    Log "FALSE GREEN BLOCKED: $leaf exit=0 but olean missing/stale"
    return @{ module=$mod; exit=-2; log=$log; realErrors=0; fatal=$true
              note='exit0 but no fresh olean' }
  }
  $real = 0
  $txt2 = Get-Content $log -Raw -ErrorAction SilentlyContinue
  if ($txt2) { $real = (($txt2 -split "`n") | Where-Object { $_ -match ':\d+:\d+:\s*error\s*:' }).Count }
  return @{ module=$mod; exit=$code; log=$log; realErrors=$real; fatal=($code -ne 0); reused=$false }
}

Log "--- PHASE 2: gate modules serially (resume-capable) ---"
$fatal = $null
$segTimes = @()
foreach ($k in 13..35) {
  if ($fatal) { break }
  $mn = $k + 1
  $mods = @("N11Formalization.C450Source${mn}Data")
  $mods += 1..32 | ForEach-Object { "N11Formalization.C450Source${mn}GroupedC{0:D2}" -f $_ }
  $mods += "N11Formalization.C450Source${mn}Segment"
  $segStart = Get-Date
  foreach ($m in $mods) {
    $r = GateModule $m $k
    $results += [pscustomobject]@{ phase='gate'; key="k=$k"; module=$m; exit=$r.exit
                                   log=$r.log; realErrors=$r.realErrors; fatal=$r.fatal
                                   reused=[bool]$r.reused; note=$r.note }
    if ($r.fatal) { $fatal = $r; break }
  }
  if ($fatal) { Log "FATAL at $($fatal.module) : $($fatal.note) -> STOP"; break }
  $dt = [int]((Get-Date) - $segStart).TotalSeconds
  $segTimes += $dt
  Log "SEGMENT k=$k GREEN (34 modules, ${dt}s)"
  $results | ConvertTo-Json -Depth 4 | Set-Content -Encoding utf8 $jsonOut
}

$reused = @($results | Where-Object { $_.reused }).Count
$gateFail = @($results | Where-Object { $_.phase -eq 'gate' -and $_.exit -ne 0 }).Count
Log "phase2 rows=$($results.Count) reused=$reused failures=$gateFail"
if ($fatal -or $gateFail -gt 0) {
  Log "=== STOP: failures=$gateFail fatal=$($fatal.module) note=$($fatal.note) ==="
  $results | ConvertTo-Json -Depth 4 | Set-Content -Encoding utf8 $jsonOut
  exit 1
}
Log "PHASE 2 COMPLETE: all 23 segments module-green"

# ---- PHASE 3: 23 root imports + ONE root build ----
Log "--- PHASE 3: root imports + single root build ---"
$root = "$W\lean\N11Formalization.lean"
$preSha = (Get-FileHash $root -Algorithm SHA256).Hash
Log "root sha before phase 3: $preSha"
python "$E\add_batch_root_imports.py" *>&1 | ForEach-Object { Log "  $_" }
if ($LASTEXITCODE -ne 0) { Log "ABORT: root import insertion failed (exit=$LASTEXITCODE)"; exit 1 }
Log "root sha after edit: $((Get-FileHash $root -Algorithm SHA256).Hash)"

$rlog = Join-Path $logs "batch2-rootbuild-$stamp.log"
try { & $wrapper -File 'N11Formalization.lean' -Log $rlog -Build -MutexWaitSeconds 5400 | Out-Null }
catch { Log "ROOT BUILD WRAPPER THREW: $($_.Exception.Message)" }
$rcode = if (Test-Path "$rlog.result.json") { (Get-Content "$rlog.result.json" -Raw|ConvertFrom-Json).exit } else { -1 }
Log "ROOT BUILD exit=$rcode log=$rlog"
$results += [pscustomobject]@{ phase='rootbuild'; key='root'; exit=$rcode; log=$rlog }
$results | ConvertTo-Json -Depth 4 | Set-Content -Encoding utf8 $jsonOut
Log "=== BATCH v2 COMPLETE (root build exit=$rcode) ==="
if ($rcode -ne 0) { exit 1 }
