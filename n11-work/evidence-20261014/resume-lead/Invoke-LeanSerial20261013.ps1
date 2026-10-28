param(
  [Parameter(Mandatory=$true)][string]$File,
  [Parameter(Mandatory=$true)][string]$Log,
  [switch]$Build,
  [int]$MutexWaitSeconds = 5400
)
# Lead-owned variant of evidence\resume-lead\Invoke-LeanSerial.ps1.
# Identical evidence format and identical mutex name; the ONLY change is that
# the mutex wait is configurable and defaults to 90 minutes instead of 10,
# because a single peer module build can legitimately exceed 10 minutes
# (observed: SharedMomentConcreteSwitchBatch module build = 1042 s), which made
# queued members hit "N11 serial lock wait exceeded 10 min" on a healthy system.
# Never launch unlocked: if the wait expires this throws and starts nothing.
$ErrorActionPreference = 'Stop'
$project = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..\lean'))
$logPath = [IO.Path]::GetFullPath($Log)
[IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($logPath)) | Out-Null
if (Test-Path -LiteralPath $logPath) { throw "Refusing to overwrite existing evidence: $logPath" }
$mutex = [Threading.Mutex]::new($false, 'Local\N11Formalization_LeanSerial_20260929')
$held = $false
try {
  try { $held = $mutex.WaitOne($MutexWaitSeconds * 1000) } catch [Threading.AbandonedMutexException] { $held = $true }
  if (!$held) { throw "N11 serial lock wait exceeded $MutexWaitSeconds s; report to lead, do not launch unlocked." }
  $env:PATH = 'E:\lean-lab\.elan\bin;' + $env:PATH
  $env:ELAN_HOME = 'E:\lean-lab\.elan'
  Push-Location $project
  $start = (Get-Date).ToString('o')
  $hash = if (!$Build) { (Get-FileHash -Algorithm SHA256 -LiteralPath $File).Hash } else { $null }
  if ($Build) { & lake build $File 1> $logPath 2> "$logPath.stderr" }
  else { & lake env lean $File 1> $logPath 2> "$logPath.stderr" }
  $code = $LASTEXITCODE
  $after = if (!$Build) { (Get-FileHash -Algorithm SHA256 -LiteralPath $File).Hash } else { $null }
  [ordered]@{file=$File; build=[bool]$Build; started=$start; finished=(Get-Date).ToString('o'); exit=$code; sha256_before=$hash; sha256_after=$after; unchanged=($hash -eq $after); project=$project; log=$logPath; mutex_wait_seconds=$MutexWaitSeconds} | ConvertTo-Json | Set-Content -Encoding utf8 "$logPath.result.json"
  Write-Output "exit=$code log=$logPath"
} finally {
  if ($held) { Pop-Location; $mutex.ReleaseMutex() }
  $mutex.Dispose()
}
