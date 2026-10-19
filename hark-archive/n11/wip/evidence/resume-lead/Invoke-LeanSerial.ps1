param(
  [Parameter(Mandatory=$true)][string]$File,
  [Parameter(Mandatory=$true)][string]$Log,
  [switch]$Build
)
$ErrorActionPreference = 'Stop'
$project = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..\lean'))
$logPath = [IO.Path]::GetFullPath($Log)
[IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($logPath)) | Out-Null
$mutex = [Threading.Mutex]::new($false, 'Local\N11Formalization_LeanSerial_20260929')
$held = $false
try {
  try { $held = $mutex.WaitOne(600000) } catch [Threading.AbandonedMutexException] { $held = $true }
  if (!$held) { throw 'N11 serial lock wait exceeded 10 min; report to lead, do not launch unlocked.' }
  $env:PATH = 'E:\lean-lab\.elan\bin;' + $env:PATH
  $env:ELAN_HOME = 'E:\lean-lab\.elan'
  Push-Location $project
  $start = (Get-Date).ToString('o')
  $hash = if (!$Build) { (Get-FileHash -Algorithm SHA256 -LiteralPath $File).Hash } else { $null }
  if ($Build) { & lake build $File 1> $logPath 2> "$logPath.stderr" }
  else { & lake env lean $File 1> $logPath 2> "$logPath.stderr" }
  $code = $LASTEXITCODE
  $after = if (!$Build) { (Get-FileHash -Algorithm SHA256 -LiteralPath $File).Hash } else { $null }
  [ordered]@{file=$File; build=[bool]$Build; started=$start; finished=(Get-Date).ToString('o'); exit=$code; sha256_before=$hash; sha256_after=$after; unchanged=($hash -eq $after); project=$project; log=$logPath} | ConvertTo-Json | Set-Content -Encoding utf8 "$logPath.result.json"
  Write-Output "exit=$code log=$logPath"
} finally {
  if ($held) { Pop-Location; $mutex.ReleaseMutex() }
  $mutex.Dispose()
}
