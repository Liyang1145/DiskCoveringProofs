param(
  [Parameter(Mandatory=$true)][string]$List,      # one module name per line
  [Parameter(Mandatory=$true)][string]$Tag,
  [int]$Jobs = 2,
  [string]$Root = 'E:\ai4math2\research-2026\n11-formalization'
)
# One-shot serialized `lake build -j N` over an emitted module list.
# Rationale: the per-module wrapper pays a ~2 min full-closure replay on every
# call; a single lake invocation pays it once and still compiles serially enough
# to stay inside the 15.2 GB envelope (DEAD.md records OOM/olean-read failures
# under 16-way parallelism).
$ErrorActionPreference = 'Stop'
$outdir = Join-Path $Root ("evidence\energy-emit-20261028\logs\" + $Tag)
New-Item -ItemType Directory -Force $outdir | Out-Null
$log = Join-Path $outdir 'lake-build.log'
if (Test-Path -LiteralPath $log) { throw "Refusing to overwrite existing evidence: $log" }
$progress = Join-Path $outdir 'progress.txt'
$mods = Get-Content $List | Where-Object { $_.Trim() -ne '' } | ForEach-Object { $_.Trim() }

$mutex = [Threading.Mutex]::new($false, 'Local\N11Formalization_LeanSerial_20260929')
$held = $false
try {
  try { $held = $mutex.WaitOne(5400 * 1000) } catch [Threading.AbandonedMutexException] { $held = $true }
  if (!$held) { throw 'N11 serial lock wait exceeded 5400 s; do not launch unlocked.' }
  $env:PATH = 'E:\lean-lab\.elan\bin;' + $env:PATH
  $env:ELAN_HOME = 'E:\lean-lab\.elan'
  Push-Location (Join-Path $Root 'lean')
  $start = (Get-Date).ToString('o')
  "start lake build -j $Jobs ($($mods.Count) targets) $start" | Add-Content $progress
  $args = @('build', "-j$Jobs") + $mods
  & lake @args 1> $log 2> "$log.stderr"
  $code = $LASTEXITCODE
  $finish = (Get-Date).ToString('o')
  [ordered]@{ targets = $mods; jobs = $Jobs; started = $start; finished = $finish
              exit = $code; log = $log } | ConvertTo-Json -Depth 4 |
    Set-Content -Encoding utf8 "$log.result.json"
  "end exit=$code $finish" | Add-Content $progress
  "exit=$code" | Write-Output
} finally {
  if ($held) { Pop-Location; $mutex.ReleaseMutex() }
  $mutex.Dispose()
}
