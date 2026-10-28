param(
  [string]$Root = 'E:\ai4math2\research-2026\n11-formalization'
)
# Anti-stale-olean matched-pair control for the stage-1 energy emission.
#   A  root import REVERTED, root NOT rebuilt  -> probe PASSES (the trap)
#   B  root import REVERTED, root rebuilt      -> probe FAILS (unknownIdentifier)
#   C  root import RESTORED, root rebuilt      -> probe PASSES
$ErrorActionPreference = 'Continue'
$wrapper = Join-Path $Root 'evidence\resume-lead\Invoke-LeanSerial20261013.ps1'
$logdir  = Join-Path $Root 'evidence\energy-emit-20261028\logs\matched-pair'
New-Item -ItemType Directory -Force $logdir | Out-Null
$rootFile = Join-Path $Root 'lean\N11Formalization.lean'
$backup   = Join-Path $Root 'evidence\energy-emit-20261028\N11Formalization-root-stage1.lean.bak'
$marker   = '-- Energy stage 1 (2026-10-28, Asia/Shanghai)'

$rootText = [IO.File]::ReadAllText($rootFile)
if (-not $rootText.Contains($marker)) { throw 'stage-1 block not found in the root; aborting' }
if (-not (Test-Path $backup)) { [IO.File]::WriteAllText($backup, $rootText, (New-Object System.Text.UTF8Encoding($false))) }
$integrated = [IO.File]::ReadAllText($backup)
$idx = $integrated.IndexOf($marker)
$reverted = $integrated.Substring(0, $idx).TrimEnd("`n") + "`n"
if ($reverted.Contains('EnergyTerminalBatchB12Main')) { throw 'revert left the stage-1 import in place' }

$rows = @()
function Hash-Root { (Get-FileHash -LiteralPath $rootFile -Algorithm SHA256).Hash }
function Run-Arm([string]$arm, [bool]$build, [string]$expect) {
  $log = Join-Path $logdir ("probe-arm-" + $arm + ".log")
  if ($build) {
    & $wrapper -File 'N11Formalization' -Log (Join-Path $logdir ("rootbuild-" + $arm + ".log")) -Build -MutexWaitSeconds 5400 | Out-Null
  }
  & $wrapper -File 'ProbeEnergyNext505.lean' -Log $log -MutexWaitSeconds 5400 | Out-Null
  $res = Get-Content -LiteralPath "$log.result.json" -Raw | ConvertFrom-Json
  $txt = Get-Content -LiteralPath $log -Raw
  $unknown = ([regex]::Matches($txt, 'unknownIdentifier')).Count
  $script:rows += [pscustomobject]@{ arm = $arm; rebuilt = $build; expected = $expect
    probeExit = $res.exit; unchanged = $res.unchanged; unknownIdentifier = $unknown
    rootSha = (Hash-Root); log = $log }
  Write-Output ("arm {0}: exit={1} unknownIdentifier={2} ({3})" -f $arm, $res.exit, $unknown, $expect)
}

[IO.File]::WriteAllText($rootFile, $reverted, (New-Object System.Text.UTF8Encoding($false)))
Run-Arm 'A' $false 'probe must STILL pass on the stale root olean'

Run-Arm 'B' $true 'probe must FAIL with unknownIdentifier'

[IO.File]::WriteAllText($rootFile, $integrated, (New-Object System.Text.UTF8Encoding($false)))
Run-Arm 'C' $true 'probe must pass again'

$out = Join-Path $logdir 'matched-pair-summary.json'
[ordered]@{ restoredRootSha = (Hash-Root); backup = $backup; rows = $rows } |
  ConvertTo-Json -Depth 4 | Set-Content -Encoding utf8 $out
Write-Output "summary -> $out"