# n11-formalization 本地验证器（隔离工程；不触碰全局 elan 默认，不改别的 Lake 工程）
# 用法：
#   .\verify.ps1                       # 编译整个 lean 工程
#   .\verify.ps1 N11Formalization.Foo  # 只编译某个模块
#   .\verify.ps1 -File path\to\x.lean  # 用 lake env lean 单文件检查（不写 olean 到库目录）
# 退出码：0 通过 / 1 编译错误 / 2 用法或环境错误
param(
  [Parameter(Position=0)][string]$Target,
  [string]$File,
  [switch]$Json
)
$ErrorActionPreference = "Stop"
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8

$env:ELAN_HOME = "E:\lean-lab\.elan"
if ($env:PATH -notlike "*E:\lean-lab\.elan\bin*") { $env:PATH = "E:\lean-lab\.elan\bin;" + $env:PATH }

$proj = Join-Path $PSScriptRoot "lean"
if (-not (Test-Path (Join-Path $proj "lakefile.toml"))) { Write-Error "找不到 lean 工程: $proj"; exit 2 }

Push-Location $proj
try {
  if ($File) {
    $f = (Resolve-Path $File).Path
    $out = & lake env lean $f 2>&1
    $code = $LASTEXITCODE
  } elseif ($Target) {
    $out = & lake build $Target 2>&1
    $code = $LASTEXITCODE
  } else {
    $out = & lake build 2>&1
    $code = $LASTEXITCODE
  }
} finally { Pop-Location }

$out | ForEach-Object { $_ }
if ($Json) {
  [pscustomobject]@{ exit = $code; target = $Target; file = $File; lines = @($out).Count } | ConvertTo-Json -Compress
}
exit $code
