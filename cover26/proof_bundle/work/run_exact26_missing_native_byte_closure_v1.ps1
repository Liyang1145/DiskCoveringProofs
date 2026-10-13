param(
    [string]$PythonExecutable = 'C:/热爱单机但萌新/dependencies/python/python.exe'
)
$ErrorActionPreference = 'Stop'
$taskOwn = 'outputs/n26-prior-native-receipt-byte-closure-v1'
$taskFinal = 'outputs/n26-prior-native-receipt-byte-closure-independent-final-v1.json'
if ((Test-Path -LiteralPath $taskOwn) -or (Test-Path -LiteralPath $taskFinal)) {
    throw 'Preserve existing own/final native closure evidence; do not repeat a completed own.'
}
$taskNativeImportWorkers = Get-CimInstance Win32_Process | Where-Object {
    $_.Name -eq 'python.exe' -and $_.CommandLine -match '(import_exact26_missing_native_receipts|recheck_exact26_missing_native_import)\.py'
}
if ($taskNativeImportWorkers) { throw 'An actual native byte-closure worker is live; do not overlap.' }
& $PythonExecutable work/import_exact26_missing_native_receipts.py --output $taskOwn
if ($LASTEXITCODE -ne 0) { throw 'Native original-byte/partition own failed; final not started.' }
& $PythonExecutable work/recheck_exact26_missing_native_import.py --input $taskOwn --report $taskFinal
if ($LASTEXITCODE -ne 0) {
    throw 'Native independent final failed. Preserve completed OWN; retry only final after diagnosis.'
}
Write-Output 'Actual missing-native byte closure OWN and independent final completed; actual latest-current join is still required.'
