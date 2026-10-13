param(
    [Parameter(Mandatory=$true)][string]$ReportPath
)
$ErrorActionPreference = 'Stop'
$taskRoot = $PSScriptRoot
$reportTarget = [System.IO.Path]::GetFullPath((Join-Path $taskRoot $ReportPath))
$evidenceRoot = [System.IO.Path]::GetFullPath((Join-Path $taskRoot 'evidence')) + [System.IO.Path]::DirectorySeparatorChar
if (-not $reportTarget.StartsWith($evidenceRoot, [System.StringComparison]::OrdinalIgnoreCase)) {
    throw 'Resume report must stay in this task evidence directory.'
}
if (Test-Path -LiteralPath $reportTarget) { throw 'Refuse to overwrite an existing resume report.' }
$auditPath = Join-Path $taskRoot 'evidence/n22-global-snapshot-integrity-streamed-resume1.json'
$audit = Get-Content -LiteralPath $auditPath -Raw | ConvertFrom-Json
if (-not $audit.verified -or -not $audit.all_bound_files_checked -or
    $audit.file_count -ne 904281 -or $audit.mismatches.Count -ne 0) {
    throw 'Critical n22 full-byte audit has not passed.'
}
$snapshotPath = Join-Path $taskRoot 'evidence/N22-GLOBAL-SNAPSHOT-resume1.json'
$snapshotHash = (Get-FileHash -LiteralPath $snapshotPath -Algorithm SHA256).Hash.ToLowerInvariant()
if ($snapshotHash -ne $audit.manifest_sha256) { throw 'Audit does not bind the current final snapshot.' }
$record = Get-Content -LiteralPath (Join-Path $taskRoot 'evidence/n23-B15-native-suspension-resume1.json') -Raw | ConvertFrom-Json
if ($record.ProcessId -ne 37424 -or $record.ThreadId -ne 40232 -or
    $record.PreviousSuspendCount -ne 0 -or -not $record.ResumeRequired) {
    throw 'Unexpected suspension provenance; no thread changed.'
}
$native = Get-CimInstance Win32_Process -Filter 'ProcessId=37424'
$parent = Get-CimInstance Win32_Process -Filter 'ProcessId=27252'
if ($null -eq $native -or $null -eq $parent -or $native.ParentProcessId -ne 27252 -or
    $native.Name -ne 'peel_degree.exe' -or
    -not $native.CommandLine.Contains('23 15 evidence\n23-B15-degree-streamed-resume1\N23-B15-dfs.json') -or
    -not $parent.CommandLine.Contains('--n 23 --B 15 --degree-root --output evidence/n23-B15-degree-streamed-resume1')) {
    throw 'Retained process identity or command changed; no thread changed.'
}
$process = Get-Process -Id 37424
$creation = $process.StartTime.ToUniversalTime().ToString('o')
$recordCreation = ([DateTime]$record.CreationTime).ToUniversalTime().ToString('o')
if ($creation -ne $recordCreation -or $process.Threads.Count -ne 1 -or
    $process.Threads[0].Id -ne 40232 -or
    $process.Threads[0].ThreadState -ne [System.Diagnostics.ThreadState]::Wait -or
    $process.Threads[0].WaitReason -ne [System.Diagnostics.ThreadWaitReason]::Suspended) {
    throw 'Creation time, single-thread identity, or suspension state changed; no thread changed.'
}
Add-Type -TypeDefinition @'
using System;
using System.Runtime.InteropServices;
public static class N23RetainedNativeResume {
    [DllImport("kernel32.dll", SetLastError=true)]
    public static extern IntPtr OpenThread(uint access, bool inherit, uint threadId);
    [DllImport("kernel32.dll", SetLastError=true)]
    public static extern uint GetProcessIdOfThread(IntPtr thread);
    [DllImport("kernel32.dll", SetLastError=true)]
    public static extern uint ResumeThread(IntPtr thread);
    [DllImport("kernel32.dll", SetLastError=true)]
    public static extern bool CloseHandle(IntPtr handle);
}
'@
$threadHandle = [N23RetainedNativeResume]::OpenThread(0x42, $false, 40232)
if ($threadHandle -eq [IntPtr]::Zero) { throw 'Could not open this retained thread.' }
try {
    if ([N23RetainedNativeResume]::GetProcessIdOfThread($threadHandle) -ne 37424) {
        throw 'Thread owner differs; no thread changed.'
    }
    $cpuBefore = $process.CPU
    # Exactly one call restores our single prior SuspendThread increment.
    $previousCount = [N23RetainedNativeResume]::ResumeThread($threadHandle)
    if ($previousCount -eq [uint32]::MaxValue) { throw 'ResumeThread failed.' }
} finally {
    [void][N23RetainedNativeResume]::CloseHandle($threadHandle)
}
$result = [ordered]@{
    ProcessId = 37424
    ParentProcessId = 27252
    ThreadId = 40232
    CreationTime = $creation
    PreviousSuspendCountBeforeResume = $previousCount
    ResumeThreadCalls = 1
    State = $(if ($previousCount -eq 1) { 'retained-native-enumerator-resumed' } else { 'unexpected-additional-suspension-requires-investigation' })
    ResumeRequired = ($previousCount -gt 1)
    CPUSecondsBeforeResume = $cpuBefore
    CommandLine = $native.CommandLine
    n22_integrity_report_sha256 = (Get-FileHash -LiteralPath $auditPath -Algorithm SHA256).Hash.ToLowerInvariant()
    n22_snapshot_sha256 = $snapshotHash
    helper_sha256 = (Get-FileHash -LiteralPath $PSCommandPath -Algorithm SHA256).Hash.ToLowerInvariant()
    goal_paused = $false
    catalogue_complete = $false
}
$result | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath $reportTarget -Encoding utf8
$result | ConvertTo-Json -Depth 5
if ($previousCount -ne 1) { throw 'Only our one increment was removed; inspect additional suspension, never repeat automatically.' }
