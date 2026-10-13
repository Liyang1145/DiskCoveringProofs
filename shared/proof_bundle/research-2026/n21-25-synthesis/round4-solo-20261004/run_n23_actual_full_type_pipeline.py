"""Wait for the real existing extractor, then propose and independently audit.

The Windows process handle observes an actual terminal code. Missing files,
silence and disappearing/reused PIDs are never converted into a success code.
"""
from pathlib import Path
import argparse
import ctypes
from ctypes import wintypes
import json
import os
import subprocess
import sys

from n25_outer_search import read, publish
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def observed_extractor(pid, restored, output):
    assert os.name == "nt" and type(pid) is int and pid > 0
    kernel = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel.OpenProcess.argtypes = (wintypes.DWORD, wintypes.BOOL, wintypes.DWORD)
    kernel.OpenProcess.restype = wintypes.HANDLE
    kernel.CloseHandle.argtypes = (wintypes.HANDLE,)
    kernel.GetProcessTimes.argtypes = (wintypes.HANDLE,)+(
        ctypes.POINTER(wintypes.FILETIME),)*4
    kernel.WaitForSingleObject.argtypes = (wintypes.HANDLE, wintypes.DWORD)
    kernel.WaitForSingleObject.restype = wintypes.DWORD
    kernel.GetExitCodeProcess.argtypes = (wintypes.HANDLE, ctypes.POINTER(wintypes.DWORD))
    kernel.QueryFullProcessImageNameW.argtypes = (
        wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD))
    handle = kernel.OpenProcess(0x00100000 | 0x1000, False, pid)
    if not handle:
        raise OSError(ctypes.get_last_error(), "cannot bind original live extractor process")
    try:
        times = [wintypes.FILETIME() for _ in range(4)]
        assert kernel.GetProcessTimes(handle, *(ctypes.byref(value) for value in times))
        creation = (times[0].dwHighDateTime << 32)+times[0].dwLowDateTime
        buffer, size = ctypes.create_unicode_buffer(32768), wintypes.DWORD(32768)
        assert kernel.QueryFullProcessImageNameW(handle, 0, buffer, ctypes.byref(size))
        assert Path(buffer.value).resolve() == Path(sys.executable).resolve()
        command = (
            "[Console]::OutputEncoding = [System.Text.Encoding]::UTF8; "
            f"Get-CimInstance Win32_Process -Filter 'ProcessId = {pid}' | "
            "Select-Object ProcessId,Name,CommandLine,"
            "@{Name='CreationFileTime';Expression={$_.CreationDate.ToUniversalTime().ToFileTimeUtc().ToString()}} "
            "| ConvertTo-Json -Compress"
        )
        metadata = subprocess.run(
            ["powershell.exe", "-NoProfile", "-NonInteractive", "-Command", command],
            check=True, capture_output=True, encoding="utf8",
            creationflags=subprocess.CREATE_NO_WINDOW)
        actual = json.loads(metadata.stdout)
        assert actual["ProcessId"] == pid and actual["Name"] == "python.exe"
        assert int(actual["CreationFileTime"])//10 == creation//10
        assert "extract_n23_actual_residual_types.py" in actual["CommandLine"]
        assert "--output "+restored.name in actual["CommandLine"]
        assert "--parent n23-B15-residual-new7-force5001-full-source-audit-solo-v1" in actual["CommandLine"]
        publish(output / "EXTRACTOR-PROCESS-BINDING.json", {
            "original_pid": pid, "creation_filetime_identity_only": str(creation),
            "process_image": buffer.value, "command_line": actual["CommandLine"],
            "extractor_source_sha256": sha(ROOT / "extract_n23_actual_residual_types.py"),
            "not_a_terminal_or_mathematical_success_yet": True,
        })
        print("N23 full-type pipeline bound the real existing extractor", pid,
              "; waiting for actual terminal, not restarting it", flush=True)
        while True:
            result = kernel.WaitForSingleObject(handle, 1000)
            assert result in (0, 258)
            if result == 0:
                break
        code = wintypes.DWORD()
        assert kernel.GetExitCodeProcess(handle, ctypes.byref(code))
        publish(output / "EXTRACTOR-TERMINAL.json", {
            "original_pid": pid, "actual_exit_code": code.value,
            "same_original_process_handle_terminal_observed": True,
            "process_binding_sha256": sha(output / "EXTRACTOR-PROCESS-BINDING.json"),
            "source_sha256": sha(Path(__file__)),
        })
        assert code.value == 0
    finally:
        kernel.CloseHandle(handle)


def child(command, output, name):
    with (output / (name+"-STDOUT.log")).open("xb") as stdout, \
            (output / (name+"-STDERR.log")).open("xb") as stderr:
        process = subprocess.Popen(
            list(map(str, command)), cwd=str(ROOT), stdout=stdout, stderr=stderr,
            env=dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / (name+"-TERMINAL.json"), {
        "actual_child_pid": process.pid, "actual_exit_code": code,
        "independent_process_terminal_observed": True,
        "command": list(map(str, command)), "source_sha256": sha(Path(__file__)),
    })
    assert code == 0, (name, code)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--wait-extractor-pid", type=int, required=True)
    for name in ("restored", "core", "core-proof", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--limit", type=int, default=31)
    args = ap.parse_args()
    restored, corepath, coreproof, controls, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("restored", "core", "core-proof", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (restored, corepath, coreproof, controls, output))
    assert not output.exists() and 1 <= args.limit <= 5001
    frozen = {str(path): sha(path) for path in (
        Path(__file__), corepath, coreproof, controls,
        ROOT / "extract_n23_actual_residual_types.py",
        ROOT / "propose_n23_actual_full_types.py",
        ROOT / "audit_n23_actual_full_type_stage.py",
        ROOT / "test_n23_actual_full_type_stage.py")}
    output.mkdir()
    publish(output / "PIPELINE-INPUT-BINDINGS.json", {
        "frozen_files": frozen, "only_existing_extractor_observed_not_restarted": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    observed_extractor(args.wait_extractor_pid, restored, output)
    accepted = read(restored / "VERIFIED.json")
    assert accepted["verified"] and accepted["actual_full_residual_types"] == 829
    assert accepted["selected_original_outer_group_members"] == {
        "369033": 330, "436330": 330, "522460": 169}
    for path, digest in frozen.items():
        assert sha(path) == digest
    proposals = output / "PROPOSALS"
    audit = output / "ACTUAL-TYPE-PAYMENT-AUDIT"
    child([
        sys.executable, "-u", ROOT / "propose_n23_actual_full_types.py",
        "--restored", restored, "--core", corepath,
        "--limit", args.limit, "--output", proposals], output, "PROPOSAL")
    print("N23 actual full-type proposals ended; independent exact payment starts", flush=True)
    child([
        sys.executable, "-u", ROOT / "audit_n23_actual_full_type_stage.py",
        "--restored", restored, "--stage", proposals, "--core", corepath,
        "--core-proof", coreproof, "--controls", controls, "--output", audit], output, "AUDIT")
    for path, digest in frozen.items():
        assert sha(path) == digest
    result = read(audit / "VERIFIED.json")
    assert result["verified"]
    publish(output / "PIPELINE-COMPLETED.json", {
        "actual_proposal_and_independent_audit_terminals_observed": True,
        "payment_report_sha256": sha(audit / "VERIFIED.json"),
        "counts": result["counts"], "pending_full_types": result["pending_full_types"],
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    print("N23 actual full-type pipeline complete:", result["counts"], flush=True)


if __name__ == "__main__":
    main()
