"""Authoritative machine-reboot interruption evidence, never a fabricated exit."""
from pathlib import Path
from datetime import datetime
import argparse
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from test_outer_collar import WSL
from closed_origin_slab import rows

assert __debug__

PREVIOUS_NAMES = {
    15: "n25-B15-origin-streamed-search-20261005-v1",
    16: "n25-B16-origin-streamed-search-20261005-v1",
    17: "n25-B17-origin-streamed-search-20261005-v1",
}
RECORD_NAME = "n25-machine-reboot-interruption-20261005-v1"


def current_state():
    ps = subprocess.run([WSL, "--distribution", "Ubuntu2204", "--exec", "/bin/ps", "-eo", "pid,args"],
                        capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    assert ps.returncode == 0 and b"PID COMMAND" in ps.stdout
    linux_text = ps.stdout.decode("utf8", errors="replace")
    boot = subprocess.run(["powershell.exe", "-NoProfile", "-Command",
        "(Get-CimInstance Win32_OperatingSystem).LastBootUpTime.ToUniversalTime().ToString('o')"],
        capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    assert boot.returncode == 0
    boot_utc = boot.stdout.decode("ascii").strip()
    boot_timestamp = datetime.fromisoformat(boot_utc.replace("Z", "+00:00")).timestamp()
    windows = subprocess.run(["powershell.exe", "-NoProfile", "-Command",
        "Get-CimInstance Win32_Process | Where-Object { $_.Name -match 'python|wsl|lean|lake' } | "
        "Select-Object ProcessId,ParentProcessId,Name,CreationDate,CommandLine | ConvertTo-Json -Depth 4"],
        capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    assert windows.returncode == 0
    return linux_text, boot_utc, boot_timestamp, windows.stdout.decode("utf8", errors="replace")


def assert_no_live_boundary(linux_text, B):
    assert not any(re.search(r"\./peel_\S*collar-linux\s+25\s+"+str(B)+r"(?:\s|$)", line)
                   for line in linux_text.splitlines()), "a full N25/B job is still alive"


def recovery_gate(origin_controls_path, previous, B):
    assert B in PREVIOUS_NAMES and previous.resolve() == ROOT / PREVIOUS_NAMES[B]
    record_path = ROOT / RECORD_NAME / "VERIFIED.json"
    report = read(record_path)
    assert report["verified"] and report["schema"] == "machine-reboot-interrupted-N25-searches-v1"
    assert report["source_sha256"] == sha(Path(__file__))
    assert report["actual_old_native_exit_code_unknown"]
    assert report["old_prefixes_not_complete_or_resumable_catalogues"]
    unchanged(report["files_relative_to_workspace"])
    linux_text, boot_utc, boot_timestamp, windows_text = current_state()
    assert boot_utc == report["windows_last_boot_utc"]
    assert_no_live_boundary(linux_text, B)
    entry = next(row for row in report["searches"] if row["B"] == B)
    assert entry["previous_search"] == previous.name
    assert entry["input_bindings_sha256"] == sha(previous / "INPUT-BINDINGS.json")
    assert entry["no_actual_terminal_was_observed"]
    assert not (previous / "NATIVE-TERMINAL.json").exists()
    assert not (previous / "SUMMARY.json").exists()
    assert not (previous / f"N25-B{B}-complete-origin-sorted-chunks.json").exists()
    assert (previous / "INPUT-BINDINGS.json").stat().st_mtime < boot_timestamp
    from b15_origin_replacement_gate import b15_origin_controls_gate
    files = b15_origin_controls_gate(origin_controls_path)
    files.update(report["files_relative_to_workspace"])
    inputs = read(previous / "INPUT-BINDINGS.json")
    assert (inputs["N"], inputs["B"]) == (25, B)
    unchanged(inputs["files_relative_to_workspace"])
    files.update(inputs["files_relative_to_workspace"])
    bind(files, record_path);bind(files, Path(__file__))
    return files


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--record", type=Path, required=True)
    args = ap.parse_args()
    record = args.record.resolve()
    assert record == ROOT / RECORD_NAME and not record.exists()
    linux_text, boot_utc, boot_timestamp, windows_text = current_state()
    files, searches = {}, []
    for B, name in PREVIOUS_NAMES.items():
        assert_no_live_boundary(linux_text, B)
        previous = ROOT / name
        input_path, identity_path, launch_path, log_path = (
            previous / filename for filename in (
                "INPUT-BINDINGS.json", "LINUX-NATIVE-IDENTITY.json", "WSL-LAUNCH.json", "NATIVE-STDERR.log"))
        inputs, identity, launch = map(read, (input_path, identity_path, launch_path))
        assert (inputs["N"], inputs["B"]) == (25, B)
        assert launch["command"] == inputs["command"]
        assert launch["owned_wsl_proxy_pid"] == identity["owned_wsl_proxy_pid"]
        assert input_path.stat().st_mtime < boot_timestamp and identity_path.stat().st_mtime < boot_timestamp
        unchanged(inputs["files_relative_to_workspace"])
        files.update(inputs["files_relative_to_workspace"])
        assert not (previous / "NATIVE-TERMINAL.json").exists() and not (previous / "SUMMARY.json").exists()
        manifest = previous / f"N25-B{B}-complete-origin-sorted-chunks.json"
        assert not manifest.exists()
        slabs = sorted(previous.glob(manifest.name+".chunk-*.jsonl"),
                       key=lambda p: int(p.name.rsplit("-", 1)[1].split(".")[0]))
        slab_records = []
        for index, slab_path in enumerate(slabs):
            assert slab_path.name == manifest.name+f".chunk-{index}.jsonl"
            before = sha(slab_path)
            count = sum(1 for _ in rows(slab_path, B, index))
            assert count == 100000 and sha(slab_path) == before
            slab_records.append({"index": index, "rows": count, "sha256": before, "file": slab_path.name})
            bind(files, slab_path)
        searches.append({
            "B": B, "previous_search": name, "previous_linux_pid": identity["linux_native_pid"],
            "previous_owned_wsl_proxy_pid": launch["owned_wsl_proxy_pid"],
            "input_bindings_sha256": sha(input_path),
            "closed_finite_slabs_fully_scanned": slab_records,
            "no_current_native_process_for_this_boundary": True,
            "no_actual_terminal_was_observed": True, "actual_native_exit_code": None,
            "complete_manifest_missing": True, "all_old_files_preserved": True,
        })
        for path in (input_path, identity_path, launch_path, log_path):
            bind(files, path)
        print("Reboot-interrupted job evidence checked: B", B, len(slabs),
              "closed slabs preserved; no terminal code fabricated", flush=True)
    record.mkdir()
    publish(record / "PROCESS-SNAPSHOT.json", {
        "windows_last_boot_utc": boot_utc, "linux_process_snapshot": linux_text,
        "windows_process_snapshot": windows_text,
    })
    bind(files, Path(__file__));bind(files, ROOT / "closed_origin_slab.py")
    bind(files, record / "PROCESS-SNAPSHOT.json")
    unchanged(files)
    publish(record / "VERIFIED.json", {
        "verified": True, "schema": "machine-reboot-interrupted-N25-searches-v1",
        "windows_last_boot_utc": boot_utc, "searches": searches,
        "actual_old_native_exit_code_unknown": True,
        "old_prefixes_not_complete_or_resumable_catalogues": True,
        "no_signal_or_delete_performed": True,
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
