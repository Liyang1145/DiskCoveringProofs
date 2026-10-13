"""Read-only actual new-job identity and duplicate-replacement refusal audit."""
from pathlib import Path
import argparse
import re
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from test_outer_collar import linux_path
from b15_degree_controlled_stop import invoke, replacement_readiness
from pending_degree_production_gate import production_gate

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    current = ROOT / "n25-B15-degree-origin-complete-search-20261005-v1"
    previous = ROOT / "n25-B15-origin-streamed-search-reboot-20261005-v1"
    inputs, identity, launch = map(read, (
        current / "INPUT-BINDINGS.json", current / "LINUX-NATIVE-IDENTITY.json", current / "WSL-LAUNCH.json"))
    assert (inputs["N"], inputs["B"]) == (25, 15)
    assert inputs["command"] == launch["command"]
    assert launch["owned_wsl_proxy_pid"] == identity["owned_wsl_proxy_pid"]
    binary = ROOT / "peel_pending_degree_origin_collar-linux"
    assert sha(binary) == identity["native_binary_sha256"]
    files = dict(inputs["files_relative_to_workspace"])
    unchanged(files)
    assert files[binary.relative_to(ROOT.parents[2]).as_posix()] == sha(binary)
    pid = identity["linux_native_pid"]
    assert type(pid) is int and pid > 1
    command = inputs["command"]
    expected = command[command.index("./peel_pending_degree_origin_collar-linux"):]
    assert len(expected) == 16 and expected[:3] == ["./peel_pending_degree_origin_collar-linux", "25", "15"]
    assert expected[3] == current.name+"/N25-B15-complete-origin-sorted-chunks.json"
    assert expected[8:11] == ["0", "dfs", "-"]
    assert expected[11] == "n25-B15-offline-contracted-union27-library-20261005-v1/OBSTACLES.tsv"
    assert expected[-4:] == ["4058615", "100000", "1", "1"]
    actual = invoke(["/bin/cat", f"/proc/{pid}/cmdline"]).stdout.split(b"\0")
    assert actual[-1] == b""
    actual = [value.decode("utf8") for value in actual[:-1]]
    executable = invoke(["/usr/bin/readlink", "-f", f"/proc/{pid}/exe"]).stdout.decode("utf8").strip()
    directory = invoke(["/usr/bin/readlink", "-f", f"/proc/{pid}/cwd"]).stdout.decode("utf8").strip()
    assert actual == expected and executable == linux_path(binary) and directory == linux_path(ROOT)
    stat = invoke(["/bin/cat", f"/proc/{pid}/stat"]).stdout.decode("utf8")
    assert int(stat.split(" ", 1)[0]) == pid
    start_ticks = int(stat.rsplit(")", 1)[1].split()[19])
    snapshot = invoke(["/bin/ps", "-eo", "pid,args"]).stdout.decode("utf8")
    relevant = [line for line in snapshot.splitlines()
                if re.search(r"\./peel_\S*collar-linux\s+25\s+15(?:\s|$)", line)]
    assert len(relevant) == 1 and int(relevant[0].split()[0]) == pid
    assert not (current / "NATIVE-TERMINAL.json").exists() and not (current / "SUMMARY.json").exists()
    old_terminal = read(previous / "NATIVE-TERMINAL.json")
    assert old_terminal["native_terminal_observed"] and old_terminal["actual_exit_code"] == 15
    assert old_terminal["linux_native_pid"] != pid
    files.update(production_gate(
        ROOT / "n25-B15-offline-contracted-union27-library-20261005-v1/LIBRARY.json",
        ROOT / "n25-B15-union27-sparse-map-controls-20261005-v1/VERIFIED.json",
        ROOT / "n25-B15-union27-eight-sparse-guard-controls-20261005-v1/VERIFIED.json", 15))
    try:
        replacement_readiness(previous)
    except AssertionError as error:
        assert "another N25/B15 enumerator is still alive" in str(error)
    else:
        raise AssertionError("a second replacement was admitted while the new B15 job is truly alive")
    for path in (Path(__file__), current / "INPUT-BINDINGS.json", current / "LINUX-NATIVE-IDENTITY.json",
                 current / "WSL-LAUNCH.json", previous / "NATIVE-TERMINAL.json"):
        bind(files, path)
    unchanged(files)
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "actual-B15-degree-live-start-and-duplicate-refusal-v1",
        "N": 25, "B": 15, "linux_native_pid": pid, "linux_starttime_ticks": start_ticks,
        "actual_native_cmdline": actual, "actual_linux_executable": executable,
        "actual_linux_cwd": directory, "owned_wsl_proxy_pid": launch["owned_wsl_proxy_pid"],
        "exactly_one_actual_N25_B15_native_alive": True,
        "old_owned_native_actual_exit_code": old_terminal["actual_exit_code"],
        "true_live_duplicate_replacement_independently_rejected": True,
        "complete_root_unseeded_node_limit_zero_origin_and_degree_flags_one": True,
        "not_a_complete_competitor_family_or_union": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })
    print("Actual B15 degree native identity and real live duplicate refusal PASS:",
          pid, "; one unseeded full-root job; old actual exit 15", flush=True)


if __name__ == "__main__":
    main()
