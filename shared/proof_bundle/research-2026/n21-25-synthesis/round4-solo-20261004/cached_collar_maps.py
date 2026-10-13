"""Reuse checked map batches; on an unavailable backend, keep rows unclassified."""
from pathlib import Path
import os
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
from n25_outer_search import read, publish, bind
from stream_catalog import sha
from verify_sparse_maps_fast import batch_match
from test_outer_collar import WSL

assert __debug__


def cached_batch_match(table, requests, output, N, B, cached_root, files):
    cached = cached_root.resolve() / output.name
    terminalpath, requestpath, answerpath = (cached / name for name in
                                            ("NATIVE-TERMINAL.json", "REQUESTS.tsv", "NATIVE-MAPS.json"))
    if terminalpath.exists() and read(terminalpath)["actual_exit_code"] == 0:
        terminal = read(terminalpath)
        response = read(answerpath)
        assert response["scope"] == "sparse subgraph maps only"
        expected = "\n".join("\t".join(map(str, [index, len(faces), *faces]))
                             for index, faces in enumerate(requests))+"\n"
        assert requestpath.read_text(encoding="ascii") == expected, "cached request/parent graph mismatch"
        assert [r["request"] for r in response["matches"]] == list(range(len(requests)))
        for source, name in ((requestpath, "REQUESTS.tsv"), (answerpath, "NATIVE-MAPS.json")):
            assert not (output / name).exists()
            shutil.copyfile(source, output / name)
            bind(files, source)
        publish(output / "NATIVE-TERMINAL.json", {
            **terminal, "reused_from_cached_batch": cached.relative_to(ROOT).as_posix(),
            "not_a_fresh_native_run": True,
        })
        bind(files, terminalpath)
        publish(output / "CACHE.json", {
            "requests_explicitly_equal_to_current_parent_rows": True,
            "original_actual_native_exit_code": 0,
            "original_terminal_sha256": sha(terminalpath),
            "original_request_sha256": sha(requestpath), "original_map_sha256": sha(answerpath),
            "not_a_resumed_enumeration": True,
        })
        return response["matches"]
    # Check a real successful process snapshot, not an empty pgrep exit, before
    # repeating a failed small matching batch. No enumerator is restarted.
    relative = os.path.relpath(requestpath, ROOT).replace("\\", "/")
    snapshot = subprocess.run([WSL, "--distribution", "Ubuntu2204", "--exec",
                               "/bin/ps", "-eo", "pid,args"], capture_output=True,
                              creationflags=subprocess.CREATE_NO_WINDOW)
    text = snapshot.stdout.decode("utf8", errors="replace")
    snapshot_ok = snapshot.returncode == 0 and "PID COMMAND" in text
    residual_native = snapshot_ok and any(
        "sparse_outer_match-linux" in line and relative in line for line in text.splitlines())
    publish(output / "PRIOR-NATIVE-ABSENCE-CHECK.json", {
        "actual_process_snapshot_exit_code": snapshot.returncode,
        "successful_nonempty_process_snapshot": snapshot_ok,
        "prior_owned_native_absent": snapshot_ok and not residual_native,
        "prior_request_relative_path": relative,
        "unavailable_map_backend_never_used_for_exclusion": True,
    })
    if snapshot_ok and not residual_native:
        try:
            return batch_match(table, requests, output, N, B)
        except AssertionError:
            # A map backend failure does not block a sound overapproximation:
            # no positive maps from that batch are accepted, and every graph
            # is still processed by the independent angle/family checks.
            pass
    answers = [{"request": index, "obstacle": -1} for index in range(len(requests))]
    fallback = {"scope": "sparse subgraph maps only", "matches": answers,
                "conservative_unknown_map_fallback": True}
    if not (output / "NATIVE-MAPS.json").exists():
        publish(output / "NATIVE-MAPS.json", fallback)
    else:
        publish(output / "CONSERVATIVE-NO-MATCHES.json", fallback)
    publish(output / "MAP-BACKEND-UNAVAILABLE.json", {
        "no_sparse_match_or_exclusion_claimed_for_any_request": True,
        "request_count": len(requests), "independent_angle_and_family_checks_still_required": True,
    })
    return answers
