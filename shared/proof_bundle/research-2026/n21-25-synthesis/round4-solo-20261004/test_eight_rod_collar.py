"""Compare the new native angle gate with explicit integer certificates.

Retain the exact attaining graph, regress unchanged no-screen enumeration, and
transport every complete small reference graph or pay its negative cycle.
"""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import os
import random
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import canonical
from paid_binary_residual import BinaryRows, verify_merge
from test_outer_collar import linux_path, WSL, collar_codes
from test_sparse_collar import mechanical_derivation
from eight_rod_angles import read, constants_gate, exclusion, verify_cycle, CAP8

assert __debug__
EMPTY_LAUNCH_RETRIES = []


def derivation_gate():
    mechanical_derivation()
    report = read(ROOT / "eight-rod-collar-source-derivation.json")
    assert report["verified_mechanical_derivation"]
    assert report["original_source_sha256"] == sha(ROOT / "peel_sparse_outer_collar.cpp")
    assert report["derived_source_sha256"] == sha(ROOT / "peel_eight_rod_collar.cpp")
    assert report["extra_angle_gate_sha256"] == sha(ROOT / "eight_rod_possible.inc")
    assert report["source_sha256"] == sha(ROOT / "derive_eight_rod_collar.py")
    text = (ROOT / "peel_sparse_outer_collar.cpp").read_text(encoding="utf8")
    for before, after in report["changes"]:
        assert text.count(before) == 1
        text = text.replace(before, after, 1)
    assert text == (ROOT / "peel_eight_rod_collar.cpp").read_text(encoding="utf8")
    probe = read(ROOT / "eight-possible-test-source-derivation.json")
    assert probe["only_entrypoint_name_changed"]
    assert probe["native_source_sha256"] == sha(ROOT / "peel_eight_rod_collar.cpp")
    assert probe["probe_body_sha256"] == sha(ROOT / "eight_collar_probe_body.inc")
    assert probe["source_sha256"] == sha(ROOT / "derive_eight_possible_test.py")
    native = (ROOT / "peel_eight_rod_collar.cpp").read_text(encoding="utf8")
    expected = native.replace("int main(int argc,char**argv){try{",
                              "int frozen_eight_collar_main(int argc,char**argv){try{", 1)
    assert expected == (ROOT / "eight_collar_probe_body.inc").read_text(encoding="utf8")


def run_eight(n, B, output, mode="dfs", library="-", limit=0, cap8=CAP8):
    constants = read(ROOT.parent / "evidence/core-reduction/constants/n25.json")
    relative = lambda path: os.path.relpath(Path(path).resolve(), ROOT).replace("\\", "/")
    output = relative(output)
    table = "-" if library == "-" else relative(library)
    assert output.isascii() and table.isascii()
    command = [
        WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
        "./peel_eight_rod_collar-linux", str(n), str(B), output,
        str(constants["angle_scale"]), *map(str, constants["angle_caps"]),
        str(limit), mode, "-", table, str(cap8),
    ]
    for attempt in range(3):
        result = subprocess.run(command, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        if (result.returncode == 0 or result.stdout or result.stderr
                or (ROOT / output).exists() or attempt == 2):
            return result
        # A terminal WSL proxy with no native diagnostic is not sufficient to
        # rule out a surviving child. Inspect real Linux state before retrying
        # this complete small control (never a production search).
        status = subprocess.run(
            [WSL, "--distribution", "Ubuntu2204", "--exec", "/bin/ps", "-eo", "pid,args"],
            capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        assert status.returncode == 0 and status.stdout, "cannot establish real native absence"
        pattern = re.compile(r"\s"+re.escape(output)+r"(?:\s|$)")
        live = [line for line in status.stdout.decode("utf8", errors="replace").splitlines()
                if "peel_eight_rod_collar-linux" in line and pattern.search(line)]
        assert not live, "prior small-control native survived; refusing duplicate launch"
        EMPTY_LAUNCH_RETRIES.append({"output": output, "attempt": attempt+1,
                                     "proxy_exit_code": result.returncode,
                                     "no_matching_native_process_observed": True})
    raise AssertionError("unreachable")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    derivation_gate()
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    constants_gate(constants)
    capreport = read(ROOT / "n25-eight-rod-exact-cap-20261005-v1.json")
    assert capreport["verified"] and capreport["source_sha256"] == sha(ROOT / "eight_rod_angles.py")
    assert capreport["constants_sha256"] == sha(constants_path) and capreport["cap8"] == CAP8
    output = args.output.resolve()
    assert output.is_relative_to(ROOT)
    output.mkdir()
    requests, source_files = [], []
    geompath = ROOT.parent / "evidence/n25-algebraic-upper-round2/geometry.json"
    geometry = read(geompath)
    full = sorted(sum(1 << v for v in face) for face in geometry["faces"])
    requests.append({"N": 25, "B": 16, "faces": full, "must_survive": True, "kind": "exact-attaining-full-graph"})
    # Full dihedral/inner relabel controls on the same known attaining graph.
    rng = random.Random(251784)
    for sign, shift in ((1, 5), (-1, 7), (-1, 15)):
        inner = list(range(16, 25))
        rng.shuffle(inner)
        mapping = [(shift+sign*v) % 16 for v in range(16)]+inner
        faces = sorted(sum(1 << mapping[v] for v in range(25) if mask >> v & 1) for mask in full)
        requests.append({"N": 25, "B": 16, "faces": faces, "must_survive": True,
                         "kind": "transformed-exact-attaining-graph"})
    reference = ROOT / "n25-B14-outer-library-controls-v3-static/N20-B14-no-payment-reference.bin"
    reference_header, _ = verify_merge(reference)
    reference_rows = list(BinaryRows(reference).rows())
    source_files.extend([geompath, reference])
    for index, row in reference_rows:
        requests.append({"N": 20, "B": 14, "faces": row["faces"], "must_survive": False,
                         "kind": "complete-screened-small-reference", "reference_index": index})
    for B, budget in ((14, 3000000), (15, 25000000), (16, 2000000), (17, 2000000)):
        prefix = (f"n25-B{B}-collar-discovery-20261005-v1/"
                  f"budget-{budget}.json.discovery.json")
        path = ROOT / prefix
        data = read(path)
        source_files.append(path)
        assert data["complete_necessary_outer_search"] is False
        for row in data["weak_graphs"][:64]:
            requests.append({"N": row["centers"], "B": B, "faces": row["faces"],
                             "must_survive": False, "kind": "discovery-graph-not-a-full-family"})
    for B in (14, 15, 16, 17):
        for _ in range(20):
            faces = sorted({sum(1 << v for v in rng.sample(range(25), 3)) for j in range(8)})
            requests.append({"N": 25, "B": B, "faces": faces, "must_survive": False,
                             "kind": "arbitrary-partial-rod-graph"})
    requestpath, answerpath = output / "REQUESTS.tsv", output / "NATIVE-ANSWERS.json"
    with requestpath.open("x", encoding="ascii") as stream:
        for index, row in enumerate(requests):
            stream.write("\t".join(map(str, [index, row["N"], row["B"], len(row["faces"]), *row["faces"]]))+"\n")
    relative = lambda path: os.path.relpath(path, ROOT).replace("\\", "/")
    result = subprocess.run([
        WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
        "./test_eight_possible-linux", relative(requestpath), relative(answerpath), str(CAP8),
    ], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
    answers = read(answerpath)["results"]
    assert len(answers) == len(requests)
    stricter = excluded = 0
    witnesses = []
    for index, (row, answer) in enumerate(zip(requests, answers, strict=True)):
        assert answer["request"] == index
        assert answer["old_fast"] == answer["old_audit"]
        assert answer["eight_fast"] == answer["eight_audit"]
        assert not answer["eight_fast"] or answer["old_fast"]
        proof = exclusion(row["B"], row["N"], row["faces"], constants)
        assert bool(answer["eight_fast"]) == (proof is None), ("native/Python angle disagreement", index)
        if row["must_survive"]:
            assert proof is None and answer["eight_fast"], "known attaining graph was incorrectly rejected"
        if proof is not None:
            excluded += 1
            witnesses.append({"request": index, "N": row["N"], "B": row["B"],
                              "faces": row["faces"], **proof})
        stricter += bool(answer["old_fast"] and not answer["eight_fast"])
    (output / "EXACT-CYCLES.json").write_text(json.dumps(witnesses, indent=2)+"\n", encoding="utf8")
    no_screen = []
    base = ROOT / "outer-collar-controls-v3-deep-internal"
    base_report = read(base / "VERIFIED.json")
    assert base_report["verified"] and base_report["all_full_reference_outer_restrictions_present"]
    for case in base_report["cases"]:
        N, B, mode = case["N"], case["B"], case["mode"]
        oldpath = base / f"N{N}-B{B}-{mode}-collars.json"
        assert sha(oldpath) == case["collar_sha256"]
        _, expected = collar_codes(oldpath, N, B)
        target = output / f"N{N}-B{B}-{mode}.json"
        result = run_eight(N, B, target, mode)
        assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
        header, actual = collar_codes(target, N, B)
        assert not header["screen"] and not header["eight_rod_screen"] and header["cap8"] == CAP8
        assert actual == expected
        no_screen.append({"N": N, "B": B, "mode": mode, "complete_set_equal": True,
                          "old_sha256": sha(oldpath), "new_sha256": sha(target)})
        source_files.append(oldpath)
    screen_cases = []
    expected_reference = {canonical(20, 14, row["faces"], 1)[0] for _, row in reference_rows}
    for mode in ("dfs", "audit"):
        target = output / f"N20-B14-eight-{mode}.json"
        result = run_eight(20, 14, target, mode)
        assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
        header, codes = collar_codes(target, 20, 14)
        assert header["eight_rod_screen"] and header["cap8"] == CAP8
        not_present = 0
        for _, row in reference_rows:
            code = canonical(20, 14, row["faces"], 1)[0]
            if code not in codes:
                proof = exclusion(14, 20, row["faces"], constants)
                assert proof is not None, "a nonexcluded complete reference graph's collar was lost"
                not_present += 1
        screen_cases.append({"N": 20, "B": 14, "mode": mode,
                             "reference_complete_graphs": reference_header["orbits"],
                             "weak_graphs": len(codes), "missing_full_graphs_exactly_paid_by_angles": not_present,
                             "catalog_sha256": sha(target)})
    # Genuine use of a four-center path, rather than only old 2/4/6 bounds.
    eight_witness = next((w for w in witnesses if any(len(e.get("path", [])) == 4 for e in w["cycle"])), None)
    assert eight_witness is not None and stricter > 0
    negatives = []
    for label, mutation in (
        ("wrong-weight", lambda c: c[0].__setitem__("weight", c[0]["weight"]+1)),
        ("broken-cycle", lambda c: c[0].__setitem__("v", (c[0]["v"]+1) % eight_witness["B"])),
        ("too-long-path", lambda c: next(e for e in c if len(e.get("path", [])) == 4).__setitem__("path", [0]*5)),
    ):
        bad = deepcopy(eight_witness["cycle"])
        mutation(bad)
        try:
            verify_cycle(eight_witness["B"], eight_witness["N"], eight_witness["faces"], bad, constants)
        except (AssertionError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError(("forged cycle accepted", label))
    for label, N, B, limit, cap in (
        ("node-limit", 25, 14, 1, CAP8), ("bad-N", 26, 14, 0, CAP8),
        ("bad-B", 14, 15, 0, CAP8), ("bad-cap8", 25, 14, 0, 5000000),
    ):
        target = output / (label+".json")
        result = run_eight(N, B, target, limit=limit, cap8=cap)
        assert result.returncode != 0 and not target.exists()
        negatives.append(label)
    (output / "VERIFIED.json").write_text(json.dumps({
        "verified": True, "schema": "eight-rod-collar-controls-v1",
        "source_sha256": sha(Path(__file__)),
        "native_source_sha256": sha(ROOT / "peel_eight_rod_collar.cpp"),
        "native_binary_sha256": sha(ROOT / "peel_eight_rod_collar-linux"),
        "native_angle_source_sha256": sha(ROOT / "eight_rod_possible.inc"),
        "independent_cycle_checker_sha256": sha(ROOT / "eight_rod_angles.py"),
        "cap_report_sha256": sha(ROOT / "n25-eight-rod-exact-cap-20261005-v1.json"),
        "derivation_sha256": sha(ROOT / "eight-rod-collar-source-derivation.json"),
        "native_probe_source_sha256": sha(ROOT / "test_eight_possible.cpp"),
        "native_probe_binary_sha256": sha(ROOT / "test_eight_possible-linux"),
        "probe_derivation_sha256": sha(ROOT / "eight-possible-test-source-derivation.json"),
        "requests": len(requests), "native_results_agree_with_independent_exact_cycles": True,
        "exact_cycle_exclusions": excluded, "additional_exclusions_beyond_old_angles": stricter,
        "all_four_exact_attaining_controls_retained": True,
        "no_screen_complete_controls": no_screen, "complete_screened_reference_controls": screen_cases,
        "negative_controls_rejected": negatives, "cycles_sha256": sha(output / "EXACT-CYCLES.json"),
        "empty_proxy_retries_after_real_native_absence": EMPTY_LAUNCH_RETRIES,
        "input_files": {os.path.relpath(p, ROOT).replace("\\", "/"): sha(p) for p in source_files},
        "complete_n25_search_not_run_here": True, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    print("Eight-rod controls PASS:", len(requests), "independent graph comparisons;",
          stricter, "additional exclusions;", len(no_screen), "complete no-screen cases;", flush=True)


if __name__ == "__main__":
    main()
