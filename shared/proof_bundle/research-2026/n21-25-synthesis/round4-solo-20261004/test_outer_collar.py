"""Complete small-family containment controls for the new collar overapproximation."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import canonical
from paid_binary_residual import BinaryRows, verify_merge
from audit_streamed_hierarchy import check_map

assert __debug__
WSL = r"C:\Windows\System32\wsl.exe"


def linux_path(path):
    path = Path(path).resolve()
    assert path.drive.upper() == "C:"
    return "/mnt/c/" + path.as_posix()[3:]


def run_collar(n, b, output, mode, table="-", limit=0, caps=(2000000, 4200000, 4800000)):
    relative = os.path.relpath(Path(output).resolve(), ROOT).replace("\\", "/")
    assert relative.isascii()
    if table != "-":
        table = os.path.relpath(Path(table).resolve(), ROOT).replace("\\", "/")
        assert table.isascii()
    command = [WSL, "--distribution", "Ubuntu2204",
               "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
               "./peel_outer_collar-linux", str(n), str(b), relative,
               "10000000", *map(str, caps), str(limit), mode, table]
    return subprocess.run(command, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)


def source_derivation():
    old = (HIGH / "peel_paid_stream_kernel.inc").read_text(encoding="utf8")
    new = (ROOT / "peel_outer_collar.cpp").read_text(encoding="utf8")
    start = " int pick=pending.size()-1;"
    old_body = old[old.index(start):old.index("\n}\n\nint main", old.index(start))]
    new_body = new[new.index(start):new.index("\n}\n\nint main", new.index(start))]
    for before, after in [
        ("visit(s,pending)", "visit_collar(s,pending,omitted_faces)"),
        ("visit(next,work)", "visit_collar(next,work,omitted_faces)"),
        ("visit(next,pending)", "visit_collar(next,pending,omitted_faces)"),
    ]:
        assert old_body.count(before) == 1
        old_body = old_body.replace(before, after, 1)
    assert old_body == new_body, "non-omitted splitting recursion changed"
    assert '#include "../round3-high/peel_degree.cpp"' in new
    assert '#include "../round3-high/paid_outer_matcher.inc"' in new


def collar_codes(path, n, b):
    report = json.loads(path.read_text(encoding="utf8"))
    assert report["schema"] == "outer-collar-overapproximation-v1"
    assert report["complete_necessary_outer_search"] and not report["complete_full_triangulations"]
    assert (report["N"], report["B"]) == (n, b)
    rows = report["weak_graphs"]
    assert len(rows) == report["weak_graph_count"]
    codes = set()
    previous = None
    for row in rows:
        centers, masks = row["centers"], row["faces"]
        assert b <= centers <= n and masks == sorted(set(masks))
        code, mapping = canonical(centers, b, masks, 1)
        assert code == tuple(masks)
        check_map(centers, b, row, mapping, set(masks), 1)
        assert previous is None or previous < code
        previous = code
        assert code not in codes
        codes.add(code)
    return report, codes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT.resolve()) and not output.exists()
    source_derivation()
    output.mkdir(parents=True)
    cases = []
    for n, b in ((3, 3), (5, 3), (6, 4), (7, 4), (8, 5), (9, 6),
                 (10, 3), (10, 4), (11, 3)):
        referencepath = output / f"N{n}-B{b}-full-reference.bin"
        relative = os.path.relpath(referencepath, HIGH).replace("\\", "/")
        reference = subprocess.run(
            [str(HIGH / "peel_outer_stream.exe"), str(n), str(b), relative,
             "10000000", "2000000", "4200000", "4800000", "0", "noscreen", "-"],
            cwd=HIGH, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        assert reference.returncode == 0, reference.stderr
        refhead, _ = verify_merge(referencepath)
        assert refhead["proof_prunes"] == 0
        expected = {canonical(n, b, row["faces"], 1)[0] for _, row in BinaryRows(referencepath).rows()}
        for mode in ("noscreen", "audit-noscreen"):
            target = output / f"N{n}-B{b}-{mode}-collars.json"
            result = run_collar(n, b, target, mode)
            (output / f"N{n}-B{b}-{mode}.stderr").write_bytes(result.stderr)
            assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
            header, actual = collar_codes(target, n, b)
            assert expected <= actual, ("a true full graph's outer collar was lost", n, b, mode)
            cases.append({
                "N": n, "B": b, "mode": mode, "full_reference_graphs": refhead["orbits"],
                "full_reference_distinct_outer_graphs": len(expected),
                "collar_overapproximation_graphs": len(actual),
                "all_full_graph_outer_restrictions_present": True,
                "allowed_extra_weak_graphs": len(actual - expected),
                "calls": header["calls"], "dropped_region_counter": header["omitted_internal_regions_not_type_count"],
                "reference_sha256": sha(referencepath), "collar_sha256": sha(target),
            })
        print("Collar full-family containment PASS:", n, b, refhead["orbits"], "complete reference graphs", flush=True)
    # Same B14 and U25, with new actual proof-pruning library.
    const = json.loads((ROOT.parent / "evidence/core-reduction/constants/n25.json").read_text())
    table = ROOT / "n25-B14-strict-outer-library-v1/OBSTACLES.tsv"
    library = json.loads((table.parent / "LIBRARY.json").read_text())
    target = output / "N20-B14-U25-paid-collars.json"
    result = run_collar(20, 14, target, "dfs", table, caps=const["angle_caps"])
    (output / "N20-B14-U25-paid-collars.stderr").write_bytes(result.stderr)
    assert result.returncode == 0, result.stderr
    header, actual = collar_codes(target, 20, 14)
    referencepath = ROOT / "n25-B14-outer-library-controls-v3-static/N20-B14-no-payment-reference.bin"
    expected = {canonical(20, 14, row["faces"], 1)[0] for _, row in BinaryRows(referencepath).rows()}
    bycode = {tuple(o["faces"]): o for o in library["obstacles"] if o["centers"] <= 20}
    assert all(code in actual or code in bycode for code in expected)
    for payment in header["proof_payments"]:
        obstacle = library["obstacles"][payment["obstacle"]]
        mapping = {k: payment[k] for k in ("centers", "anchors", "orientation", "shift")}
        check_map(20, 14, obstacle, mapping, set(payment["sample_faces"]), 1)
    negatives = []
    for label, n, b, limit in (("node-limit", 25, 14, 1), ("bad-N", 26, 14, 0), ("bad-B", 14, 15, 0)):
        target = output / (label + ".json")
        result = run_collar(n, b, target, "dfs", table, limit=limit, caps=const["angle_caps"])
        assert result.returncode != 0 and not target.exists()
        negatives.append(label)
    compiler = subprocess.run([WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/g++", "--version"],
                              capture_output=True, check=True, creationflags=subprocess.CREATE_NO_WINDOW)
    report = {
        "verified": True, "schema": "outer-collar-source-and-small-controls-v1",
        "source_sha256": sha(Path(__file__)), "native_source_sha256": sha(ROOT / "peel_outer_collar.cpp"),
        "native_binary_sha256": sha(ROOT / "peel_outer_collar-linux"),
        "frozen_degree_source_sha256": sha(HIGH / "peel_degree.cpp"),
        "frozen_outer_matcher_sha256": sha(HIGH / "paid_outer_matcher.inc"),
        "splitting_recursion_mechanically_preserved_except_recursive_name_and_omission_accounting": True,
        "cases": cases, "all_full_reference_outer_restrictions_present": True,
        "same_B14_actual_library_pruning_reference_containment": True,
        "same_B14_paid_weak_graphs": header["weak_graph_count"],
        "same_B14_source_reference_outer_graphs": len(expected),
        "same_B14_payment_samples_verified": len(header["proof_payments"]),
        "negative_controls_rejected": negatives,
        "compiler_version_text": compiler.stdout.decode("utf8"),
        "compiler_flags": ["-O3", "-std=c++20", "-static"],
        "native_platform": "Ubuntu2204 WSL; explicitly new platform, not old Windows binary",
        "full_n25_necessary_search_not_run_by_this_control": True,
        "global_optimality_proved": False,
    }
    (output / "VERIFIED.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("New collar controls PASS:", len(cases), "complete containment cases;",
          len(negatives), "fail-closed controls; no n25 completion claim", flush=True)


if __name__ == "__main__":
    main()
