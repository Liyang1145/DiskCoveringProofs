"""Force tiny slabs and verify complete union equality, duplicates and rejection."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from test_outer_collar import linux_path, WSL, collar_codes
from merge_collar_chunks import merge

assert __debug__


def derivation_gate():
    report = read(ROOT / "streamed-collar-source-derivation.json")
    assert report["verified_mechanical_derivation"]
    assert report["original_source_sha256"] == sha(ROOT / "peel_eight_rod_collar.cpp")
    assert report["derived_source_sha256"] == sha(ROOT / "peel_streamed_collar.cpp")
    assert report["storage_include_sha256"] == sha(ROOT / "collar_chunk_storage.inc")
    assert report["source_sha256"] == sha(ROOT / "derive_streamed_collar.py")
    text = (ROOT / "peel_eight_rod_collar.cpp").read_text(encoding="utf8")
    for (before, after), count in zip(report["changes"], report["occurrence_counts"], strict=True):
        assert text.count(before) == count
        text = text.replace(before, after)
    assert text == (ROOT / "peel_streamed_collar.cpp").read_text(encoding="utf8")


def run_streamed(N, B, output, slab, mode="dfs", limit=0, table="-"):
    c = read(HIGH.parent / "evidence/core-reduction/constants/n25.json")
    relative = lambda p: os.path.relpath(Path(p).resolve(), ROOT).replace("\\", "/")
    table = "-" if table == "-" else relative(table)
    return subprocess.run([
        WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
        "./peel_streamed_collar-linux", str(N), str(B), relative(output),
        str(c["angle_scale"]), *map(str, c["angle_caps"]), str(limit), mode, "-", table,
        "4058615", str(slab),
    ], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)


def codes_from_union(path):
    with path.open(encoding="ascii") as stream:
        header = json.loads(next(stream))
        return header, {tuple(json.loads(line)["faces"]) for line in stream}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    derivation_gate()
    output.mkdir()
    base = ROOT / "n25-B14-eight-sparse-guard-controls-20261005-v1"
    controls = read(base / "VERIFIED.json")
    assert controls["verified"] and controls["all_baseline_minus_residual_graphs_individually_paid"]
    cases, positive = [], None
    for N, mode, slab, sparse in ((20, "dfs", 1, False), (21, "dfs", 7, False),
                                  (21, "audit", 2, False), (21, "dfs", 1, True)):
        reference = base / (f"N{N}-B14-eight-"+("sparse-dfs.json" if sparse else "baseline.json"))
        expected_digest = next(row["residual_sha256"] if sparse else row["baseline_sha256"]
                               for row in controls["cases"] if row["N"] == N and row["mode"] == "dfs")
        assert sha(reference) == expected_digest
        _, expected = collar_codes(reference, N, 14)
        case = output / f"N{N}-{mode}-slab{slab}-sparse{int(sparse)}"
        case.mkdir()
        target = case / "MANIFEST.json"
        table = ROOT / "n25-B14-union-sparse-library-20261005-v1/OBSTACLES.tsv" if sparse else "-"
        result = run_streamed(N, 14, target, slab, mode, table=table)
        publish(case / "NATIVE-TERMINAL.json", {
            "native_terminal_observed": True, "actual_exit_code": result.returncode,
            "stdout": result.stdout.decode("utf8", errors="replace"),
            "stderr": result.stderr.decode("utf8", errors="replace"),
            "manifest_sha256": sha(target) if target.exists() else None,
        })
        assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
        accepted = merge(target, result.returncode, case / "UNION")
        header, actual = codes_from_union(case / "UNION/CATALOG.jsonl")
        assert actual == expected
        cases.append({
            "N": N, "B": 14, "mode": mode, "slab_limit": slab, "sparse_guard_enabled": sparse,
            "unique_graphs": len(actual), "complete_set_equals_in_memory_reference": True,
            "cross_slab_duplicates_removed": accepted["cross_slab_duplicates_removed"],
            "manifest_sha256": sha(target), "union_replay_sha256": sha(case / "UNION/VERIFIED.json"),
        })
        if len(read(target)["chunks"]) > 1:
            positive = target
        print("Complete slab union comparison PASS:", N, mode, slab,
              len(actual), "graphs;", accepted["cross_slab_duplicates_removed"], "duplicates", flush=True)
    assert positive is not None and any(row["cross_slab_duplicates_removed"] > 0 for row in cases)
    negatives = []
    target = output / "node-limit.json"
    result = run_streamed(25, 15, target, 2, limit=1)
    assert result.returncode != 0 and not target.exists()
    negatives.append("node-limit-no-complete-manifest")
    try:
        merge(positive, 1, output / "illegal-nonzero-union")
    except AssertionError:
        negatives.append("nonzero-exit-rejected")
    else:
        raise AssertionError("accepted nonzero search")
    manifest = read(positive)
    for label, mutate in (
        ("missing-slab", lambda m: None),
        ("wrong-row-count", lambda m: m["chunks"][0].__setitem__("rows", m["chunks"][0]["rows"]+1)),
        ("prefix-manifest", lambda m: m.__setitem__("complete_necessary_outer_search", False)),
    ):
        bad = deepcopy(manifest)
        path = positive.parent / (label+".json")
        for index, chunk in enumerate(bad["chunks"]):
            original_path = ROOT / chunk["file"]
            replacement_path = path.with_name(path.name+f".chunk-{index}.jsonl")
            assert not replacement_path.exists()
            chunk["file"] = replacement_path.relative_to(ROOT).as_posix()
            if label != "prefix-manifest" and not (label == "missing-slab" and index == 0):
                shutil.copyfile(original_path, replacement_path)
        mutate(bad)
        publish(path, bad)
        try:
            merge(path, 0, output / (label+"-union"))
        except (AssertionError, FileNotFoundError):
            negatives.append(label)
        else:
            raise AssertionError(("corrupt slab set accepted", label))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "streamed-collar-storage-controls-v1",
        "source_sha256": sha(Path(__file__)),
        "native_source_sha256": sha(ROOT / "peel_streamed_collar.cpp"),
        "native_binary_sha256": sha(ROOT / "peel_streamed_collar-linux"),
        "storage_include_sha256": sha(ROOT / "collar_chunk_storage.inc"),
        "merge_source_sha256": sha(ROOT / "merge_collar_chunks.py"),
        "derivation_sha256": sha(ROOT / "streamed-collar-source-derivation.json"),
        "all_complete_union_sets_equal_to_in_memory_references": True,
        "cases": cases, "negative_controls_rejected": negatives,
        "full_n25_search_not_run_by_this_control": True, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
