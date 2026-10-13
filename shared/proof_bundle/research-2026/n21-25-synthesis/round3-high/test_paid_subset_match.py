"""Read-only exact strict-subgraph controls and a real closed-block probe."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import random
import subprocess
import time
from audit_paid_regression import check_subset, find_subset
from paid_binary_residual import BinaryRows
from positive_core_completion_synthesis import disk_check
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2].resolve()
assert __debug__


def read(path):
    return json.loads(Path(path).read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--rows", type=int, default=2000)
    args = ap.parse_args()
    assert 0 < args.rows <= 100000 and not args.output.exists()
    args.output.mkdir(parents=True)
    N, B = 25, 14
    librarypath = ROOT / "evidence/n22-portable-strict-obstacles-resume1/LIBRARY.json"
    library = read(librarypath)
    assert library["verified"] and library["all_library_trees_fresh_exact_replayed"]
    assert library["no_root_or_local_theorem_used"]
    constants = read(ROOT.parent / "evidence/core-reduction/constants/n25.json")
    assert F(constants["radius_upper"]) <= F(library["radius_threshold"])
    for name, digest in library["files"].items():
        assert sha(WORK / name) == digest
    table = librarypath.parent / "OBSTACLES.tsv"
    assert sha(table) == library["pattern_table_sha256"]
    patterns = [row for row in library["obstacles"] if row["B"] == B]
    byid = {row["id"]: row for row in patterns}
    assert len(patterns) == 1478
    selected = [row for row in patterns if row["centers"] == 22][:24]
    assert len(selected) == 24
    rng = random.Random(251425)
    requests = []
    # Artificial strict supergraphs test the transport lemma, not planar
    # completion or geometry feasibility. Their extra used label rules out
    # equality with any N22 library graph.
    for pattern in selected:
        for sign, shift in ((1, 0), (-1, 5)):
            inside = list(range(B, 24))
            rng.shuffle(inside)
            center = [(shift+sign*j) % B for j in range(B)]+inside[:22-B]
            images = [sum(1 << center[v] for v in range(22) if mask >> v & 1)
                      for mask in pattern["faces"]]
            images.append((1 << 0)|(1 << 1)|(1 << 24))
            requests.append({"kind": "artificial-strict-supergraph", "faces": sorted(set(images))})
    positive_count = len(requests)
    rawpath = ROOT / "evidence/n25-B14-paid-streamed-resume1/N25-B14-paid-residual.bin.runs/run-0.bin"
    original_hash = sha(rawpath)
    weak_to_full = {}
    for index, row in BinaryRows(rawpath, run=True).rows():
        assert disk_check(N, B, {tuple(v for v in range(N) if mask >> v & 1) for mask in row["faces"]})
        weak = tuple(mask for mask in row["faces"] if (mask & ((1 << B)-1)).bit_count() >= 2)
        weak_to_full.setdefault(weak, row["faces"])
        if index+1 == args.rows:
            break
    assert len(weak_to_full) > 0 and sha(rawpath) == original_hash
    for weak, full in weak_to_full.items():
        requests.append({"kind": "real-closed-block-weak-graph", "faces": list(weak), "full": full})
    requestpath = args.output / "REQUESTS.tsv"
    with requestpath.open("x", encoding="ascii") as stream:
        for i, request in enumerate(requests):
            stream.write("\t".join(map(str, [i, len(request["faces"]), *request["faces"]]))+"\n")
    target = args.output / "MATCHES.json"
    started = time.monotonic()
    process = subprocess.run([str(ROOT / "paid_subset_match.exe"), str(N), str(B), str(table),
                              str(requestpath), str(target)], cwd=ROOT, capture_output=True)
    assert process.returncode == 0, process.stderr
    answers = read(target)["matches"]
    assert len(answers) == len(requests)
    legacy = subset = gained = 0
    for i, (request, answer) in enumerate(zip(requests, answers, strict=True)):
        assert answer["request"] == i
        oid = answer["obstacle"]
        if oid >= 0:
            mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
            check_subset(N, B, byid[oid], mapping, set(request["faces"]))
            if request["kind"] == "real-closed-block-weak-graph":
                check_subset(N, B, byid[oid], mapping, set(request["full"]))
        if i < positive_count:
            assert oid >= 0 and answer["legacy_exact_obstacle"] < 0
        else:
            legacy += answer["legacy_exact_obstacle"] >= 0
            subset += oid >= 0
            gained += oid >= 0 and answer["legacy_exact_obstacle"] < 0
    # Independently establish existence on five bounded cases. Returned maps
    # for ALL hits were already checked, not only these existence controls.
    for i in range(min(5, positive_count)):
        assert any(find_subset(N, B, pattern, requests[i]["faces"]) is not None for pattern in patterns)
    badpath = args.output / "BAD-REQUEST.tsv"
    with badpath.open("x", encoding="ascii") as stream:
        stream.write("0\t1\t1\n")
    rejected = args.output / "BAD-PROPOSAL.json"
    bad = subprocess.run([str(ROOT / "paid_subset_match.exe"), str(N), str(B), str(table),
                          str(badpath), str(rejected)], cwd=ROOT, capture_output=True)
    assert bad.returncode != 0
    report = {"verified": True, "N": N, "B": B,
              "artificial_strict_supergraph_controls": positive_count,
              "all_emitted_positive_maps_independently_checked": True,
              "real_full_disk_rows_checked": args.rows,
              "distinct_real_weak_graphs": len(weak_to_full),
              "real_weak_graphs_legacy_exact_match": legacy,
              "real_weak_graphs_strict_subset_match": subset,
              "real_weak_graphs_newly_matched": gained,
              "real_hit_maps_also_checked_into_full_graph": True,
              "library_sha256": sha(librarypath), "table_sha256": sha(table),
              "closed_input_block_sha256": original_hash,
              "request_sha256": sha(requestpath), "matches_sha256": sha(target),
              "native_source_sha256": sha(ROOT / "paid_subset_match.cpp"),
              "native_binary_sha256": sha(ROOT / "paid_subset_match.exe"),
              "source_sha256": sha(Path(__file__)), "seconds": time.monotonic()-started,
              "negative_controls_rejected": ["nontriangle-request"],
              "used_in_any_production_search": False,
              "full_necessary_family_classified": False, "global_optimality_proved": False,
              "scope": "strict subset transport prototype and selected real-block probe only"}
    with (args.output / "VERIFIED.json").open("x", encoding="utf8") as stream:
        json.dump(report, stream, indent=2)
    print("Strict subset prototype controls PASS:", positive_count, "artificial supergraphs;",
          len(weak_to_full), "real weak graphs;", gained, "new real matches; production not modified", flush=True)


if __name__ == "__main__":
    main()
