"""Old/new support-filter matching equality with exact explicit positive maps."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import validate
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate
from cached_support_gate import derivation_gate
from test_origin_collar import native, relative

assert __debug__


def request_rows(path):
    with path.open(encoding="ascii") as stream:
        for index, line in enumerate(stream):
            tokens = [int(value) for value in line.split()]
            assert tokens[0] == index and tokens[1] == len(tokens)-2
            faces = tokens[2:]
            assert faces == sorted(set(faces)) and faces
            yield index, faces


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    files = derivation_gate()
    library_path = ROOT / "n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json"
    constants, library, table, dependencies = sparse_library_gate(library_path)
    files.update(dependencies)
    assert library["B"] == 16 and library["obstacle_count"] == 164
    maps_path = ROOT / "n25-B16-offline-union-sparse-map-controls-20261005-v1/VERIFIED.json"
    maps = read(maps_path)
    assert maps["verified"] and maps["library_sha256"] == sha(library_path)
    assert maps["known_B16_attaining_graph_not_matched"]
    unchanged(maps["files_relative_to_workspace"])
    slab_path = ROOT / "n25-B16-origin-slab0-union164-sparse-payments-20261005-v1/VERIFIED.json"
    slab = read(slab_path)
    assert slab["verified"] and slab["finite_rows_fully_scanned"] == 100000
    assert slab["library_sha256"] == sha(library_path)
    unchanged(slab["files_relative_to_workspace"])
    output.mkdir()
    cases = []
    obstacles = {row["id"]: row for row in library["obstacles"]}
    for name, directory in (
        ("synthetic-independent-attaining", maps_path.parent),
        ("actual-closed-slab100000", slab_path.parent),
    ):
        requests_path, old_answers_path = directory / "REQUESTS.tsv", directory / "NATIVE-MAPS.json"
        old = read(old_answers_path)
        if directory == maps_path.parent:
            assert sha(old_answers_path) == maps["native_maps_sha256"]
        else:
            source_proposal = read(directory / "PROPOSAL.json")
            assert sha(old_answers_path) == source_proposal["native_maps_sha256"]
        new_answers_path = output / (name+"-SUPPORT-MAPS.json")
        started = time.monotonic()
        process = native("sparse_support_cached_match-linux", [
            "match", 25, 16, relative(table), relative(requests_path), relative(new_answers_path)])
        seconds = time.monotonic()-started
        publish(output / (name+"-TERMINAL.json"), {
            "actual_exit_code": process.returncode, "seconds": seconds,
            "stdout": process.stdout.decode(errors="replace"), "stderr": process.stderr.decode(errors="replace"),
        })
        assert process.returncode == 0, (process.returncode, process.stderr)
        new = read(new_answers_path)
        assert new == old, "A necessary fast filter changed the old first successful map"
        assert new["scope"] == "sparse subgraph maps only"
        count = positive = 0
        for index, faces in request_rows(requests_path):
            answer = new["matches"][index]
            assert answer["request"] == index
            if answer["obstacle"] >= 0:
                obstacle = obstacles[answer["obstacle"]]
                mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
                assert len(mapping["centers"]) == obstacle["centers"]
                validate(25, 16, obstacle["faces"], mapping, faces)
                positive += 1
            else:
                assert answer["obstacle"] == -1
            count += 1
        assert count == len(new["matches"])
        cases.append({"name": name, "requests": count, "positive_maps_checked": positive,
                      "all_old_new_answers_and_maps_equal": True, "new_native_seconds": seconds,
                      "requests_sha256": sha(requests_path), "old_answers_sha256": sha(old_answers_path),
                      "new_answers_sha256": sha(new_answers_path)})
        for path in (requests_path, old_answers_path, new_answers_path):
            bind(files, path)
        print("Necessary support filters match equality PASS:", name, count, "requests;",
              positive, "explicit positives;", round(seconds, 2), "native seconds", flush=True)
    rejected = []
    good_requests = maps_path.parent / "REQUESTS.tsv"
    lines = table.read_text(encoding="ascii").splitlines()
    for label, bad_lines in (
        ("bad-schema", ["not-a-sparse-library", *lines[1:]]),
        ("bad-id", [lines[0], lines[1].replace("0\t", "1\t", 1)]),
        ("extra-column", [lines[0], lines[1]+"\t0"]),
    ):
        bad_table, answer_path = output / (label+".tsv"), output / (label+"-MAPS.json")
        bad_table.write_text("\n".join(bad_lines)+"\n", encoding="ascii")
        process = native("sparse_support_cached_match-linux", [
            "match", 25, 16, relative(bad_table), relative(good_requests), relative(answer_path)])
        assert process.returncode != 0 and not answer_path.exists()
        rejected.append(label)
    answer_path = output / "bad-N-MAPS.json"
    process = native("sparse_support_cached_match-linux", [
        "match", 26, 16, relative(table), relative(good_requests), relative(answer_path)])
    assert process.returncode != 0 and not answer_path.exists()
    rejected.append("bad-N")
    for path in (Path(__file__), library_path, maps_path, slab_path,
                 ROOT / "sparse_support_cached_match-linux", ROOT / "sparse_outer_match-linux",
                 ROOT / "support_filter_gate.py", HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "bounded-sparse-support-cache-map-controls-v1",
        "N": 25, "B": 16, "cases": cases, "all_old_new_first_positive_maps_identical": True,
        "all_positive_center_anchor_and_face_maps_checked": True,
        "known_attaining_result_unchanged_from_frozen_control": True,
        "negative_controls_rejected": rejected, "library_sha256": sha(library_path),
        "native_binary_sha256": sha(ROOT / "sparse_support_cached_match-linux"),
        "derivation_sha256": sha(ROOT / "cached-sparse-support-source-derivation.json"),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "does_not_certify_complete_search_or_new_graph_theorems": True,
        "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
