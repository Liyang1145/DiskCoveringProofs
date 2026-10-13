"""Exact sorted slab validation and streaming union; not a geometric lower bound."""
from pathlib import Path
import argparse
import heapq
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import canonical, validate
from n25_outer_search import read, publish

assert __debug__


def merge(manifestpath, native_terminal, output, verify_canonical=True):
    assert native_terminal == 0, "only real zero exit can accept a complete sorted-chunk search"
    manifest = read(manifestpath)
    assert manifest["schema"] == "complete-outer-collar-sorted-chunks-v1"
    assert manifest["complete_necessary_outer_search"] and not manifest["complete_full_triangulations"]
    N, B = manifest["N"], manifest["B"]
    assert 3 <= B <= N <= 25
    assert len(manifest["chunks"]) == manifest["chunk_count"]
    assert not output.exists()
    output.mkdir()
    input_chunks, paths = [], []
    for index, chunk in enumerate(manifest["chunks"]):
        path = (ROOT / chunk["file"]).resolve()
        assert path.is_relative_to(manifestpath.resolve().parent)
        assert path.name == manifestpath.name+f".chunk-{index}.jsonl"
        assert 0 < chunk["rows"] <= manifest["slab_limit"]
        paths.append(path)
        input_chunks.append({"file": path.name, "sha256": sha(path), "rows": chunk["rows"]})

    def rows(index):
        chunk, path = manifest["chunks"][index], paths[index]
        count, previous = 0, None
        with path.open(encoding="ascii") as stream:
            first = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
            assert first == {"schema": "sorted-outer-collar-slab-v1", "N": N, "B": B,
                             "index": index, "rows": chunk["rows"], "not_a_complete_search": True}
            for line in stream:
                row = json.loads(line, object_pairs_hook=no_duplicate_keys)
                centers, faces = row["centers"], row["faces"]
                assert B <= centers <= N and faces and faces == sorted(set(faces))
                assert all(type(mask) is int and 0 < mask < 1 << centers and mask.bit_count() == 3
                           and mask & ((1 << B)-1) for mask in faces)
                used = 0
                for face in faces:
                    used |= face
                assert used == (1 << centers)-1
                code = tuple(faces)
                assert previous is None or previous < code
                previous = code
                if verify_canonical:
                    canonical_code, mapping = canonical(centers, B, faces, 1)
                    assert canonical_code == code and len(mapping["centers"]) == centers
                    validate(centers, B, faces, mapping, faces)
                count += 1
                yield code, centers
        assert count == chunk["rows"]
        assert sha(path) == input_chunks[index]["sha256"]

    iterators, heap = [], []
    for index in range(len(paths)):
        iterator = iter(rows(index))
        iterators.append(iterator)
        try:
            code, centers = next(iterator)
        except StopIteration:
            raise AssertionError("manifest referenced an empty slab")
        heapq.heappush(heap, (code, centers, index))
    catalog, bindings = output / "CATALOG.jsonl", output / "bindings.jsonl"
    unique = processed = 0
    previous_code, previous_centers = None, None
    with catalog.open("x", encoding="ascii") as target, bindings.open("x", encoding="ascii") as bound:
        target.write(json.dumps({"schema": "complete-necessary-collar-union-jsonl-v1",
                                 "N": N, "B": B, "members_are_weak_graphs_not_full_types": True},
                                separators=(",", ":"))+"\n")
        while heap:
            code, centers, index = heapq.heappop(heap)
            processed += 1
            if code == previous_code:
                assert centers == previous_centers
            else:
                assert previous_code is None or previous_code < code
                target.write(json.dumps({"id": unique, "centers": centers, "faces": list(code), "members": 1},
                                        separators=(",", ":"))+"\n")
                bound.write(json.dumps({"index": unique, "group": unique, "map": {
                    "centers": list(range(centers)), "anchors": list(range(B)), "orientation": 1, "shift": 0}},
                    separators=(",", ":"))+"\n")
                previous_code, previous_centers = code, centers
                unique += 1
            try:
                nextcode, nextcenters = next(iterators[index])
            except StopIteration:
                continue
            heapq.heappush(heap, (nextcode, nextcenters, index))
    assert processed == sum(chunk["rows"] for chunk in manifest["chunks"]) == manifest["rows_to_chunks_not_unique_types"]
    for item, path in zip(input_chunks, paths, strict=True):
        assert sha(path) == item["sha256"]
    report = {
        "verified": True, "schema": "independent-complete-collar-slab-union-v1", "N": N, "B": B,
        "native_manifest_sha256": sha(manifestpath), "actual_native_exit_code": native_terminal,
        "all_declared_slabs_fully_scanned": True, "all_rows_ordered_and_canonical_checked": verify_canonical,
        "complete_streaming_set_union": True, "input_rows_including_cross_slab_duplicates": processed,
        "unique_necessary_weak_graphs": unique, "cross_slab_duplicates_removed": processed-unique,
        "catalog_file": catalog.name, "catalog_sha256": sha(catalog),
        "bindings_file": bindings.name, "bindings_sha256": sha(bindings), "input_chunks": input_chunks,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
        "all_residual_lower_bounds_not_paid_by_this_merge": True,
    }
    publish(output / "VERIFIED.json", report)
    return report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", type=Path, required=True)
    ap.add_argument("--terminal", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    terminal = read(args.terminal)
    assert terminal["native_terminal_observed"]
    assert terminal["manifest_sha256"] == sha(args.manifest)
    result = merge(args.manifest.resolve(), terminal["actual_exit_code"], args.output.resolve())
    print("Independent complete sorted-collar union accepted:",
          result["unique_necessary_weak_graphs"], "unpaid weak graphs", flush=True)


if __name__ == "__main__":
    main()
