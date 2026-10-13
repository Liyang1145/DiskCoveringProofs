"""Independent complete sorted-slab union for the new small-order source schema."""
from pathlib import Path
from fractions import Fraction as F
import heapq
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import canonical
from audit_streamed_hierarchy import check_map
from n25_outer_search import read, publish

assert __debug__


def gate(manifest):
    assert manifest["schema"] == "complete-small-order-origin-collar-sorted-chunks-v1"
    assert manifest["complete_necessary_outer_search"] and not manifest["complete_full_triangulations"]
    N, B = manifest["N"], manifest["B"]
    assert type(N) is int and type(B) is int and 3 <= B <= N <= 25
    assert manifest["origin_cover_orders"] == [23, 24]
    assert manifest["origin_cover_scope"] == "actual arbitrary disk covers only; not weak graph geometry"
    assert manifest["disk_guard_bytes"] == 4*1024**3
    assert manifest["proof_prunes"] == 0 and not manifest["proof_payments"]
    assert manifest["sparse_proof_prunes"] == 0 and not manifest["sparse_payments"]
    if manifest["origin_cover_screen"]:
        expected = {23: F(249953776586051, 10**15), 24: F(61325412542131, 250000000000000)}
        assert N in expected
        U = F(manifest["origin_radius_upper_numerator"], manifest["origin_radius_upper_denominator"])
        assert U == expected[N] and U < F(1, 4)
        for sample in manifest["origin_cover_samples"]:
            mask = (1 << B)-1
            for face in sample["outer_faces"]:
                assert type(face) is int and 0 < face < 1 << N and face.bit_count() == 3
                assert face & ((1 << B)-1)
                mask |= face
            assert mask == (1 << N)-1
    else:
        assert manifest["origin_cover_prunes_not_type_count"] == 0 and not manifest["origin_cover_samples"]
    return N, B


def merge(manifestpath, actual_code, output):
    assert type(actual_code) is int and actual_code == 0
    manifestpath, output = Path(manifestpath).resolve(), Path(output).resolve()
    assert manifestpath.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    manifest = read(manifestpath)
    N, B = gate(manifest)
    assert len(manifest["chunks"]) == manifest["chunk_count"]
    maximum = N-1 if manifest["origin_cover_screen"] else N
    paths, inputs = [], []
    for index, chunk in enumerate(manifest["chunks"]):
        path = (ROOT / chunk["file"]).resolve()
        assert path.parent == manifestpath.parent
        assert path.name == manifestpath.name+f".chunk-{index}.jsonl"
        assert type(chunk["rows"]) is int and 0 < chunk["rows"] <= manifest["slab_limit"]
        paths.append(path)
        inputs.append({"file": path.name, "sha256": sha(path), "rows": chunk["rows"]})
    assert sum(path.stat().st_size for path in paths) == manifest["bytes_to_chunks"]

    def rows(index):
        previous, count = None, 0
        with paths[index].open(encoding="ascii") as stream:
            header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
            assert header == {
                "schema": "sorted-outer-collar-slab-v1", "N": N, "B": B,
                "index": index, "rows": manifest["chunks"][index]["rows"], "not_a_complete_search": True}
            for line in stream:
                row = json.loads(line, object_pairs_hook=no_duplicate_keys)
                assert set(row) == {"centers", "faces"}
                centers, faces = row["centers"], row["faces"]
                assert type(centers) is int and B <= centers <= maximum
                assert faces == sorted(set(faces)) and faces
                assert all(type(mask) is int and 0 < mask < 1 << centers
                           and mask.bit_count() == 3 and mask & ((1 << B)-1) for mask in faces)
                used = 0
                for mask in faces:
                    used |= mask
                assert used == (1 << centers)-1
                code = tuple(faces)
                assert previous is None or previous < code
                previous = code
                actualcode, mapping = canonical(centers, B, faces, 1)
                assert actualcode == code and len(mapping["centers"]) == centers
                check_map(centers, B, row, mapping, set(faces), 1)
                count += 1
                yield code, centers
        assert count == inputs[index]["rows"] and sha(paths[index]) == inputs[index]["sha256"]

    iterators, heap = [], []
    for index in range(len(paths)):
        iterator = iter(rows(index))
        iterators.append(iterator)
        item = next(iterator, None)
        assert item is not None
        heapq.heappush(heap, (*item, index))
    output.mkdir()
    catalogpath, bindingspath = output / "CATALOG.jsonl", output / "bindings.jsonl"
    processed = unique = 0
    previous, oldcenters = None, None
    with catalogpath.open("x", encoding="ascii") as target, bindingspath.open("x", encoding="ascii") as bindings:
        target.write(json.dumps({
            "schema": "complete-necessary-small-order-collar-union-v1", "N": N, "B": B,
            "members_are_weak_graphs_not_full_types": True}, separators=(",", ":"))+"\n")
        while heap:
            code, centers, index = heapq.heappop(heap)
            processed += 1
            if code == previous:
                assert centers == oldcenters
            else:
                assert previous is None or previous < code
                target.write(json.dumps({
                    "id": unique, "centers": centers, "faces": list(code), "members": 1},
                    separators=(",", ":"))+"\n")
                bindings.write(json.dumps({
                    "index": unique, "group": unique, "map": {
                        "centers": list(range(centers)), "anchors": list(range(B)), "orientation": 1, "shift": 0}},
                    separators=(",", ":"))+"\n")
                unique += 1
                previous, oldcenters = code, centers
            item = next(iterators[index], None)
            if item is not None:
                heapq.heappush(heap, (*item, index))
    assert processed == sum(chunk["rows"] for chunk in manifest["chunks"]) == manifest["rows_to_chunks_not_unique_types"]
    for path, item in zip(paths, inputs, strict=True):
        assert sha(path) == item["sha256"]
    report = {
        "verified": True, "schema": "independent-small-order-complete-collar-slab-union-v1",
        "N": N, "B": B, "actual_native_exit_code": actual_code,
        "native_manifest_sha256": sha(manifestpath), "all_declared_slabs_fully_scanned": True,
        "all_rows_ordered_full_exposure_and_canonical_maps_checked": True,
        "complete_streaming_set_union": True,
        "input_rows_including_cross_slab_duplicates": processed,
        "unique_necessary_weak_graphs": unique, "cross_slab_duplicates_removed": processed-unique,
        "input_chunks": inputs, "catalog_file": catalogpath.name, "catalog_sha256": sha(catalogpath),
        "bindings_file": bindingspath.name, "bindings_sha256": sha(bindingspath),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    }
    publish(output / "VERIFIED.json", report)
    return report
