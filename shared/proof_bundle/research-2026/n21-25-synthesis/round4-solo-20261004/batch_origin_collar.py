"""Partition an accepted complete collar union into bounded exact-proof inputs."""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import canonical, validate
from n25_outer_search import read, publish

assert __debug__


def parent_gate(manifestpath, terminalpath, unionpath):
    manifest, terminal, union = map(read, (manifestpath, terminalpath, unionpath))
    assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
    assert terminal["manifest_sha256"] == sha(manifestpath)
    assert manifest["schema"] == "complete-cover-origin-collar-sorted-chunks-v1"
    assert manifest["N"] == 25 and manifest["B"] in (14, 15, 16, 17)
    assert manifest["origin_cover_screen"] and manifest["origin_cover_only_N25"]
    assert manifest["origin_cover_scope"] == "actual arbitrary disk covers only; not weak graph geometry"
    assert not manifest.get("seeded_fixed_collar_restriction", False), "restricted seed is not the complete family"
    assert manifest["origin_radius_upper_numerator"] == 239146311738101
    assert manifest["origin_radius_upper_denominator"] == 10**15
    assert manifest["complete_necessary_outer_search"] and not manifest["complete_full_triangulations"]
    assert union["verified"] and union["schema"] == "independent-complete-collar-slab-union-v1"
    assert union["actual_native_exit_code"] == 0 and union["native_manifest_sha256"] == sha(manifestpath)
    assert union["source_sha256"] == sha(ROOT / "merge_origin_collar_chunks.py")
    assert union["all_declared_slabs_fully_scanned"] and union["all_rows_ordered_and_canonical_checked"]
    assert union["complete_streaming_set_union"]
    assert (union["N"], union["B"]) == (manifest["N"], manifest["B"])
    assert len(manifest["chunks"]) == len(union["input_chunks"]) == manifest["chunk_count"]
    for index, (chunk, record) in enumerate(zip(manifest["chunks"], union["input_chunks"], strict=True)):
        path = (ROOT / chunk["file"]).resolve()
        assert path.parent == manifestpath.resolve().parent
        assert path.name == manifestpath.name+f".chunk-{index}.jsonl" == record["file"]
        assert sha(path) == record["sha256"] and chunk["rows"] == record["rows"]
    assert sum(chunk["rows"] for chunk in manifest["chunks"]) == union["input_rows_including_cross_slab_duplicates"]
    assert union["input_rows_including_cross_slab_duplicates"] == manifest["rows_to_chunks_not_unique_types"]
    assert union["cross_slab_duplicates_removed"] >= 0
    assert union["unique_necessary_weak_graphs"]+union["cross_slab_duplicates_removed"] == manifest["rows_to_chunks_not_unique_types"]
    catalogpath = unionpath.parent / union["catalog_file"]
    bindingpath = unionpath.parent / union["bindings_file"]
    assert catalogpath.parent == unionpath.parent and bindingpath.parent == unionpath.parent
    assert sha(catalogpath) == union["catalog_sha256"] and sha(bindingpath) == union["bindings_sha256"]
    return union, catalogpath, bindingpath


def identity(centers, B):
    return {"centers": list(range(centers)), "anchors": list(range(B)), "orientation": 1, "shift": 0}


def catalog_rows(path, N, B, total, check_canonical=False):
    previous, count = None, 0
    with path.open(encoding="ascii") as stream:
        header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
        assert header == {"schema": "complete-necessary-collar-union-jsonl-v1", "N": N, "B": B,
                          "members_are_weak_graphs_not_full_types": True}
        for index, line in enumerate(stream):
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert set(row) == {"id", "centers", "faces", "members"}
            assert row["id"] == index and row["members"] == 1
            centers, faces = row["centers"], row["faces"]
            assert type(centers) is int and B <= centers < N
            assert faces and faces == sorted(set(faces))
            assert all(type(mask) is int and 0 < mask < 1 << centers and mask.bit_count() == 3
                       and mask & ((1 << B)-1) for mask in faces)
            used = 0
            for mask in faces:
                used |= mask
            assert used == (1 << centers)-1
            code = tuple(faces)
            assert previous is None or previous < code
            previous = code
            if check_canonical:
                canonical_code, mapping = canonical(centers, B, faces, 1)
                assert canonical_code == code
                validate(centers, B, faces, mapping, faces)
            count += 1
            yield row
    assert count == total


def partition(manifestpath, terminalpath, unionpath, output, batch_size=128):
    assert 1 <= batch_size <= 4096 and not output.exists()
    union, catalogpath, parentbindings = parent_gate(manifestpath, terminalpath, unionpath)
    N, B, total = union["N"], union["B"], union["unique_necessary_weak_graphs"]
    assert 3 <= B <= N <= 25
    output.mkdir()
    descriptorpath = output / "BATCHES.jsonl"
    batches = count = 0
    block = []
    parent_hash = sha(catalogpath)
    with descriptorpath.open("x", encoding="ascii") as descriptors, parentbindings.open(encoding="ascii") as bindings:
        def flush_block():
            nonlocal batches
            if not block:
                return
            directory = output / f"batch-{batches:06}"
            directory.mkdir()
            start = block[0]["id"]
            group_rows = [{"id": j, "centers": r["centers"], "faces": r["faces"], "members": 1}
                          for j, r in enumerate(block)]
            bindingpath = directory / "bindings.jsonl"
            with bindingpath.open("x", encoding="ascii") as stream:
                for j, row in enumerate(block):
                    stream.write(json.dumps({"index": row["id"], "group": j, "map": identity(row["centers"], B)},
                                            separators=(",", ":"))+"\n")
            groupspath = directory / "GROUPS.json"
            publish(groupspath, {
                "N": N, "B": B, "threshold": 1, "groups": group_rows, "group_count": len(block),
                "selected_types": len(block), "catalog_types": total,
                "catalog_sha256": parent_hash, "bindings_file": bindingpath.name,
                "bindings_sha256": sha(bindingpath), "verified_embeddings_during_generation": True,
                "full_selected_catalog_scanned": False, "parent_groups_sha256": None,
                "parent_proof_sha256": None, "members_are_necessary_weak_graphs_not_full_types": True,
                "parent_union_report_sha256": sha(unionpath), "parent_catalog_first_index": start,
                "batch_number": batches, "source_sha256": sha(Path(__file__)),
                "global_optimality_proved": False,
            })
            descriptors.write(json.dumps({
                "batch": batches, "first": start, "count": len(block),
                "groups_file": groupspath.relative_to(output).as_posix(),
                "groups_sha256": sha(groupspath), "bindings_sha256": sha(bindingpath),
            }, separators=(",", ":"))+"\n")
            block.clear()
            batches += 1

        for row in catalog_rows(catalogpath, N, B, total, check_canonical=True):
            binding = json.loads(next(bindings), object_pairs_hook=no_duplicate_keys)
            assert binding == {"index": row["id"], "group": row["id"], "map": identity(row["centers"], B)}
            block.append(row)
            count += 1
            if len(block) == batch_size:
                flush_block()
        flush_block()
        assert not bindings.read().strip()
    assert count == total and sha(catalogpath) == parent_hash
    parent_gate(manifestpath, terminalpath, unionpath)
    result = {
        "verified": True, "schema": "complete-collar-union-bounded-partition-v1", "N": N, "B": B,
        "batch_size": batch_size, "batch_count": batches, "weak_graph_count": total,
        "all_parent_rows_canonical_checked": True, "all_parent_identity_bindings_checked": True,
        "complete_parent_union_partitioned_once": True,
        "descriptor_file": descriptorpath.name, "descriptor_sha256": sha(descriptorpath),
        "manifest_sha256": sha(manifestpath), "native_terminal_sha256": sha(terminalpath),
        "parent_union_report_sha256": sha(unionpath), "parent_catalog_sha256": parent_hash,
        "parent_bindings_sha256": sha(parentbindings), "source_sha256": sha(Path(__file__)),
        "parent_requires_actual_cover_origin_condition": True,
        "not_an_unqualified_geometric_weak_graph_family": True,
        "lower_bounds_not_paid_by_partition": True, "global_optimality_proved": False,
    }
    publish(output / "VERIFIED.json", result)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", type=Path, required=True)
    ap.add_argument("--terminal", type=Path, required=True)
    ap.add_argument("--union", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--batch-size", type=int, default=128)
    args = ap.parse_args()
    result = partition(*(p.resolve() for p in (args.manifest, args.terminal, args.union, args.output)),
                       args.batch_size)
    print("Complete bounded proof partition accepted:", result["weak_graph_count"],
          "weak graphs in", result["batch_count"], "batches", flush=True)


if __name__ == "__main__":
    main()
