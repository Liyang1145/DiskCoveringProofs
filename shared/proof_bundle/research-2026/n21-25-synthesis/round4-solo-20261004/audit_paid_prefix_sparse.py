"""Independent sparse-prefix transfer audit, including rejecting bad maps.

Only standard-library exact checking and frozen label-map checks are imported.
The sparsification proposer and numerical optimizer are never imported.
"""
from pathlib import Path
from collections import Counter
from copy import deepcopy
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import canonical, validate
from family_sparse_gate import sparse_library_gate
from n25_outer_search import read, publish, bind, unchanged

assert __debug__


def jsonl(path):
    with path.open(encoding="utf8") as stream:
        return [json.loads(line, object_pairs_hook=no_duplicate_keys) for line in stream]


def audit_transfers(parents, data, entries, bindings):
    B = data["B"]
    groups = data["groups"]
    assert len(entries) == len(bindings) == data["selected_types"] == len(parents)
    assert [g["id"] for g in groups] == list(range(data["group_count"]))
    assert [row["index"] for row in entries] == list(range(len(parents)))
    assert [row["index"] for row in bindings] == list(range(len(parents)))
    counts = Counter()
    original_faces = reduced_faces = 0
    for index, (parent, row, binding) in enumerate(zip(parents, entries, bindings, strict=True)):
        assert parent["id"] == row["parent_prefix_group"] == index
        assert row["parent_centers"] == parent["centers"]
        assert row["parent_faces"] == parent["faces"]
        assert row["group"] == binding["group"] and row["map"] == binding["map"]
        assert type(row["group"]) is int and 0 <= row["group"] < len(groups)
        group = groups[row["group"]]
        retained = row["remaining_faces_in_parent_labels"]
        assert retained == sorted(set(retained)) and retained
        assert set(retained) <= set(parent["faces"])
        assert len(row["map"]["centers"]) == group["centers"]
        assert len(row["map"]["anchors"]) == B
        validate(parent["centers"], B, group["faces"], row["map"], parent["faces"])
        images = sorted(sum(1 << row["map"]["centers"][v]
                            for v in range(group["centers"]) if mask >> v & 1)
                        for mask in group["faces"])
        assert images == retained
        code, mapping = canonical(parent["centers"], B, retained, 1)
        assert list(code) == group["faces"] and len(mapping["centers"]) == group["centers"]
        counts[group["id"]] += 1
        original_faces += len(parent["faces"])
        reduced_faces += len(group["faces"])
    assert all(counts[g["id"]] == g["members"] for g in groups)
    return original_faces, reduced_faces


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefix", type=Path, required=True)
    ap.add_argument("--sparse", type=Path, required=True)
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    for name in ("prefix", "sparse", "library", "output"):
        path = getattr(args, name).resolve()
        assert path.is_relative_to(ROOT)
        setattr(args, name, path)
    assert not args.output.exists()
    constants, library, table, files = sparse_library_gate(args.library)
    data = read(args.sparse / "GROUPS.json")
    receipt = read(args.sparse / "SUMMARY.json")
    replay = read(args.sparse / "EXACT-REPLAY.json")
    parents = read(args.prefix / "GROUPS.json")
    verified = read(args.prefix / "VERIFIED.json")
    assert data["N"] == parents["N"] == 25
    assert data["B"] == parents["B"] == library["B"]
    assert data["threshold"] == parents["threshold"] == 1
    assert data["not_a_complete_family"] and not data["full_selected_catalog_scanned"]
    assert verified["verified"] and verified["not_a_complete_competitor_family_or_union"]
    assert verified["groups_sha256"] == sha(args.prefix / "GROUPS.json")
    assert verified["receipt_sha256"] == sha(args.prefix / "PROPOSALS/SUMMARY.json")
    assert verified["exact_replay_sha256"] == sha(args.prefix / "EXACT-REPLAY.json")
    assert receipt["source_prefix_groups_sha256"] == data["catalog_sha256"] == sha(args.prefix / "GROUPS.json")
    assert receipt["source_prefix_relative_to_round4"] == args.prefix.relative_to(ROOT).as_posix()
    assert receipt["groups_sha256"] == replay["groups_sha256"] == sha(args.sparse / "GROUPS.json")
    assert replay["verified"] and replay["pending_groups"] == 0
    assert receipt["pending_groups"] == 0
    assert data["group_count"] == replay["exact_groups_replayed"] == library["obstacle_count"]
    assert len(parents["groups"]) == data["selected_types"]
    assert receipt["parent_maps_sha256"] == sha(args.sparse / "parent-maps.jsonl")
    assert data["bindings_sha256"] == sha(args.sparse / data["bindings_file"])
    assert [(g["id"], g["centers"], g["faces"]) for g in data["groups"]] == [
        (o["id"], o["centers"], o["faces"]) for o in library["obstacles"]]
    for relative, digest in receipt["source_files"].items():
        path = (ROOT.parent / relative).resolve()
        assert path.is_relative_to(ROOT.parent) and sha(path) == digest
        bind(files, path)
    entries = jsonl(args.sparse / "parent-maps.jsonl")
    bindings = jsonl(args.sparse / data["bindings_file"])
    before, after = audit_transfers(parents["groups"], data, entries, bindings)
    assert before == receipt["parent_face_count"] and after == receipt["reduced_face_count"]
    assert receipt["accepted_deletions"] == before-after
    source_slab = ROOT / parents["source_slab_relative_to_workspace"]
    assert sha(source_slab) == verified["source_slab_sha256"]
    with source_slab.open(encoding="ascii") as stream:
        header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
        assert header["not_a_complete_search"] and header["N"] == 25 and header["B"] == data["B"]
        for parent in parents["groups"]:
            row = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
            assert (row["centers"], row["faces"]) == (parent["centers"], parent["faces"])
    rejected = []
    for label in ("missing-parent", "duplicate-parent", "wrong-parent-group",
                  "wrong-anchor-offset", "center-collision", "missing-retained-face",
                  "changed-parent-faces", "changed-member-count"):
        bad_entries, bad_bindings, bad_data = deepcopy(entries), deepcopy(bindings), deepcopy(data)
        if label == "missing-parent":
            bad_entries.pop()
            bad_bindings.pop()
        elif label == "duplicate-parent":
            bad_entries[-1], bad_bindings[-1] = deepcopy(bad_entries[0]), deepcopy(bad_bindings[0])
        elif label == "wrong-parent-group":
            bad_entries[0]["parent_prefix_group"] = 1
        elif label == "wrong-anchor-offset":
            for rows in (bad_entries, bad_bindings):
                rows[0]["map"]["anchors"][0] = (rows[0]["map"]["anchors"][0]+1) % data["B"]
        elif label == "center-collision":
            for rows in (bad_entries, bad_bindings):
                rows[0]["map"]["centers"][1] = rows[0]["map"]["centers"][0]
        elif label == "missing-retained-face":
            bad_entries[0]["remaining_faces_in_parent_labels"].pop()
        elif label == "changed-parent-faces":
            bad_entries[0]["parent_faces"].pop()
        else:
            bad_data["groups"][0]["members"] += 1
        try:
            audit_transfers(parents["groups"], bad_data, bad_entries, bad_bindings)
        except (AssertionError, IndexError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("bad sparse-prefix transfer accepted", label))
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath",
                                                   "sparsify_verified_group_prefix", "probe_groups"))
    for path in (Path(__file__), args.library, args.sparse / "GROUPS.json",
                 args.sparse / "SUMMARY.json", args.sparse / "EXACT-REPLAY.json",
                 args.sparse / "parent-maps.jsonl", args.sparse / data["bindings_file"],
                 HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    publish(args.output, {
        "verified": True, "schema": "independent-paid-prefix-sparse-transfers-v1",
        "N": 25, "B": data["B"], "finite_parent_count": len(parents["groups"]),
        "standalone_strict_obstacles": library["obstacle_count"],
        "parent_face_count": before, "retained_face_count": after,
        "all_parent_center_anchor_and_face_injections_checked": True,
        "all_source_slab_prefix_rows_rechecked": True,
        "all_strict_sparse_trees_fresh_exact_replayed": True,
        "no_optimizer_or_sparsification_proposer_imported": True,
        "negative_controls_rejected": rejected,
        "library_sha256": sha(args.library), "source_sha256": sha(Path(__file__)),
        "files_relative_to_workspace": files,
        "not_a_complete_competitor_family_or_union": True,
        "global_optimality_proved": False,
    })
    print("Independent finite-prefix sparse transfers PASS:",
          len(parents["groups"]), "parents;", library["obstacle_count"],
          "strict obstacles;", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
