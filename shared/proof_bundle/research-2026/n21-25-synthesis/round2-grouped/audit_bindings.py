"""Independent explicit-embedding and disjoint hierarchy membership audit.

No canonicalization/search routines are imported.  Each face and each boundary
rod is transferred directly using the supplied injective maps.  Certificates
are paid only through content-bound standalone replay receipts.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PARENT = ROOT.parent
assert __debug__


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf8"))


def bits(mask):
    return [i for i in range(mask.bit_length()) if (mask >> i) & 1]


def check_map(B, code, center, anchor, faces):
    assert B <= len(center) <= 21
    assert all(type(v) is int and 0 <= v < 21 for v in center)
    assert len(set(center)) == len(center)
    assert sorted(center[:B]) == list(range(B))
    assert all(v >= B for v in center[B:])
    assert sorted(anchor) == list(range(B))
    assert all(type(v) is int for v in anchor)
    sign = next((s for s in (1, -1) if
                 all(center[j] == (center[0] + s * j) % B for j in range(B))), None)
    assert sign is not None
    assert anchor == [(center[0] + sign * j - (sign < 0)) % B for j in range(B)]
    for i in range(B):
        assert {center[i], center[(i+1) % B]} == {anchor[i], (anchor[i]+1) % B}
    images = set()
    for mask in code:
        assert type(mask) is int and mask > 0 and mask.bit_count() == 3
        vertices = bits(mask)
        assert max(vertices) < len(center)
        image = sum(1 << center[v] for v in vertices)
        assert image in faces
        images.add(image)
    assert len(images) == len(code)
    return images


def audit_stage(B, name, catalog, expected, paid):
    path = ROOT / "evidence" / name / "GROUPS.json"
    data = read(path)
    assert data["B"] == B and data["N"] == 21
    assert data["catalog_sha256"] == catalog["sha"]
    assert data["catalog_types"] == len(catalog["rows"])
    assert data["scanned_types"] == len(data["bindings"])
    assert data["group_count"] == len(data["groups"])
    assert [g["id"] for g in data["groups"]] == list(range(data["group_count"]))
    all_indices = set()
    counts = Counter()
    for k, binding in enumerate(data["bindings"]):
        i, gid = binding["index"], binding["group"]
        assert type(i) is int and i in expected and i not in all_indices
        assert type(gid) is int and 0 <= gid < data["group_count"]
        all_indices.add(i)
        counts[gid] += 1
        group = data["groups"][gid]
        assert group["centers"] == len(binding["map"]["centers"])
        faces = set(catalog["rows"][i]["faces"])
        images = check_map(B, group["faces"], binding["map"]["centers"],
                           binding["map"]["anchors"], faces)
        threshold = data["minimum_boundary_vertices_in_retained_faces"]
        retained = {f for f in faces if (f & ((1 << B)-1)).bit_count() >= threshold}
        assert images == retained
        if k and k % 100000 == 0:
            print("B", B, name, "maps checked", k, flush=True)
    assert all_indices == expected
    assert set(counts) == set(range(data["group_count"]))
    if paid is None:
        excluded = set()
    else:
        receipt = read(paid[0])
        replay = read(paid[1])
        assert replay["verified"] and replay["B"] == B and replay["N"] == 21
        assert replay["groups_sha256"] == receipt["groups_sha256"] == sha(path)
        assert replay["combined_sha256"] == sha(paid[0])
        outcomes = receipt["outcomes"]
        assert len(outcomes) == data["group_count"]
        assert sorted(r["group"] for r in outcomes) == list(range(data["group_count"]))
        excluded_groups = {r["group"] for r in outcomes if r["status"] == "excluded"}
        assert len(excluded_groups) == replay["excluded_groups_replayed"]
        excluded = {b["index"] for b in data["bindings"] if b["group"] in excluded_groups}
        assert len(excluded) == replay["catalog_member_exclusions_replayed"]
    report = {"groups_sha256": sha(path), "maps_checked": len(all_indices),
              "excluded_types_with_replayed_certificates": len(excluded),
              "remaining_types": len(expected - excluded)}
    if paid is not None:
        report["replay_sha256"] = sha(paid[1])
    return expected - excluded, report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--B", type=int, choices=(13, 14), required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--full-combined", type=Path)
    parser.add_argument("--full-replay", type=Path)
    args = parser.parse_args()
    assert not args.output.exists()
    B = args.B
    catpath = PARENT / "evidence" / "n21-peeling-round5-B13-B14" / f"N21-B{B}-dfs.json"
    data = read(catpath)
    assert data["complete"] and data["screen"] and data["N"] == 21 and data["B"] == B
    catalog = {"sha": sha(catpath), "rows": data["survivors"]}
    assert data["orbits"] == len(catalog["rows"])
    remaining = set(range(len(catalog["rows"])))
    stages = []
    remaining, info = audit_stage(B, f"B{B}-pair-full", catalog, remaining, (
        ROOT / "evidence" / f"B{B}-pair-root-force" / "SUMMARY.json",
        ROOT / "evidence" / f"B{B}-pair-replay-standalone.json"))
    stages.append(info)
    core_indices = set()
    if B == 13:
        corepath = PARENT / "evidence" / "n21-core-embedding-map.json"
        core = read(corepath)
        assert core["catalog_sha256"] == catalog["sha"]
        definition = read(PARENT.parent / "n21-global" / "evidence" / "core-system.json")
        masks = [sum(1 << v for v in face) for face in definition["active_faces"]]
        for row in core["explicit_maps"]:
            i = row["index"]
            assert i in remaining and i not in core_indices
            core_indices.add(i)
            images = check_map(B, masks, row["center_map"], row["anchor_map"],
                               set(catalog["rows"][i]["faces"]))
            assert images == set(row["active_face_masks"])
        assert len(core_indices) == 30
        remaining -= core_indices
    remaining, info = audit_stage(B, f"B{B}-outer-refinement", catalog, remaining, (
        ROOT / "evidence" / f"B{B}-outer-combined.json",
        ROOT / "evidence" / f"B{B}-replay-standalone.json"))
    stages.append(info)
    full_paid = None
    if args.full_combined is not None:
        assert args.full_replay is not None
        full_paid = (args.full_combined, args.full_replay)
    remaining, info = audit_stage(B, f"B{B}-full-refinement", catalog, remaining, full_paid)
    stages.append(info)
    report = {
        "verified": True, "N": 21, "B": B,
        "catalog_sha256": catalog["sha"],
        "catalog_types": len(catalog["rows"]),
        "stages": stages, "core_embedding_maps_checked": len(core_indices),
        "pending_catalog_indices": sorted(remaining),
        "strict_exclusion_types": len(catalog["rows"]) - len(remaining) - len(core_indices),
        "core_lower_bound_cases": len(core_indices),
        "coverage_partition_complete": not remaining,
        "core_angle_tree_replayed_here": False,
        "arbitrary_cover_to_catalog_proved_here": False,
        "global_optimality_proved": False,
        "source_sha256": sha(Path(__file__)),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("B", B, "explicit embedding hierarchy PASS; pending", len(remaining), flush=True)


if __name__ == "__main__":
    main()
