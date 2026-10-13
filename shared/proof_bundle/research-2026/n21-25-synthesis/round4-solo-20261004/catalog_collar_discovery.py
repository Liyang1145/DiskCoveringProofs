"""Prepare an explicitly incomplete discovery set for the frozen group checker."""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from group_catalog import canonical, validate
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    data = json.loads(args.snapshot.read_text(encoding="utf8"),
                      object_pairs_hook=no_duplicate_keys)
    assert data["schema"] == "incomplete-collar-discovery-v1"
    assert data["complete_necessary_outer_search"] is False
    assert data["global_optimality_proved"] is False
    assert data["N"] == 25 and data["B"] == 14
    assert data["weak_graph_count"] == len(data["weak_graphs"])
    assert data["calls"] == data["node_limit"] > 0
    assert data["production_exit_code"] != 0
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    output.mkdir()
    groups = []
    previous = None
    with (output / "bindings.jsonl").open("x", encoding="utf8") as ledger:
        for index, row in enumerate(data["weak_graphs"]):
            centers, faces = row["centers"], row["faces"]
            assert 14 <= centers <= 25 and faces == sorted(set(faces))
            code, mapping = canonical(centers, 14, faces, 1)
            assert list(code) == faces and len(mapping["centers"]) == centers
            assert previous is None or previous < code
            previous = code
            identity = {"centers": list(range(centers)), "anchors": list(range(14)),
                        "orientation": 1, "shift": 0}
            validate(centers, 14, faces, identity, faces)
            groups.append({"id": index, "centers": centers, "faces": faces, "members": 1})
            ledger.write(json.dumps({"index": index, "group": index, "map": identity},
                                    separators=(",", ":"))+"\n")
    (output / "GROUPS.json").write_text(json.dumps({
        "N": 25, "B": 14, "threshold": 1,
        "groups": groups, "group_count": len(groups),
        "selected_types": len(groups), "catalog_types": len(groups),
        "catalog_sha256": sha(args.snapshot),
        "bindings_file": "bindings.jsonl",
        "bindings_sha256": sha(output / "bindings.jsonl"),
        "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": False,
        "parent_groups_sha256": None, "parent_proof_sha256": None,
        "members_are_incomplete_discovery_graphs_not_actual_cover_types": True,
        "complete_family_coverage": False,
        "not_a_complete_family": True,
        "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    print("Incomplete discovery groups prepared:", len(groups),
          "; no full-family coverage claim", flush=True)


if __name__ == "__main__":
    main()
