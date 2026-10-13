"""Negative controls for unpaid-domain accounting; no certificate edits."""
from pathlib import Path
from copy import deepcopy
import argparse
import gzip
import json
from replay_n25_endpoint_domain import replay
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    with gzip.open(args.tree, "rt", encoding="utf8") as stream:
        original = json.load(stream, object_pairs_hook=no_duplicate_keys)
    accepted = replay(original)
    assert accepted["verified"] and accepted["pending_boxes"] > 0
    mutations = []
    broken = deepcopy(original)
    broken["pending"].pop()
    mutations.append(("missing-unpaid-box", broken))
    broken = deepcopy(original)
    broken["pending"].append(deepcopy(broken["pending"][0]))
    mutations.append(("duplicate-unpaid-box", broken))
    broken = deepcopy(original)
    broken["pending"][0]["lo"][0] = "-1"
    mutations.append(("wrong-unpaid-domain", broken))
    broken = deepcopy(original)
    broken["complete"] = True
    mutations.append(("false-completion-claim", broken))
    broken = deepcopy(original)
    split = next(node for node in broken["nodes"] if node is not None and node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    mutations.append(("duplicate-child", broken))
    broken = deepcopy(original)
    broken["nodes"].append({"kind": "EMPTY"})
    mutations.append(("unreachable-extra-node", broken))
    broken = deepcopy(original)
    broken["input_sha256"]["trig_source"] = "0"*64
    mutations.append(("changed-input-source", broken))
    broken = deepcopy(original)
    leaf = next(node for node in broken["nodes"] if node is not None and node["kind"] == "DUAL")
    for key in ("l", "b", "f"):
        leaf["certificate"][key] = [0]*len(leaf["certificate"][key])
    mutations.append(("zero-force-certificate", broken))
    rejected = []
    for name, broken in mutations:
        try:
            replay(broken)
        except AssertionError:
            rejected.append(name)
        else:
            raise AssertionError(("invalid partition accepted", name))
    result = {"verified": True, "positive_controls": 1, "negative_controls_rejected": rejected,
              "tree_sha256": sha(args.tree), "immutable_inputs_modified": False,
              "replay_source_sha256": sha(ROOT / "replay_n25_endpoint_domain.py"),
              "source_sha256": sha(Path(__file__)),
              "scope": "partial-tree accounting controls, not whole-angle or global proof"}
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("Reduced-core partial-tree controls PASS:", len(rejected), "invalid claims rejected", flush=True)


if __name__ == "__main__":
    main()
