"""Small rejection controls for the new exact partial-graph acceptance path."""
from pathlib import Path
import argparse
import copy
import gzip
import json
import subprocess
import sys
import partial_force_exact as exact

ROOT = Path(__file__).resolve().parent
assert __debug__


def rejected(action):
    try:
        action()
    except (AssertionError, ValueError, KeyError, RuntimeError):
        return True
    return False


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    assert not args.output.exists()
    constants = json.loads((ROOT.parent.parent / "n21-global/evidence/angle-constants.json").read_text())
    with gzip.open(ROOT / "evidence/B13-outer-trees/group-0001076.json.gz", "rt") as f:
        payload = json.load(f)
    nodes = payload["nodes"]
    def verify(tree, masks=None):
        return exact.verify(13, payload["partial_centers"], payload["faces"] if masks is None else masks,
                            tree, constants)
    assert verify(nodes)["verified"]
    bad = copy.deepcopy(nodes)
    leaf = next(n for n in bad if n["kind"] == "DUAL")
    for key in ("l", "b", "f"):
        leaf["certificate"][key] = [0] * len(leaf["certificate"][key])
    controls = {"zero_force_rejected": rejected(lambda: verify(bad))}
    bad_split = copy.deepcopy(nodes)
    split = next(n for n in bad_split if n["kind"] == "SPLIT")
    split["mid"] = "100"
    controls["outside_cut_rejected"] = rejected(lambda: verify(bad_split))
    bad_child = copy.deepcopy(nodes)
    split = next(n for n in bad_child if n["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    controls["duplicate_child_rejected"] = rejected(lambda: verify(bad_child))
    controls["unreachable_node_rejected"] = rejected(lambda: verify(nodes+[{"kind": "EMPTY"}]))
    controls["repeated_face_rejected"] = rejected(lambda: verify(nodes, payload["faces"]+[payload["faces"][0]]))
    check = subprocess.run([sys.executable, "-O", "-c",
                            "import sys;sys.path.insert(0,sys.argv[1]);import partial_force_exact",
                            str(ROOT)], capture_output=True, text=True)
    controls["disabled_assertions_rejected"] = check.returncode != 0 and "Assertions must be enabled" in check.stderr
    assert all(controls.values())
    args.output.write_text(json.dumps({"verified": True, "controls": controls,
                                      "not_a_proof_of_all_software_correctness": True}, indent=2), encoding="utf8")
    print("Exact partial-force rejection controls PASS", flush=True)


if __name__ == "__main__":
    main()
