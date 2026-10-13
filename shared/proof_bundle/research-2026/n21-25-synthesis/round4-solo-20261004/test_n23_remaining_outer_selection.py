"""Selection/attainment controls only; no claim of type payment."""
from pathlib import Path
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish
from group_catalog import canonical
from probe_n23_remaining_outer import select_remaining

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    corepath, output = args.core.resolve(), args.output.resolve()
    assert corepath.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    core = read(corepath)
    masks = sorted(sum(1 << v for v in face) for face in core["all_faces"])
    code, _ = canonical(23, 15, masks, 1)
    groups = [{"id": 0, "faces": list(code), "centers": 22, "members": 1}]
    previous = [{"group": 0, "status": "pending"}]
    selected, known = select_remaining(groups, previous, core)
    assert known == 0 and selected == groups
    rejected = []
    cases = []
    for label, key, value in (("wrong-core-N", "N", 25), ("wrong-core-B", "B", 16)):
        changed = deepcopy(core)
        changed[key] = value
        cases.append((label, groups, previous, changed))
    changed = deepcopy(groups)
    changed[0]["id"] = 1
    cases.append(("wrong-original-group-id", changed, previous, core))
    changed = deepcopy(previous)
    changed[0]["group"] = 1
    cases.append(("wrong-original-outcome-id", groups, changed, core))
    changed = deepcopy(previous)
    changed[0]["status"] = "success"
    cases.append(("unrecognized-outcome-status", groups, changed, core))
    changed = deepcopy(previous)
    changed[0]["status"] = "excluded"
    cases.append(("known-attainer-incorrectly-previously-paid", groups, changed, core))
    changed = deepcopy(groups)
    changed[0]["centers"] = 21
    cases.append(("declared-centers-smaller-than-actual", changed, previous, core))
    cases.append(("duplicate-attaining-group", groups+[dict(groups[0], id=1)],
                  previous+[dict(previous[0], group=1)], core))
    # Add corrupt nonattaining pending groups, retaining the genuine control.
    for label, faces, centers in (
        ("two-center-face-not-triangle", [3], 15),
        ("pure-internal-face-incorrectly-exposed", [(1 << 15) | (1 << 16) | (1 << 17)], 18),
        ("unseen-declared-center", [7], 22),
    ):
        bad = {"id": 1, "faces": faces, "centers": centers, "members": 1}
        cases.append((label, groups+[bad], previous+[{"group": 1, "status": "pending"}], core))
    for label, testgroups, testprevious, testcore in cases:
        try:
            select_remaining(testgroups, testprevious, testcore)
        except (AssertionError, ValueError, IndexError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("bad residual proposal selection accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-remaining-outer-proposal-selection-controls-v1",
        "known_attaining_group_retained": True, "negative_controls_rejected": rejected,
        "core_sha256": sha(corepath), "source_sha256": sha(Path(__file__)),
        "proposal_source_sha256": sha(ROOT / "probe_n23_remaining_outer.py"),
        "functional_selection_fixtures_not_source_type_payments": True,
        "global_optimality_proved": False,
    })
    print("N23 remaining-outer selection controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
