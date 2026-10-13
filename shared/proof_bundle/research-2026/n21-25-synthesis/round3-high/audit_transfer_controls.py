"""Negative/positive controls for independent centre and anchor transfers."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
from audit_streamed_hierarchy import check_map
from stream_catalog import sha

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    N, B = 6, 4
    full = {sum(1 << v for v in face) for face in
            ((0, 1, 4), (1, 2, 4), (2, 3, 5), (0, 3, 5), (0, 4, 5), (2, 4, 5))}
    mapping = {"centers": [2, 1, 0, 3, 5, 4], "anchors": [1, 0, 3, 2],
               "orientation": -1, "shift": 2}
    inverse = {v: i for i, v in enumerate(mapping["centers"])}
    retained = {mask for mask in full if (mask & 15).bit_count() >= 2}
    code = sorted(sum(1 << inverse[v] for v in range(N) if mask >> v & 1)
                  for mask in retained)
    group = {"centers": N, "faces": code}
    check_map(N, B, group, mapping, full, 2)
    identity = {"centers": list(range(N)), "anchors": list(range(B)),
                "orientation": 1, "shift": 0}
    check_map(N, B, {"centers": N, "faces": sorted(full)}, identity, full, 0)
    controls = []

    def reject(name, g, m, f=full, threshold=2):
        try:
            check_map(N, B, g, m, f, threshold)
        except (AssertionError, KeyError, TypeError):
            controls.append(name)
        else:
            raise AssertionError("Invalid transfer accepted: "+name)

    bad = deepcopy(mapping)
    bad["anchors"] = [2, 1, 0, 3]
    reject("reflection_missing_anchor_offset", group, bad)
    bad = deepcopy(mapping)
    bad["centers"][-1] = bad["centers"][-2]
    reject("noninjective_internal_centres", group, bad)
    bad = deepcopy(mapping)
    bad["orientation"] = 1
    reject("wrong_boundary_orientation", group, bad)
    bad = deepcopy(mapping)
    bad["shift"] = 1
    reject("wrong_boundary_shift", group, bad)
    bad = deepcopy(mapping)
    bad["centers"][1] = True
    reject("boolean_centre_label", group, bad)
    bad = deepcopy(group)
    bad["faces"] = code[:-1]
    reject("missing_retained_face", bad, mapping)
    bad = deepcopy(group)
    bad["faces"] = code+[code[-1]]
    reject("duplicate_face", bad, mapping)
    bad = deepcopy(group)
    bad["faces"] = sorted(code+[1 << N | 3])
    reject("out_of_range_face", bad, mapping)
    bad = deepcopy(group)
    bad["centers"] = N-1
    reject("incorrect_group_centre_count", bad, mapping)
    reject("image_face_absent_from_full_type", group, mapping, full-{min(retained)})
    reject("full_layer_incomplete", group, mapping, threshold=0)
    report = {"verified": True, "positive_controls": 2,
              "negative_controls_rejected": controls,
              "auditor_sha256": sha(Path(__file__).with_name("audit_streamed_hierarchy.py")),
              "source_sha256": sha(Path(__file__)), "global_optimality_proved": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Independent transfer controls PASS:", len(controls), "invalid cases rejected", flush=True)


if __name__ == "__main__":
    main()
