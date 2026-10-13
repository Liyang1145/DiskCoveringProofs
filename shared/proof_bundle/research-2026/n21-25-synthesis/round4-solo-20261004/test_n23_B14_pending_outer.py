"""Real finite source/map selection and fixed-record decoding refusals."""
from pathlib import Path
from copy import deepcopy
from io import StringIO
import argparse
import json
import struct

from audit_n23_B14_pending_outer import (
    ROOT, HIGH, BinaryRows, adopt, decode_record, selected_groups,
    independent_mask, sha, publish)
from propose_n23_B14_pending_outer import select_pending
from group_catalog import canonical

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--catalog", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    catalogpath, output = args.catalog.resolve(), args.output.resolve()
    assert catalogpath.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    catalog = BinaryRows(catalogpath)
    iterator = iter(catalog.rows())
    rows = [next(iterator) for _ in range(256)]
    catalog.stream.close()
    source = dict(rows)
    groups, lookup, bindings = [], {}, []
    for index, row in rows:
        if independent_mask(row["faces"]) == (1 << 23)-1:
            continue
        code, mapping = canonical(23, 14, row["faces"], 1)
        if code not in lookup:
            lookup[code] = len(groups)
            groups.append({"id": len(groups), "centers": len(mapping["centers"]),
                           "faces": list(code), "members": 0})
        gid = lookup[code]
        groups[gid]["members"] += 1
        bindings.append({"index": index, "group": gid, "map": mapping})
    assert len(groups) > 1
    oldpaid = {0}
    pending = [row["index"] for row in bindings if row["group"] not in oldpaid]
    newgid = next(g["id"] for g in groups if g["id"] not in oldpaid)
    newpaid = {newgid: "fixture-identifier-not-a-mathematical-proof"}

    def invoke(current=pending, binds=bindings, graphgroups=groups, new=newpaid,
               at=source.__getitem__, expected=len(pending)):
        ledger, residual = StringIO(), StringIO()
        return adopt(
            iter(current), iter(json.dumps(row)+"\n" for row in binds), at,
            graphgroups, oldpaid, new, 256, expected, ledger, residual)

    counts = invoke()
    assert counts["new-strict-full-outer-type"] == groups[newgid]["members"]
    assert sum(counts.values()) == len(pending)
    cases = [
        ("missing-actual-pending-index", {"current": pending[:-1]}),
        ("duplicate-current-pending-index", {"current": pending[:1]+pending}),
        ("reversed-current-pending", {"current": list(reversed(pending))}),
        ("extra-outside-source-pending", {"current": pending+[256]}),
        ("wrong-current-pending-count", {"expected": len(pending)+1}),
        ("missing-actual-binding", {"binds": bindings[:-1]}),
        ("duplicate-actual-binding", {"binds": bindings[:1]+bindings}),
        ("extra-actual-binding", {"binds": bindings+[deepcopy(bindings[-1])]}),
        ("already-paid-group-reproposed", {"new": {0: "invalid"}}),
    ]
    oldindex = next(row["index"] for row in bindings if row["group"] in oldpaid)
    cases.append(("old-paid-type-reintroduced", {"current": sorted(pending+[oldindex])}))
    changed = deepcopy(groups)
    changed[newgid]["members"] += 1
    cases.append(("wrong-group-member-count", {"graphgroups": changed}))
    target = next(i for i, row in enumerate(bindings) if row["group"] == newgid)
    for label, field, value in (
        ("wrong-boundary-shift", "shift", (bindings[target]["map"]["shift"]+1) % 14),
        ("anchor-collision", "anchors", [0]*14),
        ("center-collision", "centers", [0]*len(bindings[target]["map"]["centers"])),
    ):
        changed = deepcopy(bindings)
        changed[target]["map"][field] = value
        cases.append((label, {"binds": changed}))
    changed = deepcopy(groups)
    single = next(mask for mask in changed[newgid]["faces"]
                  if (mask & ((1 << 14)-1)).bit_count() == 1)
    changed[newgid]["faces"].remove(single)
    cases.append(("one-boundary-face-omitted", {"graphgroups": changed}))
    changedsource = deepcopy(source)
    changedsource[pending[0]]["faces"].pop()
    cases.append(("actual-original-complete-face-omitted", {"at": changedsource.__getitem__}))
    rejected = []
    for label, kwargs in cases:
        try:
            invoke(**kwargs)
        except (AssertionError, ValueError, IndexError, KeyError, StopIteration):
            rejected.append(label)
        else:
            raise AssertionError(("bad actual current-residual increment accepted", label))
    data = {"N": 23, "B": 14, "threshold": 1, "group_count": len(groups), "groups": groups,
            "selected_types": len(bindings)}
    receipt = {
        "N": 23, "B": 14, "requested_groups_complete": True,
        "outcomes": [{"group": g["id"], "status": "excluded" if g["id"] in oldpaid else "pending"}
                     for g in groups],
        "excluded_groups": 1, "pending_groups": len(groups)-1,
        "catalog_members_excluded": groups[0]["members"],
    }
    selected, paid = selected_groups(data, receipt)
    proposed, proposalpaid = select_pending(data, receipt)
    assert selected == [g["id"] for g in proposed] and paid == proposalpaid == oldpaid
    for label, change in (
        ("omitted-old-outcome", lambda r: r["outcomes"].pop()),
        ("duplicate-old-outcome", lambda r: r["outcomes"].append(deepcopy(r["outcomes"][0]))),
        ("wrong-old-positive-count", lambda r: r.update(excluded_groups=2)),
        ("wrong-old-associated-count", lambda r: r.update(catalog_members_excluded=0)),
    ):
        changed = deepcopy(receipt)
        change(changed)
        for checker in (selected_groups, select_pending):
            try:
                checker(data, changed)
            except (AssertionError, ValueError, IndexError):
                pass
            else:
                raise AssertionError(("invalid whole-group selection accepted", label, checker.__name__))
        rejected.append(label)
    row = rows[0][1]
    values = [row["stabilizer"], *row["faces"]]
    block = struct.pack("<"+"I"*31, *values)
    assert decode_record(block, 23, 14) == row
    recordcases = [("truncated-fixed-record", block[:-1])]
    for label, offset, value in (
        ("zero-stabilizer", 0, 0),
        ("duplicate-original-face", 2, values[1]),
        ("non-triangle-original-face", 1, 1),
        ("outside-N-original-face", 30, (1 << 23)+3),
    ):
        changed = list(values)
        changed[offset] = value
        recordcases.append((label, struct.pack("<"+"I"*31, *changed)))
    for label, changedblock in recordcases:
        try:
            decode_record(changedblock, 23, 14)
        except (AssertionError, ValueError, struct.error):
            rejected.append(label)
        else:
            raise AssertionError(("invalid original fixed record accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-current-pending-outer-increment-controls-v1",
        "real_original_full_source_fixture_types": 256,
        "whole_group_selection_matches_current_residual_and_old_payments_stay_disjoint": True,
        "actual_full_exposed_maps_and_original_fixed_records_checked": True,
        "negative_controls_rejected": rejected,
        "fixture_tree_identifiers_not_mathematical_proofs": True,
        "audit_source_sha256": sha(ROOT / "audit_n23_B14_pending_outer.py"),
        "proposal_source_sha256": sha(ROOT / "propose_n23_B14_pending_outer.py"),
        "frozen_mapping_checker_sha256": sha(HIGH / "audit_streamed_hierarchy.py"),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("N23/B14 actual current-residual increment controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
