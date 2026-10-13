"""Real-source partition/map refusals and a real positive-tree identity control."""
from pathlib import Path
from copy import deepcopy
from io import StringIO
import argparse
import gzip
import json

from audit_n23_B14_full_outer_payment import (
    ROOT, HIGH, BinaryRows, independent_mask, scan, check_tree, sha, read, publish, exact)
from group_catalog import canonical

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("catalog", "groups", "positive-tree", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    catalogpath, groupspath, treepath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("catalog", "groups", "positive-tree", "output"))
    assert all(path.is_relative_to(ROOT) for path in (catalogpath, groupspath, treepath, output))
    assert not output.exists()
    catalog = BinaryRows(catalogpath)
    iterator = iter(catalog.rows())
    rows = [next(iterator) for _ in range(32)]
    catalog.stream.close()
    eligible = [index for index, row in rows if independent_mask(row["faces"]) != (1 << 23)-1]
    selected, prior = eligible[::2], eligible[1::2]
    assert len(selected) > 2 and prior
    groups, lookup, bindings = [], {}, []
    for index in selected:
        code, mapping = canonical(23, 14, rows[index][1]["faces"], 1)
        if code not in lookup:
            lookup[code] = len(groups)
            groups.append({"id": len(groups), "centers": len(mapping["centers"]),
                           "faces": list(code), "members": 0})
        gid = lookup[code]
        groups[gid]["members"] += 1
        bindings.append({"index": index, "group": gid, "map": mapping})
    pairs = [{"index": index, "group": 0, "tree_sha256": "0"*64} for index in prior]
    paid = {0: "fixture-identifier-not-a-geometric-certificate"}

    def invoke(source=rows, oldpairs=pairs, pending=selected, binds=bindings,
               graphgroups=groups, total=32, expected=len(selected)):
        ledger, residual = StringIO(), StringIO()
        counts = scan(
            iter(source), iter(oldpairs), iter(pending),
            StringIO("".join(json.dumps(row)+"\n" for row in binds)),
            graphgroups, paid, total, expected, ledger, residual)
        return counts, ledger.getvalue(), residual.getvalue()

    counts, ledger, residual = invoke()
    assert counts["new-strict-full-outer-type"] == groups[0]["members"]
    assert counts["unchanged-strict-pair-type"] == len(prior)
    assert counts["new-strict-full-outer-type"]+counts.get("pending", 0) == len(selected)
    cases = [
        ("missing-current-binding", {"binds": bindings[:-1]}),
        ("duplicate-current-binding", {"binds": bindings[:1]+bindings}),
        ("extra-current-binding", {"binds": bindings+[deepcopy(bindings[-1])]}),
        ("missing-current-pending", {"pending": selected[:-1]}),
        ("duplicate-current-pending", {"pending": selected[:1]+selected}),
        ("reversed-current-pending", {"pending": list(reversed(selected))}),
        ("already-pair-paid-reintroduced", {"pending": sorted(selected+[prior[0]])}),
        ("missing-old-pair-payment", {"oldpairs": pairs[:-1]}),
        ("duplicate-old-pair-payment", {"oldpairs": pairs[:1]+pairs}),
        ("source-truncated", {"source": rows[:-1]}),
        ("source-index-gap", {"source": rows[:10]+rows[11:]}),
        ("wrong-current-pending-count", {"expected": len(selected)+1}),
        ("pending-outside-original-source", {"pending": selected+[32]}),
    ]
    obstruction = next(index for index, row in rows if independent_mask(row["faces"]) == (1 << 23)-1)
    cases.append(("already-origin-paid-reintroduced", {
        "pending": sorted(selected+[obstruction]), "expected": len(selected)+1}))
    changed = deepcopy(rows)
    changed[selected[0]][1]["faces"].pop()
    cases.append(("original-complete-face-omitted", {"source": changed}))
    for label, field, value in (
        ("wrong-boundary-shift", "shift", (bindings[0]["map"]["shift"]+1) % 14),
        ("wrong-reflection-anchor", "orientation", -bindings[0]["map"]["orientation"]),
        ("anchor-collision", "anchors", [0]*14),
        ("center-collision", "centers", [0]*len(bindings[0]["map"]["centers"])),
    ):
        changed = deepcopy(bindings)
        changed[0]["map"][field] = value
        cases.append((label, {"binds": changed}))
    changed = deepcopy(groups)
    changed[0]["members"] += 1
    cases.append(("wrong-group-member-count", {"graphgroups": changed}))
    changed = deepcopy(groups)
    changed[0]["centers"] -= 1
    cases.append(("wrong-exposed-center-count", {"graphgroups": changed}))
    changed = deepcopy(groups)
    single = next(mask for mask in changed[0]["faces"] if (mask & ((1 << 14)-1)).bit_count() == 1)
    changed[0]["faces"].remove(single)
    cases.append(("one-boundary-face-omitted-cannot-use-pair-map", {"graphgroups": changed}))
    rejected = []
    for label, kwargs in cases:
        try:
            invoke(**kwargs)
        except (AssertionError, ValueError, IndexError, StopIteration):
            rejected.append(label)
        else:
            raise AssertionError(("invalid current full-outer payment selection accepted", label))

    data = read(groupspath)
    with gzip.open(treepath, "rt", encoding="utf8") as stream:
        tree = json.load(stream)
    group = data["groups"][0]
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constants_path)
    actual = exact.verify(14, group["centers"], group["faces"], tree["nodes"], constants)
    outcome = {**actual, "members": group["members"]}
    check_tree(tree, group, outcome, sha(groupspath), constants, sha(constants_path))
    treecases = []
    for label, field, value in (
        ("tree-wrong-order", "N", 24),
        ("tree-wrong-boundary", "B", 15),
        ("tree-wrong-centers", "partial_centers", group["centers"]+1),
        ("tree-omitted-full-exposed-face", "faces", group["faces"][:-1]),
        ("tree-wrong-groups-binding", "groups_sha256", "f"*64),
        ("tree-wrong-constants-binding", "constants_sha256", "f"*64),
        ("tree-wrong-radius", "radius_upper", "1/4"),
        ("tree-missing-mathematical-nodes", "nodes", []),
    ):
        changed = deepcopy(tree)
        changed[field] = value
        treecases.append((label, changed, outcome))
    changed = deepcopy(outcome)
    changed["nodes"] += 1
    treecases.append(("wrong-replayed-node-count", tree, changed))
    changed = deepcopy(outcome)
    changed["members"] += 1
    treecases.append(("wrong-positive-tree-member-count", tree, changed))
    for label, changedtree, changedoutcome in treecases:
        try:
            check_tree(changedtree, group, changedoutcome, sha(groupspath), constants, sha(constants_path))
        except (AssertionError, ValueError, IndexError, StopIteration):
            rejected.append(label)
        else:
            raise AssertionError(("invalid mathematical tree identity accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-actual-full-outer-payment-controls-v1",
        "real_original_full_types_in_fixture": 32,
        "previous_pair_and_origin_payments_disjoint_current_subset_positive_control": True,
        "all_one_boundary_faces_and_actual_exposed_centers_checked": True,
        "real_positive_full_outer_tree_mathematically_replayed": True,
        "positive_tree_sha256": sha(treepath), "groups_sha256": sha(groupspath),
        "negative_controls_rejected": rejected,
        "fixture_tree_identifiers_not_counted_as_mathematical_proofs": True,
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_n23_B14_full_outer_payment.py"),
        "frozen_mapping_checker_sha256": sha(HIGH / "audit_streamed_hierarchy.py"),
        "frozen_exact_checker_sha256": sha(HIGH / "exact_graph.py"),
        "global_optimality_proved": False,
    })
    print("N23/B14 actual full-outer payment controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
