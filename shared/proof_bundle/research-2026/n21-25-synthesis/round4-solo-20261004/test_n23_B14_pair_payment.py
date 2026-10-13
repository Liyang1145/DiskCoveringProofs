"""Finite real-source pair-map selection refusals; not geometric payments."""
from pathlib import Path
from copy import deepcopy
from collections import Counter
from io import StringIO
import argparse
import json

from audit_n23_B14_pair_payment import ROOT, HIGH, BinaryRows, scan, independent_mask, header, sha, publish
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
    rows = [next(iterator) for _ in range(32)]
    catalog.stream.close()
    groups, lookup, binds, original = [], {}, [], []
    for index, row in rows:
        mask = independent_mask(row["faces"])
        if mask == (1 << 23)-1:
            continue
        code, mapping = canonical(23, 14, row["faces"], 2)
        if code not in lookup:
            lookup[code] = len(groups)
            groups.append({"id": len(groups), "centers": len(mapping["centers"]),
                           "faces": list(code), "members": 0})
        gid = lookup[code]
        groups[gid]["members"] += 1
        binds.append({"index": index, "group": gid, "map": mapping})
        original.append({"index": index, "exposed_mask": mask})
    assert groups and original
    digest = "finite-original-catalog-identifier-not-a-new-proof"
    paid = {0: "functional-tree-identity-not-a-mathematical-proof"}

    def invoke(source=rows, bindings=binds, origins=original, graphgroups=groups,
               expected=len(original), total=32):
        origin = StringIO(json.dumps(header("not-paid-by-origin-condition", digest))+"\n"+
                          "".join(json.dumps(row)+"\n" for row in origins))
        bindingstream = StringIO("".join(json.dumps(row)+"\n" for row in bindings))
        ledger, residual = StringIO(), StringIO()
        result = scan(iter(source), origin, bindingstream, graphgroups, paid,
                      digest, total, expected, ledger, residual)
        return result, ledger.getvalue(), residual.getvalue()

    counts, payments, pending = invoke()
    assert counts["new-strict-pair-type"] == groups[0]["members"]
    assert counts["old-origin-obstruction"] == 32-len(original)
    assert counts["new-strict-pair-type"]+counts.get("pending", 0) == len(original)
    cases = [
        ("missing-actual-binding", {"bindings": binds[:-1]}),
        ("duplicate-actual-binding", {"bindings": binds[:1]+binds}),
        ("extra-actual-binding", {"bindings": binds+[deepcopy(binds[-1])]}),
        ("missing-origin-residual", {"origins": original[:-1]}),
        ("duplicate-origin-residual", {"origins": original[:1]+original}),
        ("source-truncated", {"source": rows[:-1]}),
        ("source-index-gap", {"source": rows[:10]+rows[11:]}),
        ("wrong-residual-count", {"expected": len(original)+1}),
    ]
    changed = deepcopy(original)
    changed[0]["exposed_mask"] ^= 1 << 22
    cases.append(("wrong-original-exposure-mask", {"origins": changed}))
    for label, field, value in (
        ("wrong-boundary-shift", "shift", (binds[0]["map"]["shift"]+1) % 14),
        ("wrong-reflection-anchor", "orientation", -binds[0]["map"]["orientation"]),
        ("anchor-collision", "anchors", [0]*14),
        ("center-collision", "centers", [0]*len(binds[0]["map"]["centers"])),
    ):
        changed = deepcopy(binds)
        changed[0]["map"][field] = value
        cases.append((label, {"bindings": changed}))
    changedgroups = deepcopy(groups)
    changedgroups[0]["members"] += 1
    cases.append(("wrong-original-group-member-count", {"graphgroups": changedgroups}))
    changedgroups = deepcopy(groups)
    changedgroups[0]["faces"].pop()
    cases.append(("omitted-actual-two-boundary-face", {"graphgroups": changedgroups}))
    rejected = []
    for label, kwargs in cases:
        try:
            invoke(**kwargs)
        except (AssertionError, ValueError, IndexError, StopIteration):
            rejected.append(label)
        else:
            raise AssertionError(("invalid original pair payment selection accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-actual-pair-payment-source-map-controls-v1",
        "real_original_full_source_fixture_types": 32,
        "negative_controls_rejected": rejected,
        "functional_tree_identifiers_not_counted_as_mathematical_proofs": True,
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_n23_B14_pair_payment.py"),
        "frozen_mapping_checker_sha256": sha(HIGH / "audit_streamed_hierarchy.py"),
        "global_optimality_proved": False,
    })
    print("N23/B14 actual pair-payment source/map controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
