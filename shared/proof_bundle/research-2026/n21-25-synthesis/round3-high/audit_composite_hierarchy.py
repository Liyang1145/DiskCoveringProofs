"""Full map/hierarchy audit accepting explicit disjoint exact-replay unions.

Unchanged map validation and stream consumption are inherited from the
immutable original auditor. Composite acceptance rechecks every component's
hash-bound original exact replay and their disjoint accounting, not flags.
"""
from pathlib import Path
from collections import Counter
import argparse
import time
from audit_streamed_hierarchy import Stage, read
from certified_receipt_union import checked_union_report
from stream_catalog import Catalog, sha
from enumerate_search_stage import write_new

ROOT = Path(__file__).resolve().parent
assert __debug__


class CompositeStage(Stage):
    def __init__(self, groupspath, unionpath, N, B, catalog_digest, catalog_count):
        self.group_path = Path(groupspath)
        self.data = data = read(self.group_path)
        self.digest = sha(self.group_path)
        assert (data["N"], data["B"]) == (N, B)
        assert data["catalog_sha256"] == catalog_digest and data["catalog_types"] == catalog_count
        assert data["full_selected_catalog_scanned"]
        assert type(data["threshold"]) is int and data["threshold"] in (0, 1, 2)
        assert [g["id"] for g in data["groups"]] == list(range(data["group_count"]))
        union = checked_union_report(self.group_path, unionpath)
        self.receipt_path = Path(unionpath)
        self.replay_path = Path(unionpath)
        self.paid = {row["group"] for row in union["outcomes"] if row["status"] == "excluded"}
        self.replay = {"associated_member_count": union["catalog_members_excluded"]}
        self.binding_path = self.group_path.parent / data["bindings_file"]
        assert sha(self.binding_path) == data["bindings_sha256"] == union["bindings_sha256"]
        self.counts, self.paid_counts = Counter(), Counter()
        self.stream = self.binding_path.open(encoding="utf8")
        self.previous = -1
        self.next = self.advance()
        self.seen = 0


def audit(catalogpath, specs, output):
    output = Path(output)
    assert not output.exists() and not output.with_suffix(".pending.jsonl").exists()
    catalog = Catalog(catalogpath)
    N, B, count = (catalog.header[key] for key in ("N", "B", "orbits"))
    assert N in (22, 23, 24, 25)
    digest = sha(catalogpath)
    stages = []
    for group, receipt, replay in specs:
        if replay == "COMPOSITE":
            stages.append(CompositeStage(group, receipt, N, B, digest, count))
        else:
            stages.append(Stage((group, receipt, replay), N, B, digest, count))
    assert stages and stages[0].data["parent_groups_sha256"] is None
    assert stages[0].data["parent_proof_sha256"] is None
    for parent, child in zip(stages, stages[1:]):
        assert parent.receipt_path is not None
        assert child.data["threshold"] < parent.data["threshold"]
        assert child.data["parent_groups_sha256"] == parent.digest
        assert child.data["parent_proof_sha256"] == sha(parent.receipt_path)
    pendingpath = output.with_suffix(".pending.jsonl")
    started = time.monotonic()
    pending = 0
    with pendingpath.open("x", encoding="utf8") as stream:
        for index, row in catalog.rows():
            full, active = set(row["faces"]), True
            for stage in stages:
                if active:
                    active = not stage.consume(index, full, N, B)
                else:
                    assert stage.next is None or stage.next["index"] > index
            if active:
                stream.write('{"index":'+str(index)+'}\n')
                pending += 1
            if (index+1) % 100000 == 0:
                print("Composite hierarchy full types audited", index+1,
                      "seconds", round(time.monotonic()-started, 1), flush=True)
    reports = [stage.finish() for stage in stages]
    assert sum(row["paid_types"] for row in reports)+pending == count
    result = {"verified": True, "N": N, "B": B, "catalog_sha256": digest,
              "catalog_types": count, "stages": reports,
              "strict_exclusion_types_with_replayed_certificates": count-pending,
              "pending_types": pending, "pending_indices_file": pendingpath.name,
              "pending_indices_sha256": sha(pendingpath),
              "disjoint_hierarchy_partition_verified": True,
              "coverage_partition_complete": pending == 0,
              "catalog_completeness_proved_here": False, "actual_cover_reduction_proved_here": False,
              "global_optimality_proved": False, "source_sha256": sha(Path(__file__)),
              "original_map_auditor_sha256": sha(ROOT / "audit_streamed_hierarchy.py"),
              "composite_union_auditor_sha256": sha(ROOT / "certified_receipt_union.py"),
              "stream_reader_sha256": sha(ROOT / "stream_catalog.py")}
    write_new(output, result)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--catalog", type=Path, required=True)
    ap.add_argument("--stage", nargs=3, action="append", required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    result = audit(args.catalog, args.stage, args.output)
    print("Composite hierarchy PASS; pending", result["pending_types"], flush=True)


if __name__ == "__main__":
    main()
