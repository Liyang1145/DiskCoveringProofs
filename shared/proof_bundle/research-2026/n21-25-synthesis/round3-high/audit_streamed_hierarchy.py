"""Independent streamed face/anchor-transfer and hierarchy partition audit.

No grouping, canonicalization, proposal, or optimization code is imported.
Previously paid force certificates are used only through hash-bound fresh
standard-library replay receipts. This does not prove catalogue completeness
or the actual-cover reduction, and never claims global optimality by itself.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import json
import time
from stream_catalog import Catalog, sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(Path(path).read_text(encoding="utf8"),
                      object_pairs_hook=no_duplicate_keys)


def check_map(N, B, group, mapping, full, threshold):
    center, anchor = mapping["centers"], mapping["anchors"]
    assert type(center) is list and type(anchor) is list
    assert len(center) == group["centers"] and B <= len(center) <= N
    assert all(type(v) is int and 0 <= v < N for v in center)
    assert len(set(center)) == len(center)
    assert sorted(center[:B]) == list(range(B))
    assert all(v >= B for v in center[B:])
    assert len(anchor) == B and all(type(v) is int for v in anchor)
    assert sorted(anchor) == list(range(B))
    assert type(mapping["orientation"]) is int
    assert type(mapping["shift"]) is int
    sign, shift = mapping["orientation"], mapping["shift"]
    assert sign in (1, -1) and 0 <= shift < B
    assert center[:B] == [(shift+sign*j) % B for j in range(B)]
    # A reflected boundary edge shifts its anchor by one, not zero.
    assert anchor == [(shift+sign*j-(sign < 0)) % B for j in range(B)]
    for j in range(B):
        assert {center[j], center[(j+1) % B]} == {anchor[j], (anchor[j]+1) % B}
    code = group["faces"]
    assert type(code) is list and code == sorted(set(code))
    images = set()
    for mask in code:
        assert type(mask) is int and 0 < mask < (1 << len(center))
        assert mask.bit_count() == 3
        image = sum(1 << center[v] for v in range(len(center)) if mask >> v & 1)
        assert image in full
        images.add(image)
    assert len(images) == len(code)
    retained = {mask for mask in full
                if (mask & ((1 << B)-1)).bit_count() >= threshold}
    assert images == retained


class Stage:
    def __init__(self, paths, N, B, catalog_digest, catalog_count):
        self.group_path = Path(paths[0])
        self.data = data = read(self.group_path)
        self.digest = sha(self.group_path)
        assert (data["N"], data["B"]) == (N, B)
        assert data["catalog_sha256"] == catalog_digest
        assert data["catalog_types"] == catalog_count
        assert data["full_selected_catalog_scanned"]
        assert type(data["threshold"]) is int and data["threshold"] in (0, 1, 2)
        assert [g["id"] for g in data["groups"]] == list(range(data["group_count"]))
        self.counts = Counter()
        self.paid_counts = Counter()
        self.receipt_path = None
        self.replay_path = None
        self.paid = set()
        if paths[1] != "-":
            assert paths[2] != "-"
            self.receipt_path, self.replay_path = Path(paths[1]), Path(paths[2])
            receipt, replay = read(self.receipt_path), read(self.replay_path)
            assert (receipt["N"], receipt["B"]) == (N, B)
            assert (replay["N"], replay["B"]) == (N, B)
            assert replay["verified"]
            assert receipt["groups_sha256"] == replay["groups_sha256"] == self.digest
            assert replay["receipt_sha256"] == sha(self.receipt_path)
            assert replay["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
            assert replay["source_sha256"] == sha(ROOT / "replay_group_stage.py")
            outcomes = receipt["outcomes"]
            assert sorted(r["group"] for r in outcomes) == list(range(data["group_count"]))
            assert all(r["status"] in ("excluded", "pending") for r in outcomes)
            self.paid = {r["group"] for r in outcomes if r["status"] == "excluded"}
            assert len(self.paid) == receipt["excluded_groups"] == replay["exact_groups_replayed"]
            assert data["group_count"]-len(self.paid) == replay["pending_groups"]
            assert receipt["catalog_members_excluded"] == replay["associated_member_count"]
            assert sum(data["groups"][g]["members"] for g in self.paid) == replay["associated_member_count"]
            assert not self.paid or F(replay["minimum_force_margin"]) > 0
            self.replay = replay
        else:
            assert paths[2] == "-"
            self.replay = None
        self.binding_path = self.group_path.parent / data["bindings_file"]
        assert sha(self.binding_path) == data["bindings_sha256"]
        if self.replay is not None:
            assert self.replay["bindings_sha256"] == data["bindings_sha256"]
        self.stream = self.binding_path.open(encoding="utf8")
        self.previous = -1
        self.next = self.advance()
        self.seen = 0

    def advance(self):
        line = self.stream.readline()
        if not line:
            return None
        row = json.loads(line, object_pairs_hook=no_duplicate_keys)
        assert type(row["index"]) is int and self.previous < row["index"] < self.data["catalog_types"]
        self.previous = row["index"]
        assert type(row["group"]) is int and 0 <= row["group"] < self.data["group_count"]
        return row

    def consume(self, index, full, N, B):
        assert self.next is not None and self.next["index"] == index, (
            "missing selected type or reintroduced/extra child type", index)
        binding = self.next
        gid = binding["group"]
        check_map(N, B, self.data["groups"][gid], binding["map"], full, self.data["threshold"])
        self.counts[gid] += 1
        self.seen += 1
        paid = gid in self.paid
        if paid:
            self.paid_counts[gid] += 1
        self.next = self.advance()
        return paid

    def finish(self):
        assert self.next is None, "extra selected type in child"
        self.stream.close()
        assert self.seen == self.data["selected_types"]
        assert all(self.counts[g["id"]] == g["members"] > 0 for g in self.data["groups"])
        assert set(self.counts) == set(range(self.data["group_count"]))
        paid_count = sum(self.paid_counts.values())
        if self.replay is not None:
            assert paid_count == self.replay["associated_member_count"]
        return {"groups_sha256": self.digest, "bindings_sha256": sha(self.binding_path),
                "threshold": self.data["threshold"], "maps_checked": self.seen,
                "paid_types": paid_count, "remaining_types": self.seen-paid_count,
                "force_replay_sha256": None if self.replay_path is None else sha(self.replay_path)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--catalog", type=Path, required=True)
    ap.add_argument("--stage", nargs=3, action="append", required=True,
                    metavar=("GROUPS", "RECEIPT", "REPLAY"))
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    pending_path = args.output.with_suffix(".pending.jsonl")
    assert not pending_path.exists()
    catalog = Catalog(args.catalog)
    N, B, count = (catalog.header[k] for k in ("N", "B", "orbits"))
    assert N in (22, 23, 24, 25)
    digest = sha(args.catalog)
    stages = [Stage(paths, N, B, digest, count) for paths in args.stage]
    assert stages[0].data["parent_groups_sha256"] is None
    assert stages[0].data["parent_proof_sha256"] is None
    for previous, stage in zip(stages, stages[1:]):
        assert previous.receipt_path is not None
        assert stage.data["threshold"] < previous.data["threshold"]
        assert stage.data["parent_groups_sha256"] == previous.digest
        assert stage.data["parent_proof_sha256"] == sha(previous.receipt_path)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    pending_count = 0
    started = time.monotonic()
    with pending_path.open("w", encoding="utf8") as pending:
        for index, row in catalog.rows():
            full = set(row["faces"])
            active = True
            for stage in stages:
                if active:
                    active = not stage.consume(index, full, N, B)
                else:
                    assert stage.next is None or stage.next["index"] > index
            if active:
                pending.write(json.dumps({"index": index}, separators=(",", ":"))+"\n")
                pending_count += 1
            if (index+1) % 100000 == 0:
                print("N", N, "B", B, "full types audited", index+1,
                      "seconds", round(time.monotonic()-started, 2), flush=True)
    reports = [stage.finish() for stage in stages]
    assert sum(report["paid_types"] for report in reports)+pending_count == count
    report = {"verified": True, "N": N, "B": B, "catalog_sha256": digest,
              "catalog_types": count, "stages": reports,
              "strict_exclusion_types_with_replayed_certificates": count-pending_count,
              "pending_types": pending_count, "pending_indices_file": pending_path.name,
              "pending_indices_sha256": sha(pending_path),
              "disjoint_hierarchy_partition_verified": True,
              "coverage_partition_complete": pending_count == 0,
              "catalog_completeness_proved_here": False,
              "actual_cover_reduction_proved_here": False,
              "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__)),
              "stream_reader_sha256": sha(ROOT / "stream_catalog.py")}
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N", N, "B", B, "independent streamed hierarchy PASS; pending", pending_count, flush=True)


if __name__ == "__main__":
    main()
