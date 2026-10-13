"""Recover real original outer bindings and only 22857 still-relevant strict trees.

The old logged prefix is not called a completed job. A new full-index receipt
marks every unused, unlogged, or unsolved group pending, and accepts positive
trees only through a separate fresh standard-library exact replay.
"""
from pathlib import Path
from collections import Counter, defaultdict
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish

assert __debug__
GROUP_MEMBER = "bulk/n23-B15-rest-outer-groups-resume1/GROUPS.json"
BINDING_MEMBER = "bulk/n23-B15-rest-outer-groups-resume1/bindings.jsonl"
LOG_MEMBER = "bulk/n23-B15-rest-outer-root-force-resume1/outcomes.jsonl"
TREE_PREFIX = "bulk/n23-B15-rest-outer-root-force-resume1/"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    dataset, output = args.dataset.resolve(), args.output.resolve()
    assert dataset.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    sourcegroups = dataset / "OUTER/GROUPS.json"
    groups = read(sourcegroups)
    assert (groups["N"], groups["B"], groups["threshold"]) == (23, 15, 1)
    assert groups["group_count"] == len(groups["groups"]) == 535262
    assert groups["selected_types"] == 13603249 and groups["catalog_types"] == 16790546
    assert groups["parent_groups_sha256"] == sha(dataset / "PAIR/GROUPS.json")
    pairpath = ROOT / "n23-B15-original5690-pair-force-tree-recovery-20261005-v1/SUMMARY.json"
    assert groups["parent_proof_sha256"] == sha(pairpath)
    assert [row["id"] for row in groups["groups"]] == list(range(535262))
    for group in groups["groups"]:
        faces, centers = group["faces"], group["centers"]
        assert 15 <= centers <= 23 and faces and faces == sorted(set(faces))
        mask = 0
        for face in faces:
            assert type(face) is int and face.bit_count() == 3 and 0 < face < 1 << centers
            assert face & ((1 << 15)-1)
            mask |= face
        assert mask == (1 << centers)-1
    incoming = ROOT.parents[4]
    assert incoming.name == "_incoming-local-math-20261004"
    observation = read(ROOT / "n23-B14-B15-archive-asset-name-observation-20261005-v1/OBSERVATION.json")
    observed = {row["member"]: row for row in observation["matching_members"]}
    logarchive = incoming / observed[LOG_MEMBER]["archive"]
    with zipfile.ZipFile(logarchive) as archive:
        rawlog = archive.read(LOG_MEMBER)
    logdigest = hashlib.sha256(rawlog).hexdigest()
    complete_lines = rawlog.splitlines(keepends=True)
    relevant = {}
    for index, line in enumerate(complete_lines):
        assert line.endswith(b"\n"), "incomplete log tail is not an accepted outcome"
        row = json.loads(line, object_pairs_hook=no_duplicate_keys)
        assert row["group"] == index and row["status"] in ("pending", "excluded")
        group = groups["groups"][index]
        if row["status"] == "excluded" and group["centers"] < 23:
            assert row["members"] == group["members"]
            relevant[index] = row
    assert len(complete_lines) == 436500 and len(relevant) == 22857
    selected = {
        GROUP_MEMBER: "OUTER/GROUPS.json", BINDING_MEMBER: "OUTER/bindings.jsonl",
        LOG_MEMBER: "ORIGINAL/outcomes.jsonl",
    }
    treehashes = {}
    for index, row in relevant.items():
        member = TREE_PREFIX+f"group-{index:07}.json.gz"
        selected[member] = f"FORCE/group-{index:07}.json.gz"
        treehashes[member] = row["tree_sha256"]
    located, by_archive = {}, defaultdict(list)
    for archive in sorted(incoming.glob("math-delta-*.zip")):
        with zipfile.ZipFile(archive) as source:
            for info in source.infolist():
                member = info.filename.replace("\\", "/")
                if member in selected:
                    assert member not in located
                    located[member] = {"archive": archive.name, "bytes": info.file_size, "crc32": info.CRC}
                    by_archive[archive.name].append(member)
    assert set(located) == set(selected), ("missing actual logged strict trees", sorted(set(selected)-set(located))[:10])
    total = sum(row["bytes"] for row in located.values())
    assert total < 5_000_000_000 and shutil.disk_usage(ROOT).free > total+10_000_000_000
    assets, archives = {}, {}
    for name in sorted(by_archive):
        archive = incoming / name
        metapath = incoming / (name+".meta.json")
        metadata = read(metapath)
        assert archive.stat().st_size == metadata["archive_bytes"] and sha(archive) == metadata["sha256"]
        with zipfile.ZipFile(archive) as source:
            manifest = source.read("ASSET-MANIFEST.jsonl")
            for line in manifest.decode("utf8").splitlines():
                row = json.loads(line, object_pairs_hook=no_duplicate_keys)
                member = row["sourceRoot"]+"/"+row["path"]
                if member in by_archive[name]:
                    assert member not in assets
                    assets[member] = row
            for member in by_archive[name]:
                assert assets[member]["bytes"] == located[member]["bytes"]
                assert source.getinfo(member).CRC == located[member]["crc32"]
                expected = (sha(sourcegroups) if member == GROUP_MEMBER else
                            groups["bindings_sha256"] if member == BINDING_MEMBER else
                            logdigest if member == LOG_MEMBER else treehashes[member])
                assert assets[member]["sha256"] == expected
        archives[name] = {
            "archive_sha256": metadata["sha256"], "metadata_sha256": sha(metapath),
            "asset_manifest_sha256": hashlib.sha256(manifest).hexdigest(),
        }
        print("Relevant original N23 outer strict-tree archive checked:", name, flush=True)
    assert set(assets) == set(selected)
    output.mkdir()
    publish(output / "INPUT-PLAN.json", {
        "N": 23, "B": 15, "selected_relevant_strict_trees": len(relevant),
        "old_logged_prefix_groups": len(complete_lines), "old_total_outer_groups": 535262,
        "total_uncompressed_bytes": total, "archive_bindings": archives,
        "old_prefix_not_a_completed_force_job": True,
        "all_omitted_groups_remain_pending_in_new_receipt": True, "global_optimality_proved": False,
    })
    copied, records = 0, []
    for name in sorted(by_archive):
        archive = incoming / name
        with zipfile.ZipFile(archive) as source:
            for member in by_archive[name]:
                target = (output / selected[member]).resolve()
                assert target.is_relative_to(output) and not target.exists()
                target.parent.mkdir(parents=True, exist_ok=True)
                digest = hashlib.sha256()
                size = 0
                with source.open(member) as src, target.open("xb") as dst:
                    for block in iter(lambda: src.read(1 << 20), b""):
                        dst.write(block);digest.update(block);size += len(block)
                assert size == assets[member]["bytes"] and digest.hexdigest() == assets[member]["sha256"]
                assert sha(target) == digest.hexdigest()
                copied += size
                records.append({"recovered_file": selected[member], "bytes": size, "sha256": digest.hexdigest()})
                if len(records) % 2000 == 0 or member == BINDING_MEMBER:
                    print("Relevant original outer proof bytes copied:", len(records), "/", len(selected),
                          "bytes", copied, "/", total, flush=True)
        assert sha(archive) == archives[name]["archive_sha256"]
    assert copied == total and sha(output / "ORIGINAL/outcomes.jsonl") == logdigest
    assert sha(output / "OUTER/GROUPS.json") == sha(sourcegroups)
    outcomes = []
    for index in range(535262):
        if index in relevant:
            outcomes.append(relevant[index])
        else:
            outcomes.append({"group": index, "status": "pending",
                             "unlogged_unsolved_or_origin23_graph_not_paid_by_this_receipt": True})
    receiptpath = output / "FORCE/SUMMARY.json"
    publish(receiptpath, {
        "schema": "filtered-original-logged-N23-outer-positive-tree-receipt-v1",
        "N": 23, "B": 15, "groups_sha256": sha(output / "OUTER/GROUPS.json"), "outcomes": outcomes,
        "excluded_groups": len(relevant), "pending_groups": 535262-len(relevant),
        "catalog_members_excluded": sum(groups["groups"][i]["members"] for i in relevant),
        "requested_groups_complete": False,
        "all_group_indices_have_explicit_status_unused_and_unlogged_remain_pending": True,
        "old_logged_prefix_groups": len(complete_lines), "old_prefix_does_not_prove_search_or_job_exhaustion": True,
        "original_logged_outcomes_sha256": logdigest,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    replayer = HIGH / "replay_group_stage.py"
    with (output / "REPLAY-STDOUT.log").open("xb") as stdout, (output / "REPLAY-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen([
            sys.executable, "-u", str(replayer), "--groups", str(output / "OUTER/GROUPS.json"),
            "--receipt", str(receiptpath), "--output", str(output / "EXACT-REPLAY.json")],
            stdout=stdout, stderr=stderr, cwd=str(ROOT),
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "REPLAY-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid, "source_sha256": sha(replayer),
        "independent_process_terminal_observed": True,
    })
    assert code == 0
    replay = read(output / "EXACT-REPLAY.json")
    assert replay["verified"] and replay["exact_groups_replayed"] == 22857
    assert replay["associated_member_count"] == 2058635
    assert replay["receipt_sha256"] == sha(receiptpath)
    assert replay["groups_sha256"] == sha(output / "OUTER/GROUPS.json")
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "isolated-N23-relevant-original-outer-tree-recovery-and-replay-v1",
        "N": 23, "B": 15, "strict_trees_recovered_and_fresh_replayed": 22857,
        "original_outer_groups": 535262, "original_logged_prefix_groups": 436500,
        "no_original_job_completion_or_unlogged_exclusion_claimed": True,
        "all_unused_or_unlogged_groups_kept_pending": True,
        "all_actual_group_masks_checked_not_only_declared_centers": True,
        "all_actual_tree_bytes_bound_to_original_logged_outcomes_and_archive_assets": True,
        "original_outer_bindings_exactly_restored_not_yet_mathematically_mapped": True,
        "records": records, "archive_bindings": archives, "total_uncompressed_bytes": total,
        "groups_sha256": sha(output / "OUTER/GROUPS.json"), "receipt_sha256": sha(receiptpath),
        "exact_replay_sha256": sha(output / "EXACT-REPLAY.json"),
        "source_sha256": sha(Path(__file__)),
        "all_type_maps_and_disjoint_source_payment_merge_still_required": True,
        "global_optimality_proved": False,
    })
    print("22857 original relevant N23 outer strict trees recovered and freshly accepted;", total, "bytes", flush=True)


if __name__ == "__main__":
    main()
