"""Recover only the 5690 receipt-bound strict trees, then fresh stdlib replay."""
from pathlib import Path
from collections import defaultdict
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
PREFIX = "bulk/n23-B15-all-pair-root-force-resume1/"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    dataset, output = args.dataset.resolve(), args.output.resolve()
    assert dataset.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    receiptpath = ROOT.parents[3] / PREFIX / "SUMMARY.json"
    receipt = read(receiptpath)
    groupspath = dataset / "PAIR/GROUPS.json"
    groups = read(groupspath)
    assert receipt["groups_sha256"] == sha(groupspath)
    assert receipt["source_sha256"] == sha(HIGH / "probe_groups.py")
    assert (receipt["N"], receipt["B"]) == (groups["N"], groups["B"]) == (23, 15)
    assert receipt["requested_groups_complete"] and groups["full_selected_catalog_scanned"]
    assert groups["group_count"] == len(groups["groups"]) == len(receipt["outcomes"]) == 20139
    assert [row["group"] for row in receipt["outcomes"]] == list(range(20139))
    strict = [row for row in receipt["outcomes"] if row["status"] == "excluded"]
    assert len(strict) == receipt["excluded_groups"] == 5690
    assert receipt["pending_groups"] == 14449 and receipt["catalog_members_excluded"] == 3187297
    assert receipt["outcomes"][receipt["known_attaining_group_control"]]["status"] == "pending"
    expected_tree_hashes = {
        PREFIX+f"group-{row['group']:07}.json.gz": row["tree_sha256"] for row in strict}
    selected = set(expected_tree_hashes) | {PREFIX+"SUMMARY.json"}
    incoming = ROOT.parents[4]
    assert incoming.name == "_incoming-local-math-20261004"
    archives = sorted(incoming.glob("math-delta-*.zip"))
    assert len(archives) == 134
    located = {}
    by_archive = defaultdict(list)
    for archive in archives:
        with zipfile.ZipFile(archive) as source:
            for info in source.infolist():
                member = info.filename.replace("\\", "/")
                if member not in selected:
                    continue
                assert member not in located, ("duplicate selected archive member", member)
                located[member] = {"archive": archive.name, "bytes": info.file_size, "crc32": info.CRC}
                by_archive[archive.name].append(member)
    assert set(located) == selected, ("missing actual receipt-bound trees", sorted(selected-set(located))[:10])
    total = sum(row["bytes"] for row in located.values())
    assert total < 3_000_000_000 and shutil.disk_usage(ROOT).free > total+10_000_000_000
    archive_bindings, assets = {}, {}
    for name in sorted(by_archive):
        archive = incoming / name
        metadata_path = incoming / (name+".meta.json")
        metadata = read(metadata_path)
        assert archive.stat().st_size == metadata["archive_bytes"] and sha(archive) == metadata["sha256"]
        with zipfile.ZipFile(archive) as source:
            manifest = source.read("ASSET-MANIFEST.jsonl")
            for line in manifest.decode("utf8").splitlines():
                asset = json.loads(line, object_pairs_hook=no_duplicate_keys)
                member = asset["sourceRoot"]+"/"+asset["path"]
                if member in by_archive[name]:
                    assert member not in assets
                    assets[member] = asset
            for member in by_archive[name]:
                asset = assets[member]
                expected = sha(receiptpath) if member.endswith("/SUMMARY.json") else expected_tree_hashes[member]
                assert asset["sha256"] == expected and asset["bytes"] == located[member]["bytes"]
                assert source.getinfo(member).CRC == located[member]["crc32"]
        archive_bindings[name] = {
            "archive_sha256": metadata["sha256"], "metadata_sha256": sha(metadata_path),
            "asset_manifest_sha256": hashlib.sha256(manifest).hexdigest(),
        }
        print("N23/B15 strict tree source archive accepted:", name, flush=True)
    assert set(assets) == selected
    output.mkdir()
    publish(output / "INPUT-PLAN.json", {
        "N": 23, "B": 15, "selected_strict_trees": 5690,
        "original_receipt_sha256": sha(receiptpath), "groups_sha256": sha(groupspath),
        "total_uncompressed_bytes": total, "archive_bindings": archive_bindings,
        "only_original_receipt_strict_tree_whitelist": True,
        "not_yet_math_replay_or_complete_catalog_mapping": True,
    })
    records = []
    for name in sorted(by_archive):
        archive = incoming / name
        with zipfile.ZipFile(archive) as source:
            for member in by_archive[name]:
                target = output / member[len(PREFIX):]
                assert target.parent == output and not target.exists()
                digest = hashlib.sha256()
                count = 0
                with source.open(member) as src, target.open("xb") as destination:
                    for block in iter(lambda: src.read(1 << 20), b""):
                        destination.write(block)
                        digest.update(block)
                        count += len(block)
                assert count == assets[member]["bytes"] and digest.hexdigest() == assets[member]["sha256"]
                assert sha(target) == assets[member]["sha256"]
                records.append({"member": member, "recovered_file": target.name,
                                "bytes": count, "sha256": digest.hexdigest()})
                if len(records) % 1000 == 0:
                    print("N23/B15 exact recovered strict tree assets:", len(records), "/", len(selected), flush=True)
        assert sha(archive) == archive_bindings[name]["archive_sha256"]
    assert sha(output / "SUMMARY.json") == sha(receiptpath)
    replayer = HIGH / "replay_group_stage.py"
    replayer_hash = sha(replayer)
    with (output / "REPLAY-STDOUT.log").open("xb") as stdout, (output / "REPLAY-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen([
            sys.executable, "-u", str(replayer), "--groups", str(groupspath),
            "--receipt", str(output / "SUMMARY.json"), "--output", str(output / "EXACT-REPLAY.json")],
            stdout=stdout, stderr=stderr, cwd=str(ROOT),
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "REPLAY-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid, "source_sha256": replayer_hash,
        "independent_process_terminal_observed": True,
    })
    assert code == 0 and sha(replayer) == replayer_hash
    replay = read(output / "EXACT-REPLAY.json")
    assert replay["verified"] and replay["exact_groups_replayed"] == 5690
    assert replay["receipt_sha256"] == sha(output / "SUMMARY.json")
    assert replay["groups_sha256"] == sha(groupspath) and replay["associated_member_count"] == 3187297
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "isolated-N23-B15-receipt-bound-force-tree-byte-recovery-and-replay-v1",
        "N": 23, "B": 15, "strict_trees_recovered_and_freshly_replayed": 5690,
        "selected_assets": records, "archive_bindings": archive_bindings,
        "groups_sha256": sha(groupspath), "receipt_sha256": sha(output / "SUMMARY.json"),
        "exact_replay_sha256": sha(output / "EXACT-REPLAY.json"),
        "source_sha256": sha(Path(__file__)),
        "original_catalog_pair_maps_still_require_full_stream_acceptance": True,
        "old_member_count_not_added_to_origin_obstructions_without_disjoint_merge": True,
        "global_optimality_proved": False,
    })
    print("N23/B15 5690 original strict trees recovered and independently replayed;", total, "bytes", flush=True)


if __name__ == "__main__":
    main()
