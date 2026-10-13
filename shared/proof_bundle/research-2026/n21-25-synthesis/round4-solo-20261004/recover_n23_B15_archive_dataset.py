"""Stream-copy five explicit N23 B15 dataset members into an isolated root."""
from pathlib import Path
from collections import defaultdict
import argparse
import hashlib
import json
import shutil
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, bind, unchanged

assert __debug__

SELECTED = {
    "workspace/research-2026/n21-25-synthesis/round3-high/evidence/n23-B15-degree-streamed-resume1/N23-B15-dfs.json":
        "CATALOG/N23-B15-dfs.json",
    "workspace/research-2026/n21-25-synthesis/round3-high/evidence/n23-B15-degree-streamed-resume1/SUMMARY.json":
        "CATALOG/SUMMARY.json",
    "bulk/n23-B15-all-pair-groups-resume1/bindings.jsonl":
        "PAIR/bindings.jsonl",
    "bulk/n23-B15-all-pair-groups-resume1/GROUPS.json":
        "PAIR/GROUPS.json",
    "bulk/n23-B15-rest-outer-groups-resume1/GROUPS.json":
        "OUTER/GROUPS.json",
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--observation", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    observation_path, output = args.observation.resolve(), args.output.resolve()
    assert observation_path.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    observed = read(observation_path)
    assert observed["schema"] == "N23-B14-B15-family-archive-name-observation-v1"
    assert observed["source_sha256"] == sha(ROOT / "locate_n23_family_archive_assets.py")
    available = {row["member"]: row for row in observed["matching_members"]}
    assert set(SELECTED) <= set(available)
    incoming = ROOT.parents[4]
    assert incoming.name == "_incoming-local-math-20261004"
    total = sum(available[member]["bytes"] for member in SELECTED)
    assert total < 9_000_000_000 and shutil.disk_usage(ROOT).free > total+15_000_000_000
    archives = defaultdict(list)
    for member in SELECTED:
        archives[available[member]["archive"]].append(member)
    metadata, expected = {}, {}
    # Validate whole archive bytes and selected manifest records first.
    for name in sorted(archives):
        archive = incoming / name
        meta_path = incoming / (name+".meta.json")
        meta = read(meta_path)
        assert archive.stat().st_size == meta["archive_bytes"]
        digest = sha(archive)
        assert digest == meta["sha256"]
        with zipfile.ZipFile(archive) as stream:
            manifest = stream.read("ASSET-MANIFEST.jsonl")
            manifest_digest = hashlib.sha256(manifest).hexdigest()
            for line in manifest.decode("utf8").splitlines():
                row = json.loads(line, object_pairs_hook=no_duplicate_keys)
                member = row["sourceRoot"]+"/"+row["path"]
                if member in archives[name]:
                    assert member not in expected
                    expected[member] = row
            for member in archives[name]:
                info = stream.getinfo(member)
                assert info.file_size == available[member]["bytes"] == expected[member]["bytes"]
                assert info.CRC == available[member]["zip_crc32"]
        metadata[name] = {"archive_sha256": digest, "archive_metadata_sha256": sha(meta_path),
                          "asset_manifest_sha256": manifest_digest}
        print("N23 B15 source archive verified:", name, flush=True)
    assert set(expected) == set(SELECTED)
    output.mkdir()
    publish(output / "INPUT-PLAN.json", {
        "schema": "isolated-five-member-N23-B15-byte-recovery-plan-v1",
        "members": SELECTED, "total_uncompressed_bytes": total,
        "archive_bindings": metadata, "not_mathematical_acceptance": True,
    })
    records, files = [], {}
    for name in sorted(archives):
        archive = incoming / name
        with zipfile.ZipFile(archive) as stream:
            for member in archives[name]:
                target = (output / SELECTED[member]).resolve()
                assert target.is_relative_to(output) and not target.exists()
                target.parent.mkdir(exist_ok=True)
                digest, copied = hashlib.sha256(), 0
                progress = 1 << 29
                with stream.open(member) as source, target.open("xb") as destination:
                    while True:
                        block = source.read(1 << 20)
                        if not block:
                            break
                        destination.write(block)
                        digest.update(block)
                        copied += len(block)
                        if copied >= progress:
                            print("N23 B15 exact data copy:", SELECTED[member], copied,
                                  "/", expected[member]["bytes"], "bytes", flush=True)
                            progress += 1 << 29
                assert copied == expected[member]["bytes"] and digest.hexdigest() == expected[member]["sha256"]
                assert sha(target) == expected[member]["sha256"]
                records.append({"member": member, "recovered_relative_to_round4": target.relative_to(ROOT).as_posix(),
                                "bytes": copied, "sha256": digest.hexdigest()})
                bind(files, target)
        assert sha(archive) == metadata[name]["archive_sha256"]
    catalog_path = output / "CATALOG/N23-B15-dfs.json"
    summary, pair, outer = map(read, (
        output / "CATALOG/SUMMARY.json", output / "PAIR/GROUPS.json", output / "OUTER/GROUPS.json"))
    assert summary["N"] == pair["N"] == outer["N"] == 23
    assert summary["B"] == pair["B"] == outer["B"] == 15
    assert summary["catalog_sha256"] == pair["catalog_sha256"] == outer["catalog_sha256"] == sha(catalog_path)
    assert summary["orbits"] == pair["catalog_types"] == pair["selected_types"] == 16790546
    assert pair["group_count"] == len(pair["groups"]) == 20139 and pair["threshold"] == 2
    assert pair["full_selected_catalog_scanned"] and pair["parent_groups_sha256"] is None
    assert pair["bindings_sha256"] == sha(output / "PAIR/bindings.jsonl")
    assert outer["group_count"] == len(outer["groups"]) == 535262 and outer["threshold"] == 1
    assert outer["selected_types"] == 13603249 and outer["full_selected_catalog_scanned"]
    assert outer["parent_groups_sha256"] == sha(output / "PAIR/GROUPS.json")
    for path in (Path(__file__), observation_path, ROOT / "locate_n23_family_archive_assets.py",
                 output / "INPUT-PLAN.json"):
        bind(files, path)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "isolated-N23-B15-five-member-archive-byte-recovery-v1",
        "N": 23, "B": 15, "selected_members": records, "archive_bindings": metadata,
        "all_recovered_bytes_match_exact_original_asset_manifest": True,
        "catalog_pair_and_outer_internal_byte_links_checked": True,
        "outer_bindings_and_force_trees_not_recovered_by_this_step": True,
        "full_catalog_rows_and_mapping_counts_not_yet_scanned": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "not_a_new_catalogue_completeness_or_mathematical_payment": True,
        "global_optimality_proved": False,
    })
    print("N23 B15 isolated dataset byte recovery complete:", total,
          "bytes; full row/mapping and proof audits still required", flush=True)


if __name__ == "__main__":
    main()
