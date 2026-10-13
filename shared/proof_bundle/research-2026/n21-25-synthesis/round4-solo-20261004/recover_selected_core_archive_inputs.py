"""Recover only eight named data members, exact archive and manifest hashes."""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, bind, unchanged

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--observation", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    observation_path, output = args.observation.resolve(), args.output.resolve()
    assert observation_path.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    observation = read(observation_path)
    assert observation["schema"] == "small-order-core-input-archive-central-directory-observation-v1"
    assert observation["source_sha256"] == sha(ROOT / "locate_small_order_core_archive_inputs.py")
    incoming = ROOT.parents[4]
    assert incoming.name == "_incoming-local-math-20261004"
    names = {"core-system.json", "core-root.json", "candidate-numeric.json", "kkt-numeric.json"}
    requested = {
        f"workspace/research-2026/n21-25-synthesis/evidence/n{N}/{name}"
        for N in (23, 24) for name in names
    }
    matches = observation["matching_members"]
    assert len(matches) == 8 and {row["member"] for row in matches} == requested
    archives = {row["archive"] for row in matches}
    assert archives == {"math-delta-0052.zip"}
    archive = incoming / "math-delta-0052.zip"
    metadata_path = incoming / "math-delta-0052.zip.meta.json"
    metadata = read(metadata_path)
    assert metadata["part"] == 52 and archive.stat().st_size == metadata["archive_bytes"]
    archive_hash = sha(archive)
    assert archive_hash == metadata["sha256"]
    selected, manifest_records = {}, {}
    with zipfile.ZipFile(archive) as stream:
        manifest_data = stream.read("ASSET-MANIFEST.jsonl")
        for line in manifest_data.decode("utf8").splitlines():
            item = json.loads(line, object_pairs_hook=no_duplicate_keys)
            member = item["sourceRoot"]+"/"+item["path"]
            if member in requested:
                assert member not in manifest_records
                manifest_records[member] = item
        assert set(manifest_records) == requested
        for row in matches:
            member = row["member"]
            item = manifest_records[member]
            info = stream.getinfo(member)
            assert info.file_size == row["bytes"] == item["bytes"] and info.CRC == row["zip_crc32"]
            contents = stream.read(member)
            assert len(contents) == item["bytes"]
            assert hashlib.sha256(contents).hexdigest() == item["sha256"]
            selected[member] = contents
    # All bytes have been checked before creating any destination. This is
    # an exact data copy into a new isolated folder, not a source rewrite.
    output.mkdir()
    records, files = [], {}
    for member, contents in selected.items():
        parts = member.split("/")
        N, name = parts[-2], parts[-1]
        assert N in ("n23", "n24") and name in names
        target = (output / N / name).resolve()
        assert target.is_relative_to(output) and not target.exists()
        target.parent.mkdir(exist_ok=True)
        with target.open("xb") as handle:
            handle.write(contents)
        assert sha(target) == manifest_records[member]["sha256"]
        records.append({"member": member, "recovered_relative_to_round4": target.relative_to(ROOT).as_posix(),
                        "bytes": len(contents), "sha256": sha(target)})
        bind(files, target)
    for N in (23, 24):
        directory = output / f"n{N}"
        system, root = read(directory / "core-system.json"), read(directory / "core-root.json")
        assert system["N"] == N and root["system_sha256"] == sha(directory / "core-system.json")
        assert system["proposal_sha256"] == sha(directory / "candidate-numeric.json")
        assert system["numeric_kkt_sha256"] == sha(directory / "kkt-numeric.json")
    for path in (Path(__file__), observation_path, ROOT / "locate_small_order_core_archive_inputs.py"):
        bind(files, path)
    unchanged(files)
    assert sha(archive) == archive_hash
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "isolated-selected-small-order-core-archive-byte-recovery-v1",
        "archive_absolute_path": str(archive), "archive_sha256": archive_hash,
        "archive_metadata_sha256": sha(metadata_path),
        "asset_manifest_sha256": hashlib.sha256(manifest_data).hexdigest(),
        "selected_data_members": records, "only_eight_explicit_data_files_recovered": True,
        "all_member_bytes_match_asset_manifest_and_internal_root_system_links": True,
        "no_existing_math_directory_or_file_overwritten": True,
        "numeric_roots_and_cover_optimality_not_newly_certified_by_byte_recovery": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })
    print("Isolated N23/N24 archive input recovery PASS: eight exact data files;",
          "archive, manifest and internal root links checked; not a new mathematical proof", flush=True)


if __name__ == "__main__":
    main()
