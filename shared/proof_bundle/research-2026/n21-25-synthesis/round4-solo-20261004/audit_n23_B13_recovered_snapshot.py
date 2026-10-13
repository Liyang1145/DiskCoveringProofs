"""All original snapshot bytes: current relocated files, ZIP fallback only if absent.

No old absolute reference is rewritten. This verifies byte integrity, not
fresh mathematical replay or the optimality theorem.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from audit_multiroot_snapshot import records, unique, digest
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish

assert __debug__
EXPECTED_SNAPSHOT = "64578536865f5078df43decda920f9043468f4fc35f1457bdf8cd0af6a8f6f79"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--metadata", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    metadata, output = args.metadata.resolve(), args.output.resolve()
    assert metadata.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    recovery = read(metadata / "VERIFIED.json")
    assert recovery["verified"] and recovery["original_absolute_paths_retained_unchanged"]
    assert recovery["source_sha256"] == sha(ROOT / "recover_n23_B13_final_archive_metadata.py")
    manifest = metadata / "N23-B13-CATALOGUE-SNAPSHOT-cross-volume-resume1.json"
    assert sha(manifest) == EXPECTED_SNAPSHOT
    with manifest.open(encoding="utf8") as stream:
        for _ in records(stream):
            pass
        footer = json.loads("{"+stream.read(), object_pairs_hook=unique)
    assert footer["schema"] == "disk-cover-multiroot-snapshot-v1"
    assert footer["verified"] and (footer["N"], footer["B"], footer["catalog_types"]) == (23, 13, 1530509)
    assert footer["recorded_catalogue_branch_closed"] and not footer["global_optimality_proved"]
    assert footer["strict_exclusion_types_with_replayed_certificates"] == 1530509
    assert footer["file_count"] == 670428 and set(footer["roots"]) == {"workspace", "bulk"}
    recoveredroot = ROOT.parents[3]
    roots = {"workspace": ROOT.parents[2], "bulk": recoveredroot / "bulk"}
    assert roots["workspace"].name == "workspace" and roots["bulk"].is_dir()
    incoming = ROOT.parents[4]
    assert incoming.name == "_incoming-local-math-20261004"
    output.mkdir()
    started, checked, local, missing, failures = time.monotonic(), 0, 0, {}, []
    parents = {}
    with manifest.open(encoding="utf8") as stream, \
            (output / "LOCAL-FILES.jsonl").open("x", encoding="ascii") as ledger:
        for name, parts, key, expected in records(stream):
            assert name in roots
            parentkey = (name, parts[:-1])
            if parentkey not in parents:
                parents[parentkey] = roots[name].joinpath(*parts[:-1]).resolve()
            path = parents[parentkey] / parts[-1]
            assert path.is_relative_to(roots[name]) and not path.is_symlink()
            if path.is_file():
                actual = digest(path)
                local += 1
                ledger.write(json.dumps({"key": key, "sha256": actual},
                                        separators=(",", ":"))+"\n")
                if actual != expected:
                    failures.append({"key": key, "problem": "current recovered byte mismatch"})
            else:
                assert key not in missing
                missing[key] = expected
            checked += 1
            if checked % 10000 == 0:
                print("N23 B13 snapshot current relocated bytes", checked, "/", footer["file_count"],
                      "absent", len(missing), "differences", len(failures), flush=True)
    assert checked == footer["file_count"]
    archives = sorted(incoming.glob("math-delta-*.zip"))
    assert len(archives) == 134
    plans, asset_links = {}, {}
    for number, archive in enumerate(archives, 1):
        with zipfile.ZipFile(archive) as stream:
            with stream.open("ASSET-MANIFEST.jsonl") as assets:
                for raw in assets:
                    row = json.loads(raw.decode("utf8"), object_pairs_hook=no_duplicate_keys)
                    key = row["sourceRoot"]+"/"+row["path"]
                    if key not in missing:
                        continue
                    p = PurePosixPath(key)
                    assert not p.is_absolute() and ".." not in p.parts
                    assert "\\" not in key and ":" not in key and p.as_posix() == key
                    assert key not in asset_links, "ambiguous archive fallback asset"
                    info = stream.getinfo(key)
                    assert info.file_size == row["bytes"]
                    assert row["sha256"] == missing[key], "asset manifest differs from original snapshot"
                    asset_links[key] = archive.name
                    plans.setdefault(archive.name, []).append({
                        "key": key, "sha256": missing[key],
                        "bytes": row["bytes"], "zip_crc32": info.CRC})
        if number % 20 == 0:
            print("N23 B13 absent-byte archive manifest mapping", number, "/", len(archives),
                  "located", len(asset_links), "/", len(missing), flush=True)
    for key in missing.keys()-asset_links.keys():
        failures.append({"key": key, "problem": "absent locally and from all transferred asset manifests"})
    archivebindings, archived = {}, 0
    with (output / "ARCHIVE-FILES.jsonl").open("x", encoding="ascii") as ledger:
        for name in sorted(plans):
            archive, meta_path = incoming / name, incoming / (name+".meta.json")
            meta = read(meta_path)
            assert archive.stat().st_size == meta["archive_bytes"]
            archivehash = digest(archive)
            assert archivehash == meta["sha256"]
            with zipfile.ZipFile(archive) as stream:
                manifesthash = hashlib.sha256()
                with stream.open("ASSET-MANIFEST.jsonl") as assets:
                    for block in iter(lambda: assets.read(1 << 20), b""):
                        manifesthash.update(block)
                for item in plans[name]:
                    key = item["key"]
                    info = stream.getinfo(key)
                    assert info.file_size == item["bytes"] and info.CRC == item["zip_crc32"]
                    result, size = hashlib.sha256(), 0
                    with stream.open(key) as source:
                        for block in iter(lambda: source.read(1 << 20), b""):
                            result.update(block)
                            size += len(block)
                    assert size == item["bytes"] and result.hexdigest() == item["sha256"]
                    ledger.write(json.dumps({"key": key, "archive": name, **item},
                                            separators=(",", ":"))+"\n")
                    archived += 1
                    if archived % 1000 == 0:
                        print("N23 B13 absent original bytes actually read from archive", archived,
                              "/", len(missing), flush=True)
            assert digest(archive) == archivehash
            archivebindings[name] = {
                "archive_sha256": archivehash, "archive_metadata_sha256": sha(meta_path),
                "asset_manifest_sha256": manifesthash.hexdigest()}
    assert sha(manifest) == EXPECTED_SNAPSHOT
    publish(output / "VERIFIED.json", {
        "verified": not failures,
        "schema": "n23-B13-original-all-snapshot-byte-integrity-current-roots-plus-archive-fallback-v1",
        "file_count": checked, "current_relocated_files_actually_hashed": local,
        "absent_files_actually_read_and_hashed_from_original_archives": archived,
        "all_original_bound_files_content_checked": local+archived == checked and not failures,
        "mismatches": failures, "original_snapshot_sha256": EXPECTED_SNAPSHOT,
        "original_roots": footer["roots"], "current_roots": {k: str(v) for k, v in roots.items()},
        "old_absolute_paths_and_E_registration_not_rewritten": True,
        "missing_files_not_falsely_claimed_present_in_recovered_current_roots": True,
        "local_ledger_sha256": sha(output / "LOCAL-FILES.jsonl"),
        "archive_ledger_sha256": sha(output / "ARCHIVE-FILES.jsonl"),
        "archive_bindings": archivebindings, "source_sha256": sha(Path(__file__)),
        "seconds": time.monotonic()-started,
        "scope": "all original B13 frozen proof bytes only; not fresh mathematical replay",
        "global_optimality_proved": False})
    print("N23 B13 original full snapshot current-root/archive bytes",
          "PASS" if not failures else "FAIL", checked, "local", local, "archive", archived,
          "differences", len(failures), flush=True)
    assert not failures


if __name__ == "__main__":
    main()
