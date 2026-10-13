"""Locate and exactly recover final B13 metadata without rewriting old C/E paths."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import shutil
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish

assert __debug__
FINAL_NAMES = {
    "N23-B13-CATALOGUE-SNAPSHOT-cross-volume-resume1.json",
    "n23-B13-full-disjoint-replayed-union-resume1.json",
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    incoming = ROOT.parents[4]
    archives = sorted(incoming.glob("math-delta-*.zip"))
    assert len(archives) == 134
    selected, observed = {}, []
    for number, archive in enumerate(archives, 1):
        with zipfile.ZipFile(archive) as stream:
            for info in stream.infolist():
                p = PurePosixPath(info.filename)
                assert not p.is_absolute() and ".." not in p.parts
                if "n23-b13" not in info.filename.lower():
                    continue
                if p.name.startswith("group-") and p.name.endswith(".json.gz"):
                    continue
                observed.append({"archive": archive.name, "member": info.filename,
                                 "bytes": info.file_size, "zip_crc32": info.CRC})
                if p.name in FINAL_NAMES:
                    assert p.name not in selected, "ambiguous duplicate final metadata"
                    selected[p.name] = (archive, info.filename, info.file_size, info.CRC)
        if number % 20 == 0:
            print("B13 final metadata central directories", number, "/", len(archives),
                  "selected", len(selected), flush=True)
    output.mkdir()
    publish(output / "OBSERVATION.json", {
        "all_archive_central_directories_scanned": len(archives),
        "matching_non_tree_names": observed, "selected_names_found": sorted(selected),
        "names_only_not_integrity_or_mathematical_acceptance": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    assert set(selected) == FINAL_NAMES, "missing final metadata; do not invent a snapshot"
    total = sum(item[2] for item in selected.values())
    assert total < 2*1024**3 and shutil.disk_usage(ROOT).free > total+15*1024**3
    recovered, archivebindings = [], {}
    for name in sorted(selected):
        archive, member, size, crc = selected[name]
        meta_path = incoming / (archive.name+".meta.json")
        meta = read(meta_path)
        assert archive.stat().st_size == meta["archive_bytes"]
        archivehash = sha(archive)
        assert archivehash == meta["sha256"]
        with zipfile.ZipFile(archive) as stream:
            manifestbytes = stream.read("ASSET-MANIFEST.jsonl")
            expected = None
            for line in manifestbytes.decode("utf8").splitlines():
                entry = json.loads(line, object_pairs_hook=no_duplicate_keys)
                if entry["sourceRoot"]+"/"+entry["path"] == member:
                    assert expected is None
                    expected = entry
            assert expected is not None and expected["bytes"] == size
            info = stream.getinfo(member)
            assert info.file_size == size and info.CRC == crc
            target = output / name
            digest, count = hashlib.sha256(), 0
            with stream.open(member) as source, target.open("xb") as destination:
                for block in iter(lambda: source.read(1 << 20), b""):
                    destination.write(block)
                    digest.update(block)
                    count += len(block)
            assert count == size and digest.hexdigest() == expected["sha256"] == sha(target)
        assert sha(archive) == archivehash
        archivebindings[archive.name] = {
            "archive_sha256": archivehash, "archive_metadata_sha256": sha(meta_path),
            "asset_manifest_sha256": hashlib.sha256(manifestbytes).hexdigest()}
        recovered.append({"member": member, "file": target.name,
                          "bytes": size, "sha256": sha(target)})
        print("B13 original final metadata recovered byte-for-byte:", name, size, flush=True)
    snapshotpath = output / "N23-B13-CATALOGUE-SNAPSHOT-cross-volume-resume1.json"
    assert sha(snapshotpath) == "64578536865f5078df43decda920f9043468f4fc35f1457bdf8cd0af6a8f6f79"
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "isolated-n23-B13-final-metadata-byte-recovery-v1",
        "selected_members": recovered, "archive_bindings": archivebindings,
        "original_absolute_paths_retained_unchanged": True,
        "all_snapshot_bound_files_current_integrity_still_required": True,
        "not_a_new_mathematical_replay_or_global_proof": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})


if __name__ == "__main__":
    main()
