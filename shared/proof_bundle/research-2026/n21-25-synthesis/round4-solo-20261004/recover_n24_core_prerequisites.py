"""Isolate exact historical N24 core assets; byte recovery is not a proof."""
from pathlib import Path
import argparse
import hashlib
import json
import zipfile

from n25_outer_search import read, publish
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    incoming = ROOT.parents[4]
    assert incoming.name == "_incoming-local-math-20261004"
    historicalpath = HIGH / "evidence/n24-core-replay-stdlib-resume1.json"
    historical = read(historicalpath)
    assert historical["verified"] and (historical["N"], historical["B"]) == (24, 15)
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n24.json"
    constants = read(constants_path)
    assert constants["verified"] and constants["N"] == 24
    prefix = "workspace/research-2026/n21-25-synthesis/"
    requested = {
        prefix+"round3-high/evidence/n24-core-angle-resume2/core-angle-tree.json.gz":
            ("core-angle-tree.json.gz", historical["tree_sha256"]),
        prefix+"evidence/n24/local-isolation-certificate.json":
            ("local-isolation-certificate.json", historical["local_certificate_sha256"]),
        prefix+"evidence/n24/algebraic-check1/root-verified.json":
            ("root-verified.json", constants["radius_root_report_sha256"]),
        prefix+"evidence/n24/algebraic-check1/upper-verified.json":
            ("upper-verified.json", None),
    }
    archives = sorted(incoming.glob("math-delta-*.zip"))
    assert len(archives) == 134
    matches, scanned = [], []
    for archivepath in archives:
        with zipfile.ZipFile(archivepath) as archive:
            infos = archive.infolist()
            for info in infos:
                if info.filename in requested:
                    matches.append({
                        "archive": archivepath.name, "member": info.filename,
                        "bytes": info.file_size, "zip_crc32": info.CRC,
                    })
            scanned.append({"archive": archivepath.name, "members_scanned": len(infos)})
        if len(scanned) % 20 == 0:
            print("N24 exact prerequisite archive-name scan", len(scanned), "/134", flush=True)
    assert len(matches) == 4 and {row["member"] for row in matches} == set(requested)
    output.mkdir()
    publish(output / "ARCHIVE-NAMES.json", {
        "N": 24, "archives_scanned": scanned, "matching_members": matches,
        "source_sha256": sha(Path(__file__)), "no_math_payment_by_archive_listing": True,
    })
    contents, archivebindings, selected = {}, {}, []
    frozen = {}
    for archivename in sorted({row["archive"] for row in matches}):
        archivepath = incoming / archivename
        metapath = incoming / (archivename+".meta.json")
        metadata = read(metapath)
        digest = sha(archivepath)
        assert archivepath.stat().st_size == metadata["archive_bytes"]
        assert digest == metadata["sha256"]
        rows = [row for row in matches if row["archive"] == archivename]
        with zipfile.ZipFile(archivepath) as archive:
            manifestbytes = archive.read("ASSET-MANIFEST.jsonl")
            manifest = {}
            for line in manifestbytes.decode("utf8").splitlines():
                item = json.loads(line, object_pairs_hook=no_duplicate_keys)
                member = item["sourceRoot"]+"/"+item["path"]
                if member in requested:
                    assert member not in manifest
                    manifest[member] = item
            assert set(manifest) == {row["member"] for row in rows}
            for row in rows:
                member = row["member"]
                info, item = archive.getinfo(member), manifest[member]
                assert info.file_size == row["bytes"] == item["bytes"]
                assert info.CRC == row["zip_crc32"]
                value = archive.read(member)
                filehash = hashlib.sha256(value).hexdigest()
                assert len(value) == item["bytes"] and filehash == item["sha256"]
                targetname, expectedhash = requested[member]
                assert expectedhash is None or filehash == expectedhash
                assert targetname not in contents
                contents[targetname] = value
                selected.append({
                    "archive": archivename, "member": member, "target": targetname,
                    "bytes": len(value), "sha256": filehash,
                })
        archivebindings[str(archivepath)] = {
            "archive_sha256": digest, "metadata_sha256": sha(metapath),
            "asset_manifest_sha256": hashlib.sha256(manifestbytes).hexdigest(),
        }
        frozen[str(metapath)] = sha(metapath)
    for name, value in contents.items():
        target = output / name
        assert target.resolve().is_relative_to(output)
        with target.open("xb") as stream:
            stream.write(value)
        frozen[str(target)] = sha(target)
    inputs = ROOT / "n23-n24-archive-core-inputs-20261005-v1"
    folder = inputs / "n24"
    systempath, rootpath = folder / "core-system.json", folder / "core-root.json"
    rootreport, upperreport, local = map(read, (
        output / "root-verified.json", output / "upper-verified.json",
        output / "local-isolation-certificate.json"))
    assert rootreport["verified"] and upperreport["verified"] and local["verified"]
    assert rootreport["N"] == upperreport["N"] == local["N"] == 24
    assert rootreport["root_sha256"] == upperreport["root_sha256"] == local["root_sha256"] == sha(rootpath)
    assert rootreport["system_sha256"] == sha(systempath)
    assert local["geometry_dimension"] == local["positive_leading_principal_minors"] == 114
    for path in (Path(__file__), historicalpath, constants_path, systempath, rootpath,
                 inputs / "VERIFIED.json", output / "ARCHIVE-NAMES.json"):
        frozen[str(path.resolve())] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    for path, binding in archivebindings.items():
        assert sha(path) == binding["archive_sha256"]
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "isolated-N24-core-exact-archive-assets-v1",
        "N": 24, "B": 15, "selected_members": selected,
        "archive_bindings": archivebindings, "frozen_files": frozen,
        "original_tree_local_and_root_report_match_historical_bound_digests": True,
        "isolated_reports_bound_to_actual_recovered_original_root_and_system": True,
        "original_default_evidence_paths_not_created_or_overwritten": True,
        "mathematical_root_upper_isolation_and_angle_replay_still_required": True,
        "not_a_complete_type_or_global_payment": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("N24 four exact original core assets isolated; mathematical replay still required", flush=True)


if __name__ == "__main__":
    main()
