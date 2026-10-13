"""Recover four exact historical N23 assets into a new isolated directory."""
from pathlib import Path
import argparse
import hashlib
import json
import zipfile

from n25_outer_search import read, publish
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("observation", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    observationpath, output = args.observation.resolve(), args.output.resolve()
    assert all(path.is_relative_to(ROOT) for path in (observationpath, output))
    assert not output.exists()
    observation = read(observationpath)
    assert observation["schema"] == "N23-nonstrict-core-prerequisite-central-directory-observation-v1"
    assert observation["source_sha256"] == sha(ROOT / "locate_n23_nonstrict_core_assets.py")
    base = "workspace/research-2026/n21-25-synthesis/"
    requested = {
        base+"round3-high/evidence/n23-core-angle-resume1/core-angle-tree.json.gz":
            ("core-angle-tree.json.gz", "940a589692067826b9c5db731a16c45515422735eaead95f4dc5e8f69f550f79"),
        base+"evidence/n23/local-isolation-certificate.json":
            ("local-isolation-certificate.json", "2dc2da7da348ce5e89f929394c0b07af494887d7a0c2187545bcb8b26d64cba5"),
        base+"evidence/n23/algebraic-check1/root-verified.json":
            ("root-verified.json", None),
        base+"evidence/n23/algebraic-check1/upper-verified.json":
            ("upper-verified.json", None),
    }
    rows = observation["matching_members"]
    assert len(rows) == 4 and {row["member"] for row in rows} == set(requested)
    incoming = ROOT.parents[4]
    assert incoming.name == "_incoming-local-math-20261004"
    assert {row["archive"] for row in rows} == {"math-delta-0022.zip", "math-delta-0052.zip"}
    contents, archives, records = {}, {}, []
    for archivename in sorted({row["archive"] for row in rows}):
        archivepath, metapath = incoming / archivename, incoming / (archivename+".meta.json")
        meta = read(metapath)
        digest = sha(archivepath)
        assert archivepath.stat().st_size == meta["archive_bytes"]
        assert digest == meta["sha256"]
        selected = [row for row in rows if row["archive"] == archivename]
        with zipfile.ZipFile(archivepath) as archive:
            manifestbytes = archive.read("ASSET-MANIFEST.jsonl")
            manifest = {}
            for line in manifestbytes.decode("utf8").splitlines():
                item = json.loads(line, object_pairs_hook=no_duplicate_keys)
                member = item["sourceRoot"]+"/"+item["path"]
                if member in requested:
                    assert member not in manifest
                    manifest[member] = item
            assert set(manifest) == {row["member"] for row in selected}
            for row in selected:
                member = row["member"]
                info, item = archive.getinfo(member), manifest[member]
                assert info.file_size == row["bytes"] == item["bytes"]
                assert info.CRC == row["zip_crc32"]
                value = archive.read(member)
                filehash = hashlib.sha256(value).hexdigest()
                assert len(value) == item["bytes"] and filehash == item["sha256"]
                targetname, historicalhash = requested[member]
                assert historicalhash is None or filehash == historicalhash
                assert targetname not in contents
                contents[targetname] = value
                records.append({"archive": archivename, "member": member,
                                "target": targetname, "bytes": len(value), "sha256": filehash})
        archives[str(archivepath)] = {
            "archive_sha256": digest, "metadata_sha256": sha(metapath),
            "asset_manifest_sha256": hashlib.sha256(manifestbytes).hexdigest(),
        }
    output.mkdir()
    frozen = {}
    for name, value in contents.items():
        target = output / name
        assert target.resolve().is_relative_to(output)
        with target.open("xb") as stream:
            stream.write(value)
        frozen[str(target)] = sha(target)
    rootreport, upperreport, isolation = (
        read(output / name) for name in ("root-verified.json", "upper-verified.json",
                                        "local-isolation-certificate.json"))
    original = ROOT / "n23-n24-archive-core-inputs-20261005-v1/n23"
    systempath, rootpath = original / "core-system.json", original / "core-root.json"
    assert rootreport["verified"] and upperreport["verified"] and isolation["verified"]
    assert rootreport["N"] == upperreport["N"] == isolation["N"] == 23
    assert rootreport["root_sha256"] == upperreport["root_sha256"] == isolation["root_sha256"] == sha(rootpath)
    assert rootreport["system_sha256"] == sha(systempath)
    for path in (Path(__file__), observationpath, ROOT / "locate_n23_nonstrict_core_assets.py",
                 systempath, rootpath, original.parent / "VERIFIED.json"):
        frozen[str(path.resolve())] = sha(path)
    for path, expected in frozen.items():
        assert sha(path) == expected
    for path, binding in archives.items():
        assert sha(path) == binding["archive_sha256"]
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "isolated-N23-nonstrict-core-exact-archive-assets-v1",
        "N": 23, "selected_members": records, "archive_bindings": archives,
        "original_tree_and_local_bytes_match_historical_replay_digests": True,
        "historical_reports_bind_actual_isolated_original_root_and_system": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "math_tree_root_and_local_prerequisites_not_replayed_by_byte_recovery": True,
        "not_a_complete_type_or_global_payment": True, "global_optimality_proved": False,
    })
    print("N23 historical nonstrict core exact byte recovery passed; four isolated assets;",
          "mathematical replay still required", flush=True)


if __name__ == "__main__":
    main()
