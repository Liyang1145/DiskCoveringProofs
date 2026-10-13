"""Locate actual N23 B14/B15 datasets by ZIP names; no extraction/acceptance."""
from pathlib import Path
import argparse
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    incoming = ROOT.parents[4]
    assert incoming.name == "_incoming-local-math-20261004"
    archives = sorted(incoming.glob("math-delta-*.zip"))
    assert len(archives) == 134
    matches, scans = [], []
    for archive in archives:
        with zipfile.ZipFile(archive) as stream:
            count = 0
            for info in stream.infolist():
                count += 1
                member = info.filename.replace("\\", "/")
                low = member.lower()
                if "n23-b15" not in low and "n23-b14" not in low:
                    continue
                name = member.split("/")[-1]
                # Per-group proof trees can be recovered later against the
                # actual accepted receipt; first locate catalogs and maps.
                if name.startswith("group-") and name.endswith(".json.gz"):
                    continue
                matches.append({
                    "archive": archive.name, "member": member,
                    "bytes": info.file_size, "compressed_bytes": info.compress_size,
                    "zip_crc32": info.CRC, "names_only_not_byte_or_proof_acceptance": True,
                })
        scans.append({"archive": archive.name, "members_scanned": count})
        if len(scans) % 20 == 0:
            print("N23 family asset location:", len(scans), "/", len(archives),
                  "; dataset/metadata names", len(matches), flush=True)
    output.mkdir()
    publish(output / "OBSERVATION.json", {
        "schema": "N23-B14-B15-family-archive-name-observation-v1",
        "archives_scanned": scans, "matching_members": matches,
        "group_proof_trees_intentionally_not_listed_yet": True,
        "no_archive_extracted_or_existing_file_modified": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("N23 family archive name search finished:", len(matches),
          "names; no extraction; no completeness or proof acceptance", flush=True)


if __name__ == "__main__":
    main()
