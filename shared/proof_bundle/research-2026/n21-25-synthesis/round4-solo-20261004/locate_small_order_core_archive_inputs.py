"""Read ZIP central directories for missing N23/N24 inputs; do not extract."""
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
    matches, scanned = [], []
    for archive in archives:
        count = 0
        with zipfile.ZipFile(archive) as stream:
            for member in stream.infolist():
                count += 1
                name = member.filename.replace("\\", "/")
                folded = name.lower()
                if any(f"/evidence/n{N}/" in folded for N in (23, 24)) and (
                        folded.endswith("/core-system.json") or folded.endswith("/core-root.json")
                        or folded.endswith("/candidate-numeric.json") or folded.endswith("/kkt-numeric.json")):
                    assert not name.startswith("/") and ".." not in Path(name).parts
                    matches.append({"archive": archive.name, "member": name,
                                    "bytes": member.file_size, "zip_crc32": member.CRC,
                                    "central_directory_only_not_content_or_mathematical_acceptance": True})
        scanned.append({"archive": archive.name, "central_directory_members_scanned": count})
        if len(scanned) % 20 == 0:
            print("Missing small-order core archive search:", len(scanned), "/", len(archives),
                  "; matching names", len(matches), flush=True)
    output.mkdir()
    publish(output / "OBSERVATION.json", {
        "schema": "small-order-core-input-archive-central-directory-observation-v1",
        "incoming_root": str(incoming), "archives_scanned": scanned, "matching_members": matches,
        "no_archive_extracted_and_no_existing_math_file_changed": True,
        "zip_member_names_not_byte_or_mathematical_proof_acceptance": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("Small-order core archive name search finished:", len(archives),
          "central directories;", len(matches), "matching members; no extraction", flush=True)


if __name__ == "__main__":
    main()
