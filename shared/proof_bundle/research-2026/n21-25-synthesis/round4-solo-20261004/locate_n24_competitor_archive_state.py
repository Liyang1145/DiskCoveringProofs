"""Read historical archive names for N24 family source terminal/summary assets.

No historical success is inferred from directories or filenames. Selected
small JSON metadata is recorded as data for subsequent independent recovery.
"""
from pathlib import Path
from collections import Counter
import argparse
import json
import zipfile

from n25_outer_search import publish
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
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
    records, counts, scanned = [], Counter(), []
    for archivepath in archives:
        with zipfile.ZipFile(archivepath) as archive:
            infos = archive.infolist()
            selected = []
            for info in infos:
                lowered = info.filename.lower()
                if not any(f"n24-b{B}" in lowered for B in (13, 14, 15, 16)):
                    continue
                leaf = Path(info.filename).name.lower()
                if leaf not in (
                    "native-terminal.json", "native-launch.json", "search-complete.json",
                    "summary.json", "verified.json", "input-bindings.json",
                    "search-failed.json", "launch.json", "completion.json",
                ):
                    continue
                if any(part.startswith(("group-", "type-", "parent-", "sample-"))
                       for part in Path(lowered).parts):
                    continue
                selected.append(info)
            for info in selected:
                family = next(f"B{B}" for B in (13, 14, 15, 16)
                              if f"n24-b{B}" in info.filename.lower())
                row = {"archive": archivepath.name, "member": info.filename,
                       "family": family, "bytes": info.file_size, "zip_crc32": info.CRC}
                if info.file_size <= 2_000_000:
                    content = archive.read(info.filename)
                    try:
                        data = json.loads(content.decode("utf8"), object_pairs_hook=no_duplicate_keys)
                    except (ValueError, UnicodeError):
                        row["not_parseable_json"] = True
                    else:
                        row["metadata_fields"] = {key: value for key, value in data.items()
                            if type(value) in (str, int, bool, type(None))}
                        row["metadata_file_sha256"] = __import__("hashlib").sha256(content).hexdigest()
                records.append(row)
                counts[family] += 1
            scanned.append({"archive": archivepath.name, "members_scanned": len(infos)})
        if len(scanned) % 20 == 0:
            print("N24 competitor archive source-state scan", len(scanned), "/134;",
                  dict(counts), flush=True)
    output.mkdir()
    publish(output / "OBSERVATION.json", {
        "schema": "N24-historical-competitor-source-state-archive-observation-v1",
        "archives_scanned": scanned, "matching_source_metadata": records, "family_metadata_counts": dict(counts),
        "names_and_historical_metadata_not_new_native_terminals_or_completeness_proofs": True,
        "no_source_search_or_proof_job_restarted": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("N24 historical competitor source-state metadata found:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
