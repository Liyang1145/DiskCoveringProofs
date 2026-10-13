"""Discover weak graph proposals across archived n25/B14 run prefixes.

Only the first row of each run is read. This is deliberately NOT a full-file
integrity check, run acceptance, unique catalogue, or completeness proof.
Later exact graph theorems do not trust this discovery input.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import struct
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from group_catalog import canonical
from audit_streamed_hierarchy import check_map
from stream_catalog import sha

INCOMING = ROOT.parents[4]
PREFIX = "bulk/n25-B14-pair-search-prefix-replay-resume1/N25-B14-pair-search.bin.runs/"
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    codes, counts, sources = {}, Counter(), []
    bindingpath = args.output / "bindings.jsonl"
    samplepath = args.output / "sample-full-graphs.jsonl"
    with bindingpath.open("x", encoding="utf8") as bindings, samplepath.open("x", encoding="utf8") as raw:
        for archive in sorted(INCOMING.glob("math-delta-*.zip")):
            with zipfile.ZipFile(archive) as zf:
                for info in zf.infolist():
                    if not info.filename.startswith(PREFIX):
                        continue
                    with zf.open(info) as stream:
                        header = stream.read(28)
                        assert len(header) == 28 and header[:8] == b"PAIDRUN1"
                        n, b, facecount, rows = struct.unpack("<IIIQ", header[8:])
                        assert (n, b, facecount) == (25, 14, 34) and 0 < rows <= 100000
                        payload = stream.read(4 * (facecount + 1))
                        if len(payload) != 4 * (facecount + 1):
                            continue
                    values = struct.unpack("<" + "I" * (facecount + 1), payload)
                    stabilizer, masks = values[0], list(values[1:])
                    assert stabilizer > 0 and 28 % stabilizer == 0
                    assert masks == sorted(set(masks)) and all(m.bit_count() == 3 and m < 1 << 25 for m in masks)
                    code, mapping = canonical(25, 14, masks, 1)
                    gid = codes.setdefault(code, len(codes))
                    centers = max(m.bit_length() for m in code)
                    check_map(25, 14, {"centers": centers, "faces": list(code)}, mapping, set(masks), 1)
                    index = len(sources)
                    origin = {"archive": archive.name, "entry": info.filename,
                              "record": 0, "prefix_sha256": hashlib.sha256(header + payload).hexdigest(),
                              "whole_run_bytes_not_read_or_verified": True}
                    sources.append(origin)
                    counts[gid] += 1
                    bindings.write(json.dumps({"index": index, "group": gid, "map": mapping}, separators=(",", ":")) + "\n")
                    raw.write(json.dumps({"index": index, "faces": masks, "source": origin}, separators=(",", ":")) + "\n")
            if sources:
                print(archive.name, "sampled run rows", len(sources), "distinct outer proposals", len(codes), flush=True)
    groups = [None] * len(codes)
    for code, gid in codes.items():
        groups[gid] = {"id": gid, "faces": list(code), "centers": max(m.bit_length() for m in code), "members": counts[gid]}
    report = {
        "N": 25, "B": 14, "threshold": 1, "groups": groups, "group_count": len(groups),
        "selected_types": len(sources), "catalog_types": len(sources),
        "catalog_sha256": sha(samplepath), "bindings_file": bindingpath.name,
        "bindings_sha256": sha(bindingpath), "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": False, "parent_groups_sha256": None,
        "parent_proof_sha256": None, "source_sha256": sha(Path(__file__)),
        "canonicalizer_sha256": sha(HIGH / "group_catalog.py"),
        "mapping_acceptor_sha256": sha(HIGH / "audit_streamed_hierarchy.py"),
        "sample_records_not_catalogue_types": True, "not_a_complete_family": True,
        "full_archived_run_integrity_not_checked": True, "global_optimality_proved": False,
        "scope": "graph proposals only; exact accepting path must reprove each graph independently of discovery",
    }
    (args.output / "GROUPS.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N25/B14 proposal inventory:", len(sources), "rows;", len(groups), "weak graphs; no catalogue claim", flush=True)


if __name__ == "__main__":
    main()
