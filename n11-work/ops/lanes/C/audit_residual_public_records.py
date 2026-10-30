#!/usr/bin/env python3
"""Audit public/restored WIP JSON assets for the 389 residual cell records.

This does not prove any energy cell.  It distinguishes a missing host record
from a record that was merely not searched by the original next-512 census.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
CENSUS = HERE / "residual389-census.json"
OUT = HERE / "residual-public-record-audit.json"
SEARCH_ROOTS = [
    ROOT / "n11-work/evidence-20261014",
    ROOT / "n11-work/evidence-20261028",
    ROOT / "build/n11-wip/assets/evidence",
]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def documents(path):
    text = path.read_text(encoding="utf-8-sig")
    if path.suffix == ".jsonl":
        for line in text.splitlines():
            if line.strip():
                yield json.loads(line)
    else:
        yield json.loads(text)


def main():
    census = json.loads(CENSUS.read_text())
    residual = set(census["residual_ids"])
    files = sorted({path for base in SEARCH_ROOTS if base.exists()
                    for path in base.rglob("*")
                    if path.is_file() and path.suffix in {".json", ".jsonl"}})
    hits = []
    scanned_bytes = 0
    for path in files:
        scanned_bytes += path.stat().st_size
        for document in documents(path):
            for obj in walk(document):
                node_id = obj.get("id")
                if isinstance(node_id, int) and node_id in residual:
                    keys = sorted(obj)
                    hits.append({
                        "id": node_id,
                        "file": str(path.relative_to(ROOT)),
                        "keys": keys,
                        "has_g": "g" in obj,
                        "has_f0Lo": "f0Lo" in obj,
                        "has_mixture_data": any(
                            "weight" in key.lower() or key in {"y", "beta", "support"}
                            for key in keys),
                    })

    payload_hits = [hit for hit in hits
                    if hit["has_g"] and hit["has_f0Lo"] and hit["has_mixture_data"]]
    payload_ids = sorted({hit["id"] for hit in payload_hits})
    expected = sorted(census["local_survey_records"][i]["id"]
                      for i in range(len(census["local_survey_records"])))
    payload_files = sorted({hit["file"] for hit in payload_hits})

    assert expected == [1409, 2337, 2341, 2356, 2360, 2368, 2370]
    assert payload_ids == expected, payload_ids
    assert payload_files == ["n11-work/evidence-20261028/inputs/paid16-general-next512.json"]
    assert len(payload_hits) == 7

    result = {
        "scope": "JSON/JSONL public and restored n11 WIP evidence only; not HOST storage and not a proof",
        "search_roots": [str(base.relative_to(ROOT)) for base in SEARCH_ROOTS if base.exists()],
        "scanned_file_count": len(files),
        "scanned_bytes": scanned_bytes,
        "residual_id_object_hits": len(hits),
        "core_payload_record_count": len(payload_hits),
        "core_payload_ids": payload_ids,
        "core_payload_files": payload_files,
        "missing_core_payload_records": sorted(residual - set(payload_ids)),
        "missing_core_payload_count": len(residual) - len(payload_ids),
        "source_sha256": {
            "residual389-census.json": sha256(CENSUS),
            "paid16-general-next512.json": sha256(
                ROOT / "n11-work/evidence-20261028/inputs/paid16-general-next512.json"),
        },
    }
    OUT.write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps({key: value for key, value in result.items()
                      if key != "missing_core_payload_records"}, indent=1))


if __name__ == "__main__":
    main()
