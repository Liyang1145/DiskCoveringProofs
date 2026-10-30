#!/usr/bin/env python3
"""Search every local JSON/JSONL document for the 382 missing energy payloads.

This is a repository-local inventory check, not a HOST export and not a proof.
It excludes this lane's generated reports so a prior failure listing cannot
masquerade as a recovered payload.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
CENSUS = HERE / "residual389-census.json"
OUT = HERE / "residual-repository-payload-audit.json"


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


def is_payload(obj):
    keys = set(obj)
    return ("g" in keys and "f0Lo" in keys and
            bool(keys & {"beta", "y", "weights", "support"}))


def main():
    census = json.loads(CENSUS.read_text())
    residual = set(census["residual_ids"])
    files = []
    oversized = []
    max_bytes = 2_000_000
    search_roots = [ROOT / "n11-work", ROOT / "build"]
    for path in (p for base in search_roots for p in base.rglob("*")):
        if not path.is_file() or path.suffix not in {".json", ".jsonl"}:
            continue
        rel = path.relative_to(ROOT)
        if rel.parts[:4] == ("n11-work", "ops", "lanes", "C"):
            continue
        if path.stat().st_size > max_bytes:
            oversized.append({"file": str(rel), "bytes": path.stat().st_size})
        else:
            files.append(path)
    files.sort()
    oversized.sort(key=lambda item: item["file"])

    hits = []
    parse_errors = []
    scanned_bytes = 0
    for path in files:
        scanned_bytes += path.stat().st_size
        try:
            for document in documents(path):
                for obj in walk(document):
                    node_id = obj.get("id")
                    if isinstance(node_id, int) and node_id in residual:
                        hits.append({
                            "id": node_id,
                            "file": str(path.relative_to(ROOT)),
                            "keys": sorted(obj),
                            "payload": is_payload(obj),
                        })
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            parse_errors.append({
                "file": str(path.relative_to(ROOT)),
                "error": str(exc),
            })

    payload_ids = sorted({hit["id"] for hit in hits if hit["payload"]})
    if payload_ids:
        raise AssertionError(f"unexpected repository payload ids: {payload_ids}")

    result = {
        "scope": ("all n11-work/build JSON/JSONL outside ops/lanes/C, files <=2MB; "
                  "not HOST storage and not a proof"),
        "source_sha256": {"residual389-census.json": sha256(CENSUS)},
        "scanned_file_count": len(files),
        "scanned_bytes": scanned_bytes,
        "oversized_file_count": len(oversized),
        "oversized_files": oversized,
        "parse_error_count": len(parse_errors),
        "parse_errors": parse_errors,
        "residual_object_hit_count": len(hits),
        "recovered_payload_count": len(payload_ids),
        "recovered_payload_ids": payload_ids,
        "missing_payload_count": len(residual),
        "missing_payload_ids_sha256": hashlib.sha256(
            ",".join(map(str, sorted(residual))).encode()).hexdigest(),
    }
    OUT.write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps(result, indent=1))


if __name__ == "__main__":
    main()
