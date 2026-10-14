# SPDX-License-Identifier: MIT
"""Compare a frozen migration inventory with delivered content, without replaying math.

The SQLite input is opened read-only. Only a TEMP table is written. Matching is
by original SHA256, including the uncompressed digest of delivery gzip parts;
it does not imply that archived absolute paths have been relocated correctly.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sqlite3


def digest_file(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_path(value):
    if not isinstance(value, str) or not value or "\\" in value or ":" in value:
        raise ValueError("Invalid canonical inventory path")
    path = PurePosixPath(value)
    if not path.parts or path.is_absolute() or ".." in path.parts or path.as_posix() != value:
        raise ValueError("Invalid canonical inventory path")
    return value


def digest_value(value):
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value):
        raise ValueError("Invalid SHA256 in inventory")
    return value


def summarize(connection, role=None):
    condition = ""
    params = ()
    if role is not None:
        condition = " WHERE instr(',' || f.roles || ',', ?) > 0"
        params = ("," + role + ",",)
    row = connection.execute(
        "SELECT count(*), coalesce(sum(f.bytes),0), "
        "coalesce(sum(s.sha IS NOT NULL),0), "
        "coalesce(sum(CASE WHEN s.sha IS NULL THEN f.bytes ELSE 0 END),0) "
        "FROM files f LEFT JOIN shipped s ON f.sha256=s.sha" + condition,
        params,
    ).fetchone()
    return {
        "inventory_files": row[0],
        "inventory_bytes": row[1],
        "files_with_identical_delivered_content": row[2],
        "files_without_identical_delivered_content": row[0] - row[2],
        "bytes_without_identical_delivered_content": row[3],
    }


def audit(inventory, delivery, roles, report, closure_ledger=None):
    inventory, delivery = Path(inventory), Path(delivery)
    shipped = set()
    delivery_count = 0
    paths = set()
    with delivery.open(encoding="utf-8") as stream:
        for line in stream:
            entry = json.loads(line)
            path = canonical_path(entry["path"])
            if path in paths:
                raise ValueError("Duplicate delivery path")
            paths.add(path)
            shipped.add(digest_value(entry["sha256"]))
            delivery_count += 1
    if not delivery_count:
        raise ValueError("Empty delivery manifest")
    connection = sqlite3.connect(inventory.resolve().as_uri() + "?mode=ro", uri=True)
    try:
        connection.execute("CREATE TEMP TABLE shipped(sha TEXT PRIMARY KEY)")
        connection.executemany("INSERT INTO shipped VALUES (?)", ((s,) for s in shipped))
        union = summarize(connection)
        if not union["inventory_files"]:
            raise ValueError("Empty source inventory")
        summary = {
            "schema": "disk-covering-replay-inventory-audit-v1",
            "mode": "manifest-content-comparison",
            "mathematical_replay": False,
            "fresh_full_local_file_hash_audit": False,
            "source_inventory_declarations_are_input": True,
            "matching_rule": "original SHA256 content, regardless of repository path",
            "correct_runtime_path_layout_established": False,
            "inventory_sqlite_sha256": digest_file(inventory),
            "delivery_manifest_sha256": digest_file(delivery),
            "delivered_logical_files": delivery_count,
            "union": union,
            "roles": {role: summarize(connection, role) for role in roles},
            "migration_status_counts": dict(connection.execute(
                "SELECT status,count(*) FROM files GROUP BY status ORDER BY status"
            )),
            "notes": [
                "Role counts may overlap; sum the union, not the per-order rows.",
                "A shared digest is counted for every corresponding inventory path.",
                "This checks inventory declarations; it does not reread all source assets.",
                "Missing content, runtime relocation, and mathematical obligations are separate.",
            ],
        }
        if closure_ledger:
            target = Path(closure_ledger)
            target.parent.mkdir(parents=True, exist_ok=True)
            count = 0
            with gzip.open(target, "wt", encoding="utf-8", newline="\n") as stream:
                for canonical, sha, size, role in connection.execute(
                    "SELECT canonical,sha256,bytes,roles FROM files ORDER BY canonical"
                ):
                    if not isinstance(size, int) or size < 0:
                        raise ValueError("Invalid inventory size")
                    entry = {"canonical": canonical_path(canonical),
                             "sha256": digest_value(sha), "bytes": size, "roles": role}
                    stream.write(json.dumps(entry, ensure_ascii=False, separators=(",", ":")) + "\n")
                    count += 1
            if count != union["inventory_files"]:
                raise ValueError("Closure ledger count mismatch")
            summary["closure_ledger"] = {
                "name": target.name, "encoding": "gzip-jsonl",
                "files": count, "sha256": digest_file(target), "bytes": target.stat().st_size,
                "contains_source_machine_paths": False,
            }
        target = Path(report)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        return summary
    finally:
        connection.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", required=True, type=Path,
                        help="read-only migration SQLite with files(canonical,sha256,bytes,roles,status)")
    parser.add_argument("--delivery", type=Path,
                        default=Path(__file__).resolve().parents[1] / "manifests/FILES.jsonl")
    parser.add_argument("--roles", nargs="+", default=["n23", "n24", "n25"])
    parser.add_argument("--report", type=Path, default=Path("build/replay-inventory.json"))
    parser.add_argument("--closure-ledger", type=Path,
                        help="optional complete canonical JSONL gzip for export; contains no old source paths")
    args = parser.parse_args()
    try:
        summary = audit(args.inventory, args.delivery, args.roles, args.report, args.closure_ledger)
    except (OSError, ValueError, KeyError, sqlite3.Error) as error:
        parser.exit(1, "INVENTORY AUDIT FAILED: " + str(error) + "\n")
    union = summary["union"]
    print(f"Inventory files: {union['inventory_files']}; "
          f"without delivered identical content: {union['files_without_identical_delivered_content']}; "
          f"bytes: {union['bytes_without_identical_delivered_content']}")
    print("Manifest comparison only; not a fresh file audit or mathematical replay.")


if __name__ == "__main__":
    main()
