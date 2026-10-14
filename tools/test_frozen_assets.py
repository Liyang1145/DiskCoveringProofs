# SPDX-License-Identifier: MIT
"""Small rejection controls for frozen byte export and inventory comparison.

Run with either python or python -O. Temporary fixtures contain no proof data;
the tests never change the delivered evidence or the migration database.
"""
import gzip
from contextlib import closing
import hashlib
import json
from pathlib import Path
import os
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import warnings
import zipfile

import audit_replay_inventory as inventory
import export_frozen_assets as exporter
import restore_frozen_assets as restorer


TOOLS = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


class ExportControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="frozen-export-controls-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.assets = self.root / "空 格 source assets"
        self.assets.mkdir()
        self.ledger = self.root / "ledger.jsonl"
        self.output = self.root / "export"
        self.payload = b"frozen exact bytes\r\n"
        (self.assets / "a.bin").write_bytes(self.payload)
        self.row = {"canonical": "a.bin", "sha256": sha(self.payload), "bytes": len(self.payload)}

    def rows(self, rows, compressed=False):
        body = "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows).encode("utf-8")
        if compressed:
            self.ledger = self.root / "ledger.jsonl.gz"
            self.ledger.write_bytes(gzip.compress(body, mtime=0))
        else:
            self.ledger.write_bytes(body)

    def run_export(self, success, *extra, mapping=False):
        environment = os.environ.copy()
        environment["PYTHONDONTWRITEBYTECODE"] = "1"
        environment["PYTHONIOENCODING"] = "utf-8"
        command = [sys.executable, "-O", str(TOOLS / "export_frozen_assets.py"),
                   "--ledger", str(self.ledger), "--output", str(self.output)]
        if not mapping:
            command += ["--asset-root", str(self.assets)]
        result = subprocess.run(command + list(extra), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                encoding="utf-8", env=environment, timeout=15, check=False)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        report = json.loads((self.output / "SUMMARY.json").read_text(encoding="utf-8"))
        self.assertEqual(report["complete"], success)
        self.assertEqual(report["mathematical_verification"], "not_performed")
        if not success:
            self.assertFalse(report["publishable_bundle"])
            self.assertFalse((self.output / "PACKAGES.json").exists())
            self.assertEqual(list(self.output.glob("*.zip")), [])
        return report

    def test_compressed_ledger_multipart_round_trip(self):
        payloads = {"a.bin": self.payload, "子目录/β.bin": b"second bytes\n", "z.bin": b"z" * 11}
        for name, data in payloads.items():
            file = self.assets / name
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_bytes(data)
        # A file outside the frozen selection is deliberately not exported.
        (self.assets / "unlisted-secret.txt").write_text("never select this", encoding="utf-8")
        self.rows([{"canonical": name, "sha256": sha(data), "bytes": len(data)}
                   for name, data in payloads.items()], compressed=True)
        report = self.run_export(True, "--max-package-bytes", "25",
                                 "--ledger-sha256", sha(self.ledger.read_bytes()))
        packages = json.loads((self.output / "PACKAGES.json").read_text(encoding="utf-8"))
        self.assertTrue(packages["complete"])
        self.assertGreater(len(packages["packages"]), 1)
        portable = self.output / packages["files_manifest"]["file"]
        self.assertEqual(sha(portable.read_bytes()), packages["files_manifest"]["sha256"])
        self.assertEqual(report["verified_files"], len(payloads))
        restored = {}
        for item in packages["packages"]:
            file = self.output / item["file"]
            self.assertEqual(sha(file.read_bytes()), item["sha256"])
            self.assertEqual(file.stat().st_size, item["bytes"])
            self.assertLessEqual(item["uncompressed_bytes"], 25)
            with zipfile.ZipFile(file) as archive:
                for name in archive.namelist():
                    self.assertTrue(name.startswith("assets/"))
                    self.assertNotIn(name, restored)
                    restored[name] = archive.read(name)
        self.assertEqual(restored, {"assets/" + name: data for name, data in payloads.items()})
        with gzip.open(portable, "rt", encoding="utf-8") as stream:
            entries = [json.loads(line) for line in stream]
        self.assertEqual({row["canonical"] for row in entries}, set(payloads))
        self.assertFalse(any(path.name.startswith(".staging-") for path in self.output.iterdir()))

    def test_windows_controls_explicit_longest_root_unicode_spaces(self):
        nested = self.assets / "嵌 套"
        nested.mkdir()
        (nested / "证明.txt").write_bytes(self.payload)
        root_map = self.root / "roots.json"
        root_map.write_text(json.dumps({"roots": [
            {"original": "C:\\SERVER\\work", "local": str(self.assets), "namespace": "work"},
            {"original": "C:\\server\\work\\deep", "local": str(nested), "namespace": "selected/deep"},
        ]}, ensure_ascii=False), encoding="utf-8")
        self.ledger.write_text(json.dumps({"accepted": True, "input_sha256": {
            "c:\\Server\\work\\deep\\证明.txt": sha(self.payload)
        }}, ensure_ascii=False, indent=2), encoding="utf-8")
        self.run_export(True, "--root-map", str(root_map), mapping=True)
        with zipfile.ZipFile(next(self.output.glob("*.zip"))) as archive:
            self.assertEqual(archive.namelist(), ["assets/selected/deep/证明.txt"])
            self.assertEqual(archive.read(archive.namelist()[0]), self.payload)

    def test_explicit_windows_and_wsl_aliases_share_canonical_asset(self):
        root_map = self.root / "roots.json"
        root_map.write_text(json.dumps({"roots": [
            {"original": "C:\\old\\work", "local": str(self.assets), "namespace": "n26/work"},
            {"original": "/mnt/c/old/work", "local": str(self.assets), "namespace": "n26/work"},
        ]}), encoding="utf-8")
        self.ledger.write_text(json.dumps({"input_sha256": {
            "C:\\old\\work\\a.bin": sha(self.payload),
            "/mnt/c/old/work/a.bin": sha(self.payload),
        }}), encoding="utf-8")
        report = self.run_export(True, "--root-map", str(root_map), "--audit-only", mapping=True)
        self.assertEqual(report["ledger_rows"], 2)
        self.assertEqual(report["duplicate_rows"], 1)
        self.assertEqual(report["verified_files"], 1)

    def test_missing_file_rejected(self):
        self.rows([dict(self.row, canonical="missing.bin")])
        self.assertEqual(self.run_export(False)["errors"], {"missing": 1})

    def test_hash_mismatch_and_acceptance_flag_rejected(self):
        self.rows([dict(self.row, sha256="0" * 64, accepted=True)])
        self.assertEqual(self.run_export(False)["errors"], {"hash_mismatch": 1})

    def test_wrong_size_rejected(self):
        self.rows([dict(self.row, bytes=1)])
        self.assertEqual(self.run_export(False)["errors"], {"size_mismatch": 1})

    def test_unsafe_canonical_paths_rejected_before_open(self):
        for name in ("../escape", "/absolute", "a/../escape", "a//b", "a/./b",
                     "C:/escape", "a\\b", ".", "CON.txt", "a/b ", "a/b."):
            with self.subTest(name=name):
                with self.assertRaises(exporter.Rejected):
                    exporter.safe_relative(name)
        self.rows([dict(self.row, canonical="../escape")])
        self.assertEqual(self.run_export(False)["errors"], {"unsafe_path": 1})

    def test_windows_traversal_rejected(self):
        mapping = self.root / "roots.json"
        mapping.write_text(json.dumps({"roots": [{"original": "C:\\old\\work",
                                                 "local": str(self.assets), "namespace": "work"}]}),
                           encoding="utf-8")
        self.rows([{"path": "C:\\old\\work\\..\\a.bin", "sha256": sha(self.payload)}])
        self.assertEqual(self.run_export(False, "--root-map", str(mapping), mapping=True)["errors"],
                         {"unsafe_path": 1})

    def test_unmapped_and_prefix_sibling_rejected(self):
        mapping = self.root / "roots.json"
        mapping.write_text(json.dumps({"roots": [{"original": "C:\\old\\work",
                                                 "local": str(self.assets), "namespace": "work"}]}),
                           encoding="utf-8")
        self.rows([{"path": "C:\\old\\worker\\a.bin", "sha256": sha(self.payload)}])
        self.assertEqual(self.run_export(False, "--root-map", str(mapping), mapping=True)["errors"],
                         {"unmapped": 1})

    def test_conflicting_duplicate_rejected(self):
        self.rows([self.row, dict(self.row, sha256="0" * 64)])
        report = self.run_export(False)
        self.assertEqual(report["errors"], {"conflict": 1})
        self.assertEqual(report["verified_files"], 1)

    def test_case_collision_rejected(self):
        self.rows([self.row, dict(self.row, canonical="A.bin")])
        self.assertEqual(self.run_export(False)["errors"], {"conflict": 1})

    def test_identical_duplicate_coalesced(self):
        self.rows([self.row, self.row])
        report = self.run_export(True)
        self.assertEqual(report["verified_files"], 1)
        self.assertEqual(report["ledger_rows"], 2)
        self.assertEqual(report["duplicate_rows"], 1)

    def test_zero_entries_rejected(self):
        self.rows([])
        self.assertEqual(self.run_export(False)["errors"], {"empty_ledger": 1})

    def test_empty_controls_rejected(self):
        self.ledger.write_text('{"input_sha256":{}}', encoding="utf-8")
        self.assertEqual(self.run_export(False)["errors"], {"empty_ledger": 1})

    def test_formal_files_map_explicit_field(self):
        self.ledger.write_text(json.dumps({"accepted": True, "files": {"a.bin": sha(self.payload)}}, indent=2),
                               encoding="utf-8")
        report = self.run_export(True, "--ledger-field", "files", "--audit-only")
        self.assertEqual(report["ledger_format"], {"format": "json-path-hash-map", "field": "files"})

    def test_ambiguous_controls_fields_rejected(self):
        self.ledger.write_text(json.dumps({"files": {"a.bin": sha(self.payload)},
                                          "input_sha256": {"a.bin": sha(self.payload)}}), encoding="utf-8")
        self.assertIn("conflict", self.run_export(False)["errors"])

    def test_pin_mismatch_rejected(self):
        self.rows([self.row])
        report = self.run_export(False, "--ledger-sha256", "0" * 64)
        self.assertEqual(report["errors"], {"ledger_hash_mismatch": 1})
        self.assertEqual(report["ledger"]["sha256"], sha(self.ledger.read_bytes()))

    def test_oversized_indivisible_file_rejected(self):
        self.rows([self.row])
        self.assertEqual(self.run_export(False, "--max-package-bytes", "1")["errors"], {"oversized": 1})

    def test_audit_only_no_packages_and_no_size_limit(self):
        self.rows([self.row])
        report = self.run_export(True, "--audit-only", "--max-package-bytes", "1")
        self.assertFalse(report["publishable_bundle"])
        self.assertTrue((self.output / "FILES.jsonl.gz").exists())
        self.assertFalse((self.output / "PACKAGES.json").exists())
        self.assertEqual(list(self.output.glob("*.zip")), [])

    def test_duplicate_controls_json_keys_rejected(self):
        self.ledger.write_text('{"input_sha256":{"a.bin":"' + sha(self.payload)
                               + '","a.bin":"' + "0" * 64 + '"}}', encoding="utf-8")
        self.assertIn("conflict", self.run_export(False)["errors"])

    def test_corrupt_gzip_rejected(self):
        self.ledger = self.root / "ledger.jsonl.gz"
        self.ledger.write_bytes(b"not gzip")
        self.assertFalse(self.run_export(False)["complete"])

    def test_output_no_overwrite(self):
        self.rows([self.row])
        self.output.mkdir()
        preserved = self.output / "preserve.txt"
        preserved.write_text("unchanged", encoding="utf-8")
        result = subprocess.run([sys.executable, str(TOOLS / "export_frozen_assets.py"),
                                 "--ledger", str(self.ledger), "--asset-root", str(self.assets),
                                 "--output", str(self.output)], stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=15, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(preserved.read_text(encoding="utf-8"), "unchanged")
        self.assertFalse((self.output / "SUMMARY.json").exists())

    def test_changed_bytes_during_packaging_never_published(self):
        self.rows([self.row])
        original = exporter.make_packages

        def changed(index, staging, budget):
            (self.assets / "a.bin").write_bytes(b"x" * len(self.payload))
            return original(index, staging, budget)

        with patch.object(exporter, "make_packages", side_effect=changed):
            result = exporter.main(["--ledger", str(self.ledger), "--asset-root", str(self.assets),
                                    "--output", str(self.output)])
        self.assertEqual(result, 1)
        summary = json.loads((self.output / "SUMMARY.json").read_text(encoding="utf-8"))
        self.assertFalse(summary["complete"])
        self.assertIn("changed_during_export", summary["errors"])
        self.assertEqual(list(self.output.glob("*.zip")), [])

    def test_symlink_outside_root_rejected_if_supported(self):
        outside = self.root / "outside.bin"
        outside.write_bytes(self.payload)
        symlink = self.assets / "link.bin"
        try:
            symlink.symlink_to(outside)
        except OSError:
            self.skipTest("Creating symlinks is unavailable on this host")
        self.rows([dict(self.row, canonical="link.bin")])
        self.assertEqual(self.run_export(False)["errors"], {"unsafe_path": 1})


class InventoryControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="frozen-inventory-controls-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.database = self.root / "source.sqlite"
        self.delivery = self.root / "delivery.jsonl"
        self.report = self.root / "report.json"
        self.closure = self.root / "closure.jsonl.gz"
        self.digest = sha(b"original decompressed certificate")
        with closing(sqlite3.connect(self.database)) as db:
            db.execute("CREATE TABLE files(canonical TEXT PRIMARY KEY, sha256 TEXT, bytes INTEGER, roles TEXT, status TEXT)")
            db.executemany("INSERT INTO files VALUES (?,?,?,?,?)", [
                ("a.bin", self.digest, 10, "n23,n24", "local_copy"),
                ("b.bin", self.digest, 10, "n230", "server_import"),
                ("c.bin", sha(b"missing c"), 20, "n23", "server_import"),
                ("d.bin", sha(b"missing d"), 30, "n24,n25", "metadata"),
            ])
            db.commit()
        self.write_delivery([{"path": "compressed-original.bin", "sha256": self.digest,
                              "bytes": 10, "encoding": "gzip-parts-v1", "parts": [
                                  {"path": "compressed-original.gz.part0001", "sha256": sha(b"compressed bytes"), "bytes": 7}
                              ]}])

    def write_delivery(self, rows):
        self.delivery.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")

    def test_original_digest_matching_role_union_and_read_only_db(self):
        original_hash = sha(self.database.read_bytes())
        report = inventory.audit(self.database, self.delivery, ["n23", "n24", "n25"], self.report, self.closure)
        self.assertEqual(sha(self.database.read_bytes()), original_hash)
        self.assertFalse(report["mathematical_replay"])
        self.assertFalse(report["fresh_full_local_file_hash_audit"])
        self.assertEqual(report["union"]["inventory_files"], 4)
        self.assertEqual(report["union"]["files_with_identical_delivered_content"], 2)
        self.assertEqual(report["union"]["bytes_without_identical_delivered_content"], 50)
        self.assertEqual(report["roles"]["n23"]["inventory_files"], 2)
        self.assertEqual(report["roles"]["n24"]["inventory_files"], 2)
        self.assertEqual(report["roles"]["n25"]["inventory_files"], 1)
        # n230 is not n23; shared rows explain why per-order counts do not sum to union.
        self.assertEqual(report["roles"]["n23"]["files_with_identical_delivered_content"], 1)
        with gzip.open(self.closure, "rt", encoding="utf-8") as stream:
            rows = [json.loads(line) for line in stream]
        self.assertEqual(len(rows), 4)
        self.assertEqual(rows[0]["canonical"], "a.bin")
        self.assertNotIn("source", rows[0])

    def test_identical_delivery_digest_at_multiple_paths_does_not_multiply_join(self):
        self.write_delivery([{"path": "one.bin", "sha256": self.digest},
                             {"path": "two.bin", "sha256": self.digest}])
        report = inventory.audit(self.database, self.delivery, ["n23"], self.report)
        self.assertEqual(report["delivered_logical_files"], 2)
        self.assertEqual(report["union"]["inventory_files"], 4)
        self.assertEqual(report["union"]["files_with_identical_delivered_content"], 2)

    def test_empty_bad_hash_and_duplicate_delivery_rejected(self):
        for rows in ([], [{"path": "a.bin", "sha256": "bad"}],
                     [{"path": "a.bin", "sha256": self.digest}] * 2):
            with self.subTest(rows=rows):
                self.write_delivery(rows)
                with self.assertRaises(ValueError):
                    inventory.audit(self.database, self.delivery, ["n23"], self.report)


class RestoreControls(unittest.TestCase):
    setUp = ExportControls.setUp
    rows = ExportControls.rows
    run_export = ExportControls.run_export

    def make_bundle(self):
        (self.assets / "z.bin").write_bytes(self.payload)
        self.rows([self.row, dict(self.row, canonical="z.bin")])
        self.run_export(True)
        self.package_index = self.output / "PACKAGES.json"
        self.index = json.loads(self.package_index.read_text(encoding="utf-8"))
        self.destination = self.root / "restored 空 格"

    def save_index(self):
        self.package_index.write_text(json.dumps(self.index), encoding="utf-8")

    def rewrite_package(self, members):
        package = self.output / self.index["packages"][0]["file"]
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            with zipfile.ZipFile(package, "w") as archive:
                for name, data in members:
                    archive.writestr(name, data)
        self.index["packages"][0].update(sha256=sha(package.read_bytes()), bytes=package.stat().st_size,
                                         files=len(members), uncompressed_bytes=sum(len(data) for _, data in members))
        self.save_index()

    def test_export_restore_round_trip_and_identical_existing_assets(self):
        self.make_bundle()
        result = restorer.restore(self.package_index, self.output, self.destination)
        self.assertEqual(result, {"files": 2, "bytes": 2 * len(self.payload), "complete": True,
                                  "mathematical_verification": "not_performed"})
        for name in ("a.bin", "z.bin"):
            self.assertEqual((self.destination / "assets" / name).read_bytes(), self.payload)
        # Byte-identical prior restoration is checked and safely reused.
        self.assertEqual(restorer.restore(self.package_index, self.output, self.destination), result)

    def test_duplicate_zip_member_rejected(self):
        self.make_bundle()
        self.rewrite_package([("assets/a.bin", self.payload), ("assets/a.bin", self.payload)])
        with self.assertRaisesRegex(ValueError, "Duplicate archive member"):
            restorer.restore(self.package_index, self.output, self.destination)

    def test_unbound_and_traversal_zip_members_rejected(self):
        self.make_bundle()
        for name in ("assets/unlisted.bin", "outside-assets.bin", "assets/../../escaped.bin"):
            with self.subTest(name=name):
                self.rewrite_package([("assets/a.bin", self.payload), (name, self.payload)])
                with self.assertRaises((ValueError, exporter.Rejected)):
                    restorer.restore(self.package_index, self.output, self.destination)
                self.assertFalse((self.root / "escaped.bin").exists())

    def test_tampered_package_hash_rejected_before_any_restore(self):
        self.make_bundle()
        package = self.output / self.index["packages"][0]["file"]
        data = package.read_bytes()
        package.write_bytes(b"x" + data[1:])
        with self.assertRaisesRegex(ValueError, "Package SHA256 mismatch"):
            restorer.restore(self.package_index, self.output, self.destination)
        self.assertFalse(self.destination.exists())

    def test_differing_existing_asset_not_overwritten(self):
        self.make_bundle()
        file = self.destination / "assets" / "a.bin"
        file.parent.mkdir(parents=True)
        preserved = b"existing bytes must remain"
        file.write_bytes(preserved)
        with self.assertRaisesRegex(ValueError, "Refusing differing existing asset"):
            restorer.restore(self.package_index, self.output, self.destination)
        self.assertEqual(file.read_bytes(), preserved)

    def test_missing_package_and_empty_ledger_rejected(self):
        self.make_bundle()
        package = self.output / self.index["packages"][0]["file"]
        original = package.read_bytes()
        package.unlink()
        with self.assertRaisesRegex(ValueError, "Missing package file"):
            restorer.restore(self.package_index, self.output, self.destination)
        self.assertFalse(self.destination.exists())
        package.write_bytes(original)
        manifest = self.output / self.index["files_manifest"]["file"]
        manifest.write_bytes(gzip.compress(b"", mtime=0))
        self.index["files_manifest"].update(sha256=sha(manifest.read_bytes()), bytes=manifest.stat().st_size)
        self.save_index()
        with self.assertRaisesRegex(ValueError, "Empty file ledger"):
            restorer.restore(self.package_index, self.output, self.destination)
        self.assertFalse(self.destination.exists())


if __name__ == "__main__":
    unittest.main(verbosity=2)
