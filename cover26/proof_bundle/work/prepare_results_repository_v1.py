"""Create a bounded, byte-preserving research delivery; not proof acceptance."""
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import time

REPO = Path(r"C:\Users\Administrator\Documents\Codex\2026-10-13\DiskCoveringProofs")
LOCAL = Path(r"C:\热爱单机但萌新\ai4math2")
RECOVERED = Path(r"F:\ai4math2-proof-output-20261007-v1\recovered-20261004-migrated\workspace")
SYNTHESIS = RECOVERED / "research-2026/n21-25-synthesis"
N26 = Path(r"C:\Users\Administrator\Documents\Codex\2026-10-09\n-26")
HE = Path(r"C:\Users\Administrator\Documents\Codex\2026-10-04\he")
SKIP_DIRS = {".git", ".lake", "node_modules", "__pycache__", ".venv", "venv", "external-theory-08958497"}
SOURCE_SUFFIXES = {".md", ".py", ".cpp", ".c", ".h", ".hpp", ".inc", ".lean", ".mjs", ".js", ".ps1", ".sh"}
SECRET = re.compile(rb"(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{40,}|sk-proj-[A-Za-z0-9_-]{50,})")
MAX_PLAIN = 4 * 1024 * 1024
MAX_PART = 40 * 1024 * 1024
entries = []
skipped_secret_paths = []
scanned_files = 0
omitted_files = 0
omitted_bytes = 0
start = time.monotonic()
logical_paths = set()


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def contains_secret(path):
    carry = b""
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            joined = carry + block
            if SECRET.search(joined):
                return True
            carry = joined[-512:]
    return False


class SplitWriter:
    def __init__(self, target):
        self.target = target
        self.parts = []
        self.stream = None
        self.current_size = 0
        self.current_hash = None

    def _next(self):
        self._finish()
        part = self.target.with_name(self.target.name + f".gz.part{len(self.parts) + 1:04d}")
        part.parent.mkdir(parents=True, exist_ok=True)
        self.stream = part.open("xb")
        self.current_size = 0
        self.current_hash = hashlib.sha256()
        self.current_path = part

    def _finish(self):
        if self.stream is not None:
            self.stream.close()
            self.parts.append({
                "path": self.current_path.relative_to(REPO).as_posix(),
                "bytes": self.current_size,
                "sha256": self.current_hash.hexdigest(),
            })
            self.stream = None

    def write(self, data):
        view = memoryview(data)
        while view:
            if self.stream is None or self.current_size == MAX_PART:
                self._next()
            block = view[: MAX_PART - self.current_size]
            self.stream.write(block)
            self.current_hash.update(block)
            self.current_size += len(block)
            view = view[len(block):]
        return len(data)

    def flush(self):
        if self.stream:
            self.stream.flush()

    def close(self):
        self._finish()


def deliver(source, relative, category):
    source = Path(source)
    relative = Path(relative).as_posix()
    if relative in logical_paths:
        return
    if not source.is_file():
        raise RuntimeError(f"Required source missing: {source}")
    if contains_secret(source):
        skipped_secret_paths.append(str(source))
        raise RuntimeError(f"Credential-shaped content detected; source NOT copied: {source.name}")
    stat_before = source.stat()
    digest = sha(source)
    target = REPO / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    entry = {
        "path": relative, "source": str(source), "category": category,
        "bytes": stat_before.st_size, "sha256": digest,
    }
    if stat_before.st_size > MAX_PLAIN:
        writer = SplitWriter(target)
        with source.open("rb") as input_stream, gzip.GzipFile(
            filename="", mode="wb", compresslevel=3, fileobj=writer, mtime=0,
        ) as output_stream:
            shutil.copyfileobj(input_stream, output_stream, 1024 * 1024)
        writer.close()
        entry.update({"encoding": "gzip-parts-v1", "parts": writer.parts})
    else:
        if target.exists():
            if sha(target) != digest:
                raise RuntimeError(f"Refusing to overwrite differing staged file: {relative}")
        else:
            shutil.copyfile(source, target)
        if sha(target) != digest:
            raise RuntimeError(f"Copied bytes differ: {relative}")
        entry["encoding"] = "identity"
    stat_after = source.stat()
    if (stat_before.st_size, stat_before.st_mtime_ns) != (stat_after.st_size, stat_after.st_mtime_ns):
        raise RuntimeError(f"Source changed during publication snapshot: {source}")
    entries.append(entry)
    logical_paths.add(relative)
    if len(entries) % 250 == 0 or stat_before.st_size > MAX_PLAIN:
        print(f"Staged {len(entries)} files; selected {relative} ({stat_before.st_size} original bytes)", flush=True)


def scan_tree(source_root, target_root, category, omitted_stream, json_depth=2, forced_names=()):
    global scanned_files, omitted_files, omitted_bytes
    if not source_root.is_dir():
        raise RuntimeError(f"Source root missing: {source_root}")
    for current, dirs, files in os.walk(source_root):
        dirs[:] = sorted(name for name in dirs if name not in SKIP_DIRS)
        for name in sorted(files):
            path = Path(current) / name
            relative = path.relative_to(source_root)
            stat = path.stat()
            scanned_files += 1
            selected = path.suffix.lower() in SOURCE_SUFFIXES
            selected |= path.suffix.lower() == ".json" and len(relative.parts) <= json_depth + 1 and stat.st_size <= 2 * 1024 * 1024
            selected |= path.suffix.lower() == ".txt" and stat.st_size <= 128 * 1024 and len(relative.parts) <= 2
            selected |= len(relative.parts) == 1 and path.name in forced_names
            if selected:
                deliver(path, target_root / relative, category)
            else:
                omitted_stream.write(json.dumps({
                    "source": str(path), "bytes": stat.st_size,
                    "reason": "Outside selected source/document/certificate snapshot; not delivered",
                }, ensure_ascii=True) + "\n")
                omitted_files += 1
                omitted_bytes += stat.st_size
        if scanned_files and scanned_files % 100000 < 100:
            print(f"Source inventory inspected {scanned_files} files; not delivered {omitted_files}", flush=True)


def require_digest(path, expected):
    if sha(path) != expected:
        raise RuntimeError(f"Authoritative digest mismatch: {path.name}")


def main():
    manifest_root = REPO / "manifests"
    manifest_root.mkdir(parents=True, exist_ok=True)
    if (manifest_root / "FILES.jsonl").exists():
        raise RuntimeError("Prepared manifest already exists; do not duplicate preparation.")
    acceptance_hashes = {
        23: "6da6c5e1c80ade821bb033ce3b3b547c9ff5fb4a71cac16a531442a867e5da12",
        24: "5bb55c9858a4dc1245249b12fd45cab3c5ed132a238eb6f7e70ddd6f2d0bb777",
        25: "30389bfa3132d08954281e743db670fbb3874785e0d90c9876d4f5ddeec31dd1",
    }
    final_dirs = {23: "n23-global-final1", 24: "n24-global-final1", 25: "n25-global-final5"}
    for n, name in final_dirs.items():
        require_digest(SYNTHESIS / "round4-solo-20261004" / name / "ACCEPTED/GLOBAL-SOURCE-ACCEPTED.json", acceptance_hashes[n])
    require_digest(N26 / "outputs/n26-mixed-after-six-midarc-supplemental-current-v1.json",
                   "ba52dbb56f9d273c30e1b356c55bdb0d3ff8fdaa36061248e5c8ec1e490a81a1")
    require_digest(N26 / "outputs/n26-root25-current346-refit2-origin-append-composition-v1.json",
                   "c1675552b56d762de0bca83ca3adbb28e06c71e95c94b387d7f216eee41187c9")
    journal_root = REPO / "publication-local"
    journal_root.mkdir(exist_ok=True)
    sweep_journal = journal_root / "SOURCE-SWEEP-UNSELECTED.jsonl.gz"
    with gzip.open(sweep_journal, "wt", encoding="utf-8", compresslevel=3) as omitted:
        for n, project in ((11, "team-current"), (12, "n12-global"), (14, "next-cover-global")):
            scan_tree(
                LOCAL / "research-2026" / project,
                Path(f"cover{n}/proof_bundle/research-2026") / project,
                f"local-n{n}-source", omitted, json_depth=3,
            )
        scan_tree(SYNTHESIS, Path("shared/proof_bundle/research-2026/n21-25-synthesis"),
                  "local-n21-to-n25-shared-source", omitted, json_depth=2)
        for n in range(21, 26):
            project = RECOVERED / f"research-2026/n{n}-global"
            if project.is_dir():
                scan_tree(project, Path(f"cover{n}/proof_bundle/research-2026/n{n}-global"),
                          f"local-n{n}-project-notes", omitted, json_depth=2)
        scan_tree(N26 / "work", Path("cover26/proof_bundle/work"),
                  "n26-original-executor-and-mathematical-notes", omitted, json_depth=0)
        # This workspace contains publication helpers; these are not mathematical evidence.
        critical_n26 = [
            "n26-mixed-after-six-midarc-supplemental-current-v1.json",
            "n26-mixed-after-six-midarc-independent-final-v1.json",
            "n26-mixed-after-six-midarc-supplemental-current-v1-geometry-semantic-replay.json",
            "n26-mixed-after-six-midarc-source-geometry-published-replay-v1.json",
            "n26-current28-six-target-mixed-candidate-current-v1.json",
            "n26-current28-six-target-mixed-candidate-independent-final-v1.json",
            "n26-root25-current346-refit2-origin-append-composition-v1.json",
            "n26-root25-current346-refit2-origin-append-independent-controls-v1.json",
            "n26-current346-refit2-origin-admission-diagnostic-v1.json",
            "n26-current346-refit2-origin-admission-independent-controls-v1.json",
        ]
        scan_tree(N26 / "outputs", Path("cover26/proof_bundle/outputs"),
                  "n26-selected-reports-and-authoritative-current-pairs", omitted,
                  json_depth=0, forced_names=critical_n26)
        for n, name in final_dirs.items():
            final_root = SYNTHESIS / "round4-solo-20261004" / name
            for current, dirs, files in os.walk(final_root):
                dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
                for name_part in sorted(files):
                    path = Path(current) / name_part
                    deliver(path, Path(f"cover{n}/verification/final-acceptance") / path.relative_to(final_root),
                            f"n{n}-original-final-acceptance-and-bindings")
        for path in sorted((HE / "outputs").glob("*")):
            if path.is_file() and (path.suffix == ".md" or ("completion" in path.name and path.suffix == ".json")):
                deliver(path, Path("shared/verification/history") / path.name, "n21-to-n25-followup-audit-history")
    # Record authored delivery tooling and docs in the same byte manifest.
    for path in sorted(REPO.rglob("*")):
        if path.is_file() and not {"manifests", ".git", "publication-local"}.intersection(path.relative_to(REPO).parts):
            relative = path.relative_to(REPO).as_posix()
            if relative in logical_paths or ".gz.part" in path.name:
                continue
            if contains_secret(path):
                raise RuntimeError(f"Sensitive content in authored delivery file: {relative}")
            entries.append({
                "path": relative, "category": "delivery-documentation-and-byte-verification-tooling",
                "bytes": path.stat().st_size, "sha256": sha(path), "encoding": "identity",
            })
    entries.sort(key=lambda entry: entry["path"])
    with (manifest_root / "FILES.jsonl").open("x", encoding="utf-8", newline="\n") as output:
        for entry in entries:
            output.write(json.dumps(entry, ensure_ascii=True) + "\n")
    delivered_sources = {entry.get("source") for entry in entries}
    final_omitted_files = 0
    final_omitted_bytes = 0
    with gzip.open(sweep_journal, "rt", encoding="utf-8") as swept, gzip.open(
        manifest_root / "NOT-DELIVERED.jsonl.gz", "wt", encoding="utf-8", compresslevel=3,
    ) as output:
        for line in swept:
            entry = json.loads(line)
            if entry["source"] in delivered_sources:
                continue
            output.write(line)
            final_omitted_files += 1
            final_omitted_bytes += entry["bytes"]
    summary = {
        "schema": "disk-covering-source-results-delivery-v1",
        "snapshot_date": "2026-10-13",
        "timezone": "Asia/Shanghai",
        "covers": [11, 12, 14, 21, 22, 23, 24, 25, 26],
        "duplicate_numbered_local_proofs_preserved": [11, 12, 14],
        "delivered_files": len(entries),
        "delivered_original_bytes": sum(entry["bytes"] for entry in entries),
        "scanned_source_files": scanned_files,
        "not_delivered_inventory_files": final_omitted_files,
        "not_delivered_inventory_original_bytes": final_omitted_bytes,
        "complete_historical_dependency_mirror": False,
        "this_delivery_is_new_mathematical_acceptance": False,
        "n26_global_optimality_proved": False,
        "n26_candidate_angle_roots_pending": 16,
        "n26_same_root_conditional_frontier_pending": 4957,
        "n26_root25_arithmetic_open_domains": 344,
        "raw_original_sources_unchanged": True,
        "credentials_persisted": False,
        "secret_scan_blocked_files": skipped_secret_paths,
        "seconds": round(time.monotonic() - start, 1),
    }
    (manifest_root / "SUMMARY.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, ensure_ascii=False, indent=2), flush=True)


if __name__ == "__main__":
    main()
