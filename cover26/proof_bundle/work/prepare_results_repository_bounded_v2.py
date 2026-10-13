"""Resume existing staged bytes with a bounded source selection, not full inventory."""
import gzip
import json
import os
from pathlib import Path
import subprocess
import time

import prepare_results_repository_v1 as base

start = time.monotonic()
repo = base.REPO
maps = []
for n, project in ((11, "team-current"), (12, "n12-global"), (14, "next-cover-global")):
    maps.append((
        base.LOCAL / "research-2026" / project,
        Path(f"cover{n}/proof_bundle/research-2026") / project,
        f"local-n{n}-source", 3,
    ))
maps.append((
    base.SYNTHESIS, Path("shared/proof_bundle/research-2026/n21-25-synthesis"),
    "local-n21-to-n25-shared-source", 2,
))
for n in range(21, 26):
    maps.append((
        base.RECOVERED / f"research-2026/n{n}-global",
        Path(f"cover{n}/proof_bundle/research-2026/n{n}-global"),
        f"local-n{n}-notes", 2,
    ))
maps.extend([
    (base.N26 / "work", Path("cover26/proof_bundle/work"), "n26-original-code-and-notes", 0),
    (base.N26 / "outputs", Path("cover26/proof_bundle/outputs"), "n26-selected-reports", 0),
])


def selected_files(source_root, json_depth):
    command = ["rg", "--files", "--hidden"]
    for suffix in sorted(base.SOURCE_SUFFIXES | {".json", ".txt"}):
        command.extend(["-g", "*" + suffix])
    command.extend(["-g", "!**/" + "*/" * (json_depth + 1) + "*.json"])
    for name in sorted(base.SKIP_DIRS):
        command.extend(["-g", f"!**/{name}/**"])
    process = subprocess.Popen(
        command, cwd=source_root, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        encoding="utf-8", errors="strict",
    )
    for line in process.stdout:
        relative = Path(line.rstrip("\r\n"))
        path = source_root / relative
        if path.suffix.lower() == ".json" and (
            len(relative.parts) > json_depth + 1 or path.stat().st_size > 2 * 1024 * 1024
        ):
            continue
        if path.suffix.lower() == ".txt" and (
            len(relative.parts) > 2 or path.stat().st_size > 128 * 1024
        ):
            continue
        yield path, relative
    errors = process.stderr.read()
    if process.wait() not in (0, 1):
        raise RuntimeError("Source selection failed: " + errors)


def main():
    manifest_root = repo / "manifests"
    if (manifest_root / "FILES.jsonl").exists():
        raise RuntimeError("Final delivery already prepared; refusing duplicate work.")
    finals = {
        23: ("n23-global-final1", "6da6c5e1c80ade821bb033ce3b3b547c9ff5fb4a71cac16a531442a867e5da12"),
        24: ("n24-global-final1", "5bb55c9858a4dc1245249b12fd45cab3c5ed132a238eb6f7e70ddd6f2d0bb777"),
        25: ("n25-global-final5", "30389bfa3132d08954281e743db670fbb3874785e0d90c9876d4f5ddeec31dd1"),
    }
    for n, (name, digest) in finals.items():
        base.require_digest(base.SYNTHESIS / "round4-solo-20261004" / name / "ACCEPTED/GLOBAL-SOURCE-ACCEPTED.json", digest)
    base.require_digest(base.N26 / "outputs/n26-mixed-after-six-midarc-supplemental-current-v1.json",
                        "ba52dbb56f9d273c30e1b356c55bdb0d3ff8fdaa36061248e5c8ec1e490a81a1")
    base.require_digest(base.N26 / "outputs/n26-root25-current346-refit2-origin-append-composition-v1.json",
                        "c1675552b56d762de0bca83ca3adbb28e06c71e95c94b387d7f216eee41187c9")
    for source_root, target_root, category, depth in maps:
        if not source_root.is_dir():
            continue
        print("Selecting source files: " + category, flush=True)
        for source, relative in selected_files(source_root, depth):
            base.deliver(source, target_root / relative, category)
    critical = [
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
    for name in critical:
        base.deliver(base.N26 / "outputs" / name, Path("cover26/proof_bundle/outputs") / name,
                     "n26-authoritative-pair-and-independent-mathematics")
    for n, (name, digest) in finals.items():
        final_root = base.SYNTHESIS / "round4-solo-20261004" / name
        for source in sorted(final_root.rglob("*")):
            if source.is_file():
                base.deliver(source, Path(f"cover{n}/verification/final-acceptance") / source.relative_to(final_root),
                             f"n{n}-original-final-acceptance-and-frozen-ledger")
    for source in sorted((base.HE / "outputs").iterdir()):
        if source.is_file() and (source.suffix == ".md" or ("completion" in source.name and source.suffix == ".json")):
            base.deliver(source, Path("shared/verification/history") / source.name,
                         "n21-to-n25-followup-audit-history")
    # Preserve and freshly bind every file already copied by the interrupted collector.
    for path in sorted(repo.rglob("*")):
        if not path.is_file():
            continue
        relative = path.relative_to(repo)
        if {"manifests", ".git", "publication-local", "__pycache__"}.intersection(relative.parts) or ".gz.part" in path.name:
            continue
        if relative.as_posix() in base.logical_paths:
            continue
        for source_root, target_root, category, depth in maps:
            try:
                original_relative = relative.relative_to(target_root)
            except ValueError:
                continue
            source = source_root / original_relative
            base.deliver(source, relative, category + "-retained-v1-selection")
            break
        else:
            if base.contains_secret(path):
                raise RuntimeError("Credential-shaped content in delivery documentation.")
            base.entries.append({
                "path": relative.as_posix(), "bytes": path.stat().st_size,
                "sha256": base.sha(path), "encoding": "identity",
                "category": "delivery-documentation-and-verification-tooling",
            })
    base.entries.sort(key=lambda entry: entry["path"])
    with (manifest_root / "FILES.jsonl").open("x", encoding="utf-8", newline="\n") as output:
        for entry in base.entries:
            output.write(json.dumps(entry, ensure_ascii=True) + "\n")
    summary = {
        "schema": "disk-covering-bounded-source-results-delivery-v2",
        "snapshot_date": "2026-10-13", "timezone": "Asia/Shanghai",
        "covers": [11, 12, 14, 21, 22, 23, 24, 25, 26],
        "duplicate_numbered_local_proofs_preserved": [11, 12, 14],
        "delivered_files": len(base.entries),
        "delivered_original_bytes": sum(entry["bytes"] for entry in base.entries),
        "complete_historical_dependency_mirror": False,
        "complete_not_delivered_file_inventory": False,
        "this_delivery_is_new_mathematical_acceptance": False,
        "n26_global_optimality_proved": False,
        "n26_candidate_angle_roots_pending": 16,
        "n26_same_root_conditional_frontier_pending": 4957,
        "n26_root25_arithmetic_open_domains": 344,
        "raw_original_sources_unchanged": True,
        "credentials_persisted": False,
        "previous_collector": "v1 stopped after >2.8 million inventory items; original files and staged bytes preserved; incomplete journal ignored",
        "seconds": round(time.monotonic() - start, 1),
    }
    (manifest_root / "SUMMARY.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    (manifest_root / "NOT-DELIVERED-SCOPE.json").write_text(json.dumps({
        "complete_individual_inventory": False,
        "scope_roots": [str(item[0]) for item in maps],
        "not_delivered": "Historical per-leaf data, deep checkpoint JSON, most binary executors/caches and nonselected large intermediate reports",
        "authoritative_delivered_list": "FILES.jsonl",
        "unselected_files_must_not_be_assumed_present": True,
    }, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, ensure_ascii=False, indent=2), flush=True)


if __name__ == "__main__":
    main()
