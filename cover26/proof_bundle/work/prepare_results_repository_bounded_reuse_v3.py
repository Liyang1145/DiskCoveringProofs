"""Reuse existing gzip parts only after fresh full reconstruction matches source."""
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys

import prepare_results_repository_bounded_v2 as bounded

base = bounded.base
sys.path.insert(0, str(base.REPO / "tools"))
from bundle_io import PartsReader

original_deliver = base.deliver


def checked_reuse(source, relative, category):
    source = Path(source)
    relative = Path(relative).as_posix()
    if relative in base.logical_paths:
        return
    target = base.REPO / relative
    parts = sorted(target.parent.glob(target.name + ".gz.part????"))
    if not parts:
        return original_deliver(source, relative, category)
    if source.stat().st_size <= base.MAX_PLAIN:
        raise RuntimeError("Unexpected existing compressed encoding for a small source.")
    if base.contains_secret(source):
        raise RuntimeError("Credential-shaped content detected; not admitted.")
    expected_names = [target.name + f".gz.part{index:04d}" for index in range(1, len(parts) + 1)]
    if [part.name for part in parts] != expected_names:
        raise RuntimeError("Existing compression part indices are not contiguous.")
    source_stat = source.stat()
    expected_hash = base.sha(source)
    raw_hash = hashlib.sha256()
    raw_bytes = 0
    with io.BufferedReader(PartsReader(parts)) as joined, gzip.GzipFile(fileobj=joined) as raw:
        for block in iter(lambda: raw.read(1024 * 1024), b""):
            raw_hash.update(block)
            raw_bytes += len(block)
    if raw_bytes != source_stat.st_size or raw_hash.hexdigest() != expected_hash:
        raise RuntimeError("Preserved gzip bytes do not reconstruct the actual original source.")
    if (source.stat().st_size, source.stat().st_mtime_ns) != (source_stat.st_size, source_stat.st_mtime_ns):
        raise RuntimeError("Source changed during reconstruction check.")
    base.entries.append({
        "path": relative, "source": str(source), "category": category,
        "bytes": raw_bytes, "sha256": expected_hash, "encoding": "gzip-parts-v1",
        "parts": [{
            "path": part.relative_to(base.REPO).as_posix(),
            "bytes": part.stat().st_size, "sha256": base.sha(part),
        } for part in parts],
    })
    base.logical_paths.add(relative)
    print("Freshly reconstructed and retained existing gzip: " + relative, flush=True)


if __name__ == "__main__":
    if "--reuse-staged-selection-only" in sys.argv:
        # Use only after observing v2 reach its post-selection critical-file loop.
        # Every existing staged file is still freshly matched to its real source.
        bounded.selected_files = lambda *_args: iter(())
    base.deliver = checked_reuse
    bounded.main()
    summary_path = base.REPO / "manifests/SUMMARY.json"
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    summary["schema"] = "disk-covering-bounded-source-results-checked-part-reuse-v3"
    summary["existing_gzip_parts_freshly_reconstructed_before_reuse"] = True
    summary["selection_reused_after_actual_v2_post_selection_failure"] = "--reuse-staged-selection-only" in sys.argv
    summary_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
