#!/usr/bin/env python3
"""Audit archived EnergyRefineN modules against the current 389-ID census.

The modules are read from git without checking out or modifying the archive
branch.  This is a static source audit, not a Lean build or kernel verdict.
"""
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
CENSUS = HERE / "residual389-census.json"
BRANCH = "origin/ci/n11-build"
PREFIX = "ci-n11/drafts/energy/N11Formalization/"
FRAMEWORK = "N11Formalization.Paid16MatrixCellCertificate"
CURRENT_MODULES = HERE.parents[2] / "lean/N11Formalization"
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b"
)


def git(*args, text=True):
    return subprocess.check_output(["git", *args], text=text)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


census = json.loads(CENSUS.read_text(encoding="utf-8"))
residual_ids = set(census["residual_ids"])
listing = git("ls-tree", "-r", "-l", BRANCH, PREFIX)
entries = []
for line in listing.splitlines():
    meta, path = line.split("\t", 1)
    _, kind, obj, size = meta.split()
    match = re.fullmatch(rf"{re.escape(PREFIX)}EnergyRefineN(\d+)\.lean", path)
    if kind != "blob" or not match:
        continue
    node = int(match.group(1))
    source = git("show", f"{BRANCH}:{path}")
    imports = re.findall(r"^import\s+(\S+)", source, re.MULTILINE)
    terminal_ids = {int(x) for x in re.findall(
        r"\(DBMSourceTree\.data\s+(\d+)\)\.terminal\s*=\s*true", source)}
    radius_ids = {int(x) for x in re.findall(
        r"DBMSourceTree\.data\s+(\d+)\).*?\n\s*\(FlashLeafSplit\.tlift y\)",
        source, re.DOTALL)}
    new_id_sets = re.findall(
        r"def newIDs : Finset \(Fin 5011\) := \{(\d+)\}", source)
    axiom_prints = [int(x) for x in re.findall(
        r"#print axioms N11Formalization\.EnergyRefineN(\d+)\.new_radius", source)]
    forbidden_hits = sorted(set(FORBIDDEN.findall(source)))
    checks = {
        "filename_id_matches_terminal": terminal_ids == {node},
        "radius_id_matches_filename": radius_ids == {node},
        "newIDs_singleton_matches_filename": new_id_sets == [str(node)],
        "axiom_print_matches_filename": axiom_prints == [node],
        "framework_imported": FRAMEWORK in imports,
        "id_is_current_residual": node in residual_ids,
    }
    entries.append({
        "id": node,
        "path": path,
        "bytes": int(size),
        "imports": imports,
        "kernel_decide_count": source.count("decide +kernel"),
        "draft_marker": "Exact-Fraction pre-validated; NOT compiled, NOT paid." in source,
        "forbidden_hits": forbidden_hits,
        "checks": checks,
        "static_shape_ok": all(checks.values()),
    })

framework_path = HERE.parents[2] / "lean/N11Formalization/Paid16MatrixCellCertificate.lean"
candidate_ids = sorted(entry["id"] for entry in entries)
blocking_reasons = []
if any(entry["draft_marker"] for entry in entries):
    blocking_reasons.append(
        "archive modules are marked as exact-rational pre-validated but not compiled")
if any("maxHeartbeats 0" in entry["forbidden_hits"] for entry in entries):
    blocking_reasons.append("some archive modules set maxHeartbeats 0")
if not framework_path.is_file():
    blocking_reasons.append(
        "required Paid16MatrixCellCertificate framework is absent from current tree")
if any(entry["kernel_decide_count"] for entry in entries):
    blocking_reasons.append(
        "large decide +kernel checks have not been bounded or kernel-audited here")
report = {
    "scope": "static archive-source audit only; no Lean build, source restoration or kernel credit",
    "source_branch": BRANCH,
    "source_commit": git("rev-parse", BRANCH).strip(),
    "census_path": str(CENSUS.relative_to(HERE.parents[3])),
    "census_sha256": sha256(CENSUS),
    "census_residual_count": len(residual_ids),
    "candidate_count": len(entries),
    "candidate_ids": candidate_ids,
    "candidate_ids_sha256": hashlib.sha256(
        ",".join(map(str, candidate_ids)).encode()).hexdigest(),
    "all_static_shapes_ok": all(entry["static_shape_ok"] for entry in entries),
    "all_candidates_residual": set(candidate_ids) <= residual_ids,
    "framework_present_in_current_tree": framework_path.is_file(),
    "framework_required_by_all": all(
        FRAMEWORK in entry["imports"] for entry in entries),
    "modules_with_forbidden_tokens": [
        entry["id"] for entry in entries if entry["forbidden_hits"]],
    "draft_marker_count": sum(entry["draft_marker"] for entry in entries),
    "maxheartbeats_zero_count": sum(
        "maxHeartbeats 0" in entry["forbidden_hits"] for entry in entries),
    "total_bytes": sum(entry["bytes"] for entry in entries),
    "total_kernel_decide_count": sum(
        entry["kernel_decide_count"] for entry in entries),
    "admissible_as_is": False,
    "blocking_reasons": blocking_reasons,
    "modules": entries,
}
(HERE / "archive-energy-refinement-audit.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps({key: value for key, value in report.items() if key != "modules"},
                 indent=2))
raise SystemExit(0 if report["all_static_shapes_ok"]
                 and report["all_candidates_residual"] else 1)
