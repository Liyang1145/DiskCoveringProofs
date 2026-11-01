#!/usr/bin/env python3
"""Classify public/archive payload sources for every residual n=11 id.

This is a source-completeness audit only.  It does not compile Lean, validate
the arithmetic packets, pay a residual id, or recover the unavailable HOST-side
354/35 failure taxonomy.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
CENSUS = HERE / "residual389-census.json"
PROPOSAL = ROOT / "n11-work/evidence-20261028/inputs/paid16-general-next512.json"
DBM = ROOT / "n11-work/lean/N11Formalization/DBMSourceTreeData.lean"
BRANCH = "origin/ci/n11-build"
ARCHIVE = "ci-n11/drafts/energy/N11Formalization"
OUT = HERE / "residual-payload-source-coverage.json"
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True)


def main() -> None:
    ids = json.loads(CENSUS.read_text())["residual_ids"]
    proposal = {r["id"]: r for r in json.loads(
        PROPOSAL.read_text(encoding="utf-8-sig"))["records"]}
    dbm_text = DBM.read_text()
    paths = {}
    listing = git("ls-tree", "-r", "--name-only", BRANCH, ARCHIVE)
    for rel in listing.splitlines():
        match = re.search(r"EnergyRefineN(\d+)\.lean$", rel)
        if match:
            paths[int(match.group(1))] = rel

    rows = []
    for node in ids:
        rec = proposal.get(node)
        proposal_ok = bool(
            rec and len(rec.get("g", [])) == 9 and
            all(key in rec for key in ("f0Lo", "lower", "gap", "packets")))
        db_match = re.search(
            rf"def node{node} : Node 5011 where\s*db := (.*?)\n\s*terminal :=",
            dbm_text, re.S)
        db_numbers = ([int(x) for x in re.findall(r"-?\d+", db_match.group(1))]
                      if db_match else [])
        dbm_ok = len(db_numbers) == 100
        archive_ok = False
        archive_forbidden = False
        archive_path = paths.get(node)
        if archive_path:
            source = git("show", f"{BRANCH}:{archive_path}")
            archive_ok = all(marker in source for marker in (
                "theorem terminal", "theorem new_radius", "def newIDs",
                "theorem pk_ok", f"{{{node}}}"))
            archive_forbidden = bool(FORBIDDEN.search(source))
        rows.append({
            "id": node,
            "proposal_complete": proposal_ok,
            "dbm_complete": dbm_ok,
            "archive_path": archive_path,
            "archive_static_shape_complete": archive_ok,
            "archive_has_forbidden_tokens": archive_forbidden,
        })

    proposal_ids = sorted(r["id"] for r in rows if r["proposal_complete"])
    archive_ids = sorted(r["id"] for r in rows
                         if r["archive_static_shape_complete"])
    complete_ids = sorted(set(proposal_ids) | set(archive_ids))
    report = {
        "scope": ("static source coverage for the 389-id residual census; "
                  "not arithmetic validation, Lean credit, or payment"),
        "source_sha256": {
            "residual389-census.json": sha256(CENSUS),
            "paid16-general-next512.json": sha256(PROPOSAL),
            "DBMSourceTreeData.lean": sha256(DBM),
        },
        "archive_branch": BRANCH,
        "historical_354_35_taxonomy_available_in_tree": False,
        "counts": {
            "residual": len(ids),
            "proposal_complete": len(proposal_ids),
            "dbm_complete": sum(r["dbm_complete"] for r in rows),
            "archive_static_shape_complete": len(archive_ids),
            "archive_clean_static_shape": sum(
                r["archive_static_shape_complete"] and
                not r["archive_has_forbidden_tokens"] for r in rows),
            "any_complete_source": len(complete_ids),
            "no_complete_source": len(ids) - len(complete_ids),
        },
        "proposal_ids": proposal_ids,
        "archive_ids": archive_ids,
        "archive_taxonomy_overlap": sorted(set(proposal_ids) & set(archive_ids)),
        "rows": rows,
    }
    OUT.write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps(report["counts"], indent=2))
    print("report_sha256", sha256(OUT))


if __name__ == "__main__":
    main()
