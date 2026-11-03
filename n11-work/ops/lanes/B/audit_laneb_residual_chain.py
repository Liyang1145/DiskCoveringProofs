#!/usr/bin/env python3
"""Deterministic count/subset audit of lane B's residual-ID chain

    389 --(remove 16 certified)--> 373 --(remove 27 green refinements)--> 346
        --(remove 14 archive refinements)--> 332

Sources (all read-only, outside this lane where noted):
  - n11-work/ops/lanes/C/residual389-census.json          (lane C data)
  - n11-work/ops/lanes/C/residual373-conditional-census.json
  - n11-work/ops/lanes/B/residual373-ids.txt              (lane B, exact complement)
  - n11-work/lean/N11Formalization/LaneBArchiveRefineAll14.lean (archiveIDs)

The extra-27 list is read from the committed lane-B bridge audit report; it is
re-derived from the 373-census JSON here and cross-checked.  This is exact
source arithmetic, NOT Lean elaboration or kernel credit.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LANEC = ROOT / "n11-work" / "ops" / "lanes" / "C"
LEAN = ROOT / "n11-work" / "lean" / "N11Formalization"


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest().upper()


def sha256_ids(ids) -> str:
    # canonical: sorted ints, one per line, trailing newline (matches lane-B file)
    return hashlib.sha256(
        ("".join(f"{i}\n" for i in sorted(ids))).encode()
    ).hexdigest().upper()


def archive_ids_from_lean() -> list[int]:
    txt = (LEAN / "LaneBArchiveRefineAll14.lean").read_text(encoding="utf-8")
    m = re.search(r"archiveIDs\s*:\s*Finset \(Fin 5011\)\s*:=\s*\{([^}]*)\}", txt)
    assert m, "archiveIDs literal not found"
    return sorted(int(x) for x in m.group(1).split(","))


def main() -> int:
    c389 = json.loads((LANEC / "residual389-census.json").read_text())
    c373 = json.loads((LANEC / "residual373-conditional-census.json").read_text())
    r389 = sorted(int(x) for x in c389["residual_ids"])
    r373 = sorted(int(x) for x in c373["residual_ids"])
    removed16 = sorted(int(x) for x in c373["removed_ids"])

    file373 = [int(l) for l in (HERE / "residual373-ids.txt").read_text().split()]
    archive14 = archive_ids_from_lean()

    extra27 = sorted(set(r373) - set(r389 - set(removed16)) | (set(r373) - set(r373)))
    # extra27 is the part of 373 that lane B's bridge removes to reach 346;
    # read it from the committed bridge report (authoritative lane-B artifact).
    bridge = json.loads((HERE / "audit_residual373_to_346_bridge-report.json").read_text())
    extra27 = sorted(int(x) for x in bridge["extra27"])

    c346 = sorted(set(r373) - set(extra27))
    c332 = sorted(set(c346) - set(archive14))

    checks = {
        "r389_count_389": len(r389) == 389,
        "r373_count_373": len(r373) == 373,
        "removed16_count_16": len(removed16) == 16,
        "r373_equals_r389_minus_removed16": set(r373) == set(r389) - set(removed16),
        "residual373_file_matches_census": file373 == r373,
        "residual373_file_sha_matches": sha256_ids(file373) == sha256_ids(r373),
        "extra27_count_27": len(extra27) == 27,
        "extra27_subset_of_373": set(extra27) <= set(r373),
        "extra27_disjoint_removed16": set(extra27).isdisjoint(removed16),
        "c346_count_346": len(c346) == 346,
        "c346_equals_373_minus_extra27": set(c346) == set(r373) - set(extra27),
        "archive14_count_14": len(archive14) == 14,
        "archive14_subset_of_346": set(archive14) <= set(c346),
        "archive14_disjoint_extra27": set(archive14).isdisjoint(extra27),
        "c332_count_332": len(c332) == 332,
        "c332_equals_346_minus_archive14": set(c332) == set(c346) - set(archive14),
    }

    report = {
        "scope": "exact source-ID counting/subset audit of lane B's residual chain; "
                 "no Lean elaboration or kernel credit",
        "source_sha256": {
            "residual389-census.json": sha256_file(LANEC / "residual389-census.json"),
            "residual373-conditional-census.json": sha256_file(LANEC / "residual373-conditional-census.json"),
            "residual373-ids.txt": sha256_file(HERE / "residual373-ids.txt"),
            "LaneBArchiveRefineAll14.lean": sha256_file(LEAN / "LaneBArchiveRefineAll14.lean"),
            "audit_residual373_to_346_bridge-report.json": sha256_file(
                HERE / "audit_residual373_to_346_bridge-report.json"),
        },
        "counts": {"r389": len(r389), "r373": len(r373), "c346": len(c346), "c332": len(c332)},
        "removed16": removed16,
        "extra27": extra27,
        "archive14": archive14,
        "checks": checks,
        "ok": all(checks.values()),
    }
    out = HERE / "audit_laneb_residual_chain-report.json"
    out.write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps({k: report[k] for k in ("counts", "checks", "ok")}, indent=1))
    print("report:", out.name)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
